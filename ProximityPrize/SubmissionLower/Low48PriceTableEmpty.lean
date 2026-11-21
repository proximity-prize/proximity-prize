import ProximityPrize.SubmissionLower.Low48PriceTableBase

set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
namespace Low48PriceTableEmpty
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low48Price (fullCap physicalPrice)
open Low48PriceCaps (order allowance start allowance_mono)
open Low48PriceTableBase (point oldRectangle)

private theorem r1_0 {a : Shape} (h₁ : 1 ≤ a.b) (h₂ : 3 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 3) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 73) (h₄ : a.j ≤ 4) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2 {a : Shape} (h₁ : 74 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 4) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 2) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_3 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 41) (h₄ : a.j ≤ 5) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_4 {a : Shape} (h₁ : 42 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 83) (h₄ : a.j ≤ 5) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 2) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_5 {a : Shape} (h₁ : 84 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 5) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 3) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_6 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 29) (h₄ : a.j ≤ 6) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_7 {a : Shape} (h₁ : 30 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 86) (h₄ : a.j ≤ 6) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 3) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_8 {a : Shape} (h₁ : 87 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 6) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 10) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_9 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 7 ≤ a.j)
    (h₃ : a.b ≤ 22) (h₄ : a.j ≤ 7) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_10 {a : Shape} (h₁ : 23 ≤ a.b) (h₂ : 7 ≤ a.j)
    (h₃ : a.b ≤ 66) (h₄ : a.j ≤ 7) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 3) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_11 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 7 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 7) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 10) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_12 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 18) (h₄ : a.j ≤ 8) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_13 {a : Shape} (h₁ : 19 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 53) (h₄ : a.j ≤ 8) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 3) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_14 {a : Shape} (h₁ : 54 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 88) (h₄ : a.j ≤ 8) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 5) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_15 {a : Shape} (h₁ : 89 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 8) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 10) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_16 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 104) (h₄ : a.j ≤ 9) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 7) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_17 {a : Shape} (h₁ : 105 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 9) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 22) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_18 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 10 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 10) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 7) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_19 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 10 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 10) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 22) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_20 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 11 ≤ a.j)
    (h₃ : a.b ≤ 83) (h₄ : a.j ≤ 11) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 7) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_21 {a : Shape} (h₁ : 84 ≤ a.b) (h₂ : 11 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 11) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 22) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_22 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 12 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 12) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 21) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_23 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 13 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 15) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 21) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_24 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 18) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 25) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_25 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 21) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_26 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 24) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_27 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 27) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 32) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_28 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 30) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_29 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_30 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_31 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_32 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_33 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_34 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_35 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_36 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_37 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 48) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_38 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_39 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 49) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_40 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact1 (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 3
  · apply r1_0 <;> omega
  by_cases hJ1 : a.j ≤ 4
  · by_cases hB0 : a.b ≤ 73
    · apply r1_1 <;> omega
    apply r1_2 <;> omega
  by_cases hJ2 : a.j ≤ 5
  · by_cases hB0 : a.b ≤ 41
    · apply r1_3 <;> omega
    by_cases hB1 : a.b ≤ 83
    · apply r1_4 <;> omega
    apply r1_5 <;> omega
  by_cases hJ3 : a.j ≤ 6
  · by_cases hB0 : a.b ≤ 29
    · apply r1_6 <;> omega
    by_cases hB1 : a.b ≤ 86
    · apply r1_7 <;> omega
    apply r1_8 <;> omega
  by_cases hJ4 : a.j ≤ 7
  · by_cases hB0 : a.b ≤ 22
    · apply r1_9 <;> omega
    by_cases hB1 : a.b ≤ 66
    · apply r1_10 <;> omega
    apply r1_11 <;> omega
  by_cases hJ5 : a.j ≤ 8
  · by_cases hB0 : a.b ≤ 18
    · apply r1_12 <;> omega
    by_cases hB1 : a.b ≤ 53
    · apply r1_13 <;> omega
    by_cases hB2 : a.b ≤ 88
    · apply r1_14 <;> omega
    apply r1_15 <;> omega
  by_cases hJ6 : a.j ≤ 9
  · by_cases hB0 : a.b ≤ 104
    · apply r1_16 <;> omega
    apply r1_17 <;> omega
  by_cases hJ7 : a.j ≤ 10
  · by_cases hB0 : a.b ≤ 92
    · apply r1_18 <;> omega
    apply r1_19 <;> omega
  by_cases hJ8 : a.j ≤ 11
  · by_cases hB0 : a.b ≤ 83
    · apply r1_20 <;> omega
    apply r1_21 <;> omega
  by_cases hJ9 : a.j ≤ 12
  · apply r1_22 <;> omega
  by_cases hJ10 : a.j ≤ 15
  · apply r1_23 <;> omega
  by_cases hJ11 : a.j ≤ 18
  · apply r1_24 <;> omega
  by_cases hJ12 : a.j ≤ 21
  · apply r1_25 <;> omega
  by_cases hJ13 : a.j ≤ 24
  · apply r1_26 <;> omega
  by_cases hJ14 : a.j ≤ 27
  · apply r1_27 <;> omega
  by_cases hJ15 : a.j ≤ 30
  · apply r1_28 <;> omega
  by_cases hJ16 : a.j ≤ 33
  · apply r1_29 <;> omega
  by_cases hJ17 : a.j ≤ 36
  · apply r1_30 <;> omega
  by_cases hJ18 : a.j ≤ 39
  · apply r1_31 <;> omega
  by_cases hJ19 : a.j ≤ 42
  · apply r1_32 <;> omega
  by_cases hJ20 : a.j ≤ 44
  · apply r1_33 <;> omega
  by_cases hJ21 : a.j ≤ 45
  · apply r1_34 <;> omega
  by_cases hJ22 : a.j ≤ 46
  · apply r1_35 <;> omega
  by_cases hJ23 : a.j ≤ 47
  · apply r1_36 <;> omega
  by_cases hJ24 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 119
    · apply r1_37 <;> omega
    apply r1_38 <;> omega
  by_cases hB0 : a.b ≤ 117
  · apply r1_39 <;> omega
  apply r1_40 <;> omega

private theorem r2_0 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 28) (h₄ : a.j ≤ 6) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_1 {a : Shape} (h₁ : 29 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 86) (h₄ : a.j ≤ 6) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 3) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_2 {a : Shape} (h₁ : 87 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 6) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 10) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_3 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 7 ≤ a.j)
    (h₃ : a.b ≤ 21) (h₄ : a.j ≤ 7) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_4 {a : Shape} (h₁ : 22 ≤ a.b) (h₂ : 7 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 7) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 3) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_5 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 7 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 7) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 10) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_6 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 17) (h₄ : a.j ≤ 8) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_7 {a : Shape} (h₁ : 18 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 52) (h₄ : a.j ≤ 8) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 3) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_8 {a : Shape} (h₁ : 53 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 87) (h₄ : a.j ≤ 8) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 5) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_9 {a : Shape} (h₁ : 88 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 8) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 10) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_10 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 104) (h₄ : a.j ≤ 9) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 7) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_11 {a : Shape} (h₁ : 105 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 9) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 22) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_12 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 10 ≤ a.j)
    (h₃ : a.b ≤ 91) (h₄ : a.j ≤ 10) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 7) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_13 {a : Shape} (h₁ : 92 ≤ a.b) (h₂ : 10 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 10) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 22) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_14 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 11 ≤ a.j)
    (h₃ : a.b ≤ 82) (h₄ : a.j ≤ 11) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 7) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_15 {a : Shape} (h₁ : 83 ≤ a.b) (h₂ : 11 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 11) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 22) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_16 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 12 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 12) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 21) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_17 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 13 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 15) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 21) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_18 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 18) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 25) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_19 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 21) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_20 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 24) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_21 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 27) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 32) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_22 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 30) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_23 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_24 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_25 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_26 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_27 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_28 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_29 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_30 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_31 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 46) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_32 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_33 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 47) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_34 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_35 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 48) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_36 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_37 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 49) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_38 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact2 (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 6
  · by_cases hB0 : a.b ≤ 28
    · apply r2_0 <;> omega
    by_cases hB1 : a.b ≤ 86
    · apply r2_1 <;> omega
    apply r2_2 <;> omega
  by_cases hJ1 : a.j ≤ 7
  · by_cases hB0 : a.b ≤ 21
    · apply r2_3 <;> omega
    by_cases hB1 : a.b ≤ 65
    · apply r2_4 <;> omega
    apply r2_5 <;> omega
  by_cases hJ2 : a.j ≤ 8
  · by_cases hB0 : a.b ≤ 17
    · apply r2_6 <;> omega
    by_cases hB1 : a.b ≤ 52
    · apply r2_7 <;> omega
    by_cases hB2 : a.b ≤ 87
    · apply r2_8 <;> omega
    apply r2_9 <;> omega
  by_cases hJ3 : a.j ≤ 9
  · by_cases hB0 : a.b ≤ 104
    · apply r2_10 <;> omega
    apply r2_11 <;> omega
  by_cases hJ4 : a.j ≤ 10
  · by_cases hB0 : a.b ≤ 91
    · apply r2_12 <;> omega
    apply r2_13 <;> omega
  by_cases hJ5 : a.j ≤ 11
  · by_cases hB0 : a.b ≤ 82
    · apply r2_14 <;> omega
    apply r2_15 <;> omega
  by_cases hJ6 : a.j ≤ 12
  · apply r2_16 <;> omega
  by_cases hJ7 : a.j ≤ 15
  · apply r2_17 <;> omega
  by_cases hJ8 : a.j ≤ 18
  · apply r2_18 <;> omega
  by_cases hJ9 : a.j ≤ 21
  · apply r2_19 <;> omega
  by_cases hJ10 : a.j ≤ 24
  · apply r2_20 <;> omega
  by_cases hJ11 : a.j ≤ 27
  · apply r2_21 <;> omega
  by_cases hJ12 : a.j ≤ 30
  · apply r2_22 <;> omega
  by_cases hJ13 : a.j ≤ 33
  · apply r2_23 <;> omega
  by_cases hJ14 : a.j ≤ 36
  · apply r2_24 <;> omega
  by_cases hJ15 : a.j ≤ 39
  · apply r2_25 <;> omega
  by_cases hJ16 : a.j ≤ 42
  · apply r2_26 <;> omega
  by_cases hJ17 : a.j ≤ 43
  · apply r2_27 <;> omega
  by_cases hJ18 : a.j ≤ 44
  · apply r2_28 <;> omega
  by_cases hJ19 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 120
    · apply r2_29 <;> omega
    apply r2_30 <;> omega
  by_cases hJ20 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 118
    · apply r2_31 <;> omega
    apply r2_32 <;> omega
  by_cases hJ21 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 116
    · apply r2_33 <;> omega
    apply r2_34 <;> omega
  by_cases hJ22 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 114
    · apply r2_35 <;> omega
    apply r2_36 <;> omega
  by_cases hB0 : a.b ≤ 113
  · apply r2_37 <;> omega
  apply r2_38 <;> omega

private theorem r3_0 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 104) (h₄ : a.j ≤ 9) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 7) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_1 {a : Shape} (h₁ : 105 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 9) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 22) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_2 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 10 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 10) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 7) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_3 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 10 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 10) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 22) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_4 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 11 ≤ a.j)
    (h₃ : a.b ≤ 82) (h₄ : a.j ≤ 11) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 7) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_5 {a : Shape} (h₁ : 83 ≤ a.b) (h₂ : 11 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 11) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 22) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_6 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 12 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 12) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 21) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_7 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 13 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 15) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 21) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_8 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 18) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 25) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_9 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 21) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_10 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 24) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_11 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 27) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 32) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_12 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 30) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_13 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_14 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_15 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_16 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_17 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_18 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_19 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 44) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_20 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_21 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 45) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_22 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_23 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 46) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_24 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_25 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 112) (h₄ : a.j ≤ 47) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_26 {a : Shape} (h₁ : 113 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_27 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 48) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_28 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_29 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 109) (h₄ : a.j ≤ 49) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_30 {a : Shape} (h₁ : 110 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact3 (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 9
  · by_cases hB0 : a.b ≤ 104
    · apply r3_0 <;> omega
    apply r3_1 <;> omega
  by_cases hJ1 : a.j ≤ 10
  · by_cases hB0 : a.b ≤ 92
    · apply r3_2 <;> omega
    apply r3_3 <;> omega
  by_cases hJ2 : a.j ≤ 11
  · by_cases hB0 : a.b ≤ 82
    · apply r3_4 <;> omega
    apply r3_5 <;> omega
  by_cases hJ3 : a.j ≤ 12
  · apply r3_6 <;> omega
  by_cases hJ4 : a.j ≤ 15
  · apply r3_7 <;> omega
  by_cases hJ5 : a.j ≤ 18
  · apply r3_8 <;> omega
  by_cases hJ6 : a.j ≤ 21
  · apply r3_9 <;> omega
  by_cases hJ7 : a.j ≤ 24
  · apply r3_10 <;> omega
  by_cases hJ8 : a.j ≤ 27
  · apply r3_11 <;> omega
  by_cases hJ9 : a.j ≤ 30
  · apply r3_12 <;> omega
  by_cases hJ10 : a.j ≤ 33
  · apply r3_13 <;> omega
  by_cases hJ11 : a.j ≤ 36
  · apply r3_14 <;> omega
  by_cases hJ12 : a.j ≤ 39
  · apply r3_15 <;> omega
  by_cases hJ13 : a.j ≤ 41
  · apply r3_16 <;> omega
  by_cases hJ14 : a.j ≤ 42
  · apply r3_17 <;> omega
  by_cases hJ15 : a.j ≤ 43
  · apply r3_18 <;> omega
  by_cases hJ16 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 118
    · apply r3_19 <;> omega
    apply r3_20 <;> omega
  by_cases hJ17 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 116
    · apply r3_21 <;> omega
    apply r3_22 <;> omega
  by_cases hJ18 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 114
    · apply r3_23 <;> omega
    apply r3_24 <;> omega
  by_cases hJ19 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 112
    · apply r3_25 <;> omega
    apply r3_26 <;> omega
  by_cases hJ20 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 110
    · apply r3_27 <;> omega
    apply r3_28 <;> omega
  by_cases hB0 : a.b ≤ 109
  · apply r3_29 <;> omega
  apply r3_30 <;> omega

private theorem r4_0 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 12 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 12) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 21) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_1 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 13 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 15) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 21) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_2 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 18) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 25) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_3 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 21) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_4 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 24) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_5 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 27) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 32) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_6 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 30) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_7 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_8 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_9 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_10 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 40) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_11 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_12 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_13 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_14 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 43) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_15 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_16 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 44) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_17 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_18 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 45) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_19 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_20 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 111) (h₄ : a.j ≤ 46) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_21 {a : Shape} (h₁ : 112 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_22 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 109) (h₄ : a.j ≤ 47) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_23 {a : Shape} (h₁ : 110 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_24 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 48) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_25 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_26 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 49) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_27 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact4 (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 4 .empty a.j := by
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
  by_cases hJ10 : a.j ≤ 40
  · apply r4_10 <;> omega
  by_cases hJ11 : a.j ≤ 41
  · apply r4_11 <;> omega
  by_cases hJ12 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 120
    · apply r4_12 <;> omega
    apply r4_13 <;> omega
  by_cases hJ13 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 118
    · apply r4_14 <;> omega
    apply r4_15 <;> omega
  by_cases hJ14 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 115
    · apply r4_16 <;> omega
    apply r4_17 <;> omega
  by_cases hJ15 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 113
    · apply r4_18 <;> omega
    apply r4_19 <;> omega
  by_cases hJ16 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 111
    · apply r4_20 <;> omega
    apply r4_21 <;> omega
  by_cases hJ17 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 109
    · apply r4_22 <;> omega
    apply r4_23 <;> omega
  by_cases hJ18 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 107
    · apply r4_24 <;> omega
    apply r4_25 <;> omega
  by_cases hB0 : a.b ≤ 105
  · apply r4_26 <;> omega
  apply r4_27 <;> omega

private theorem r5_0 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 15 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 15) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 25) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_1 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 18) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 25) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_2 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 21) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_3 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 24) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_4 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 27) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 32) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_5 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 30) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_6 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_7 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_8 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 38) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_9 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_10 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 40) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_11 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_12 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_13 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 42) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_14 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_15 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 43) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_16 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_17 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 44) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_18 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_19 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 45) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_20 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_21 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 108) (h₄ : a.j ≤ 46) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_22 {a : Shape} (h₁ : 109 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_23 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 47) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_24 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_25 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 104) (h₄ : a.j ≤ 48) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_26 {a : Shape} (h₁ : 105 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_27 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 102) (h₄ : a.j ≤ 49) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_28 {a : Shape} (h₁ : 103 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 49) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_29 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j :=
  oldRectangle (l := 50) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact5 (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 5 .empty a.j := by
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
  by_cases hJ8 : a.j ≤ 38
  · apply r5_8 <;> omega
  by_cases hJ9 : a.j ≤ 39
  · apply r5_9 <;> omega
  by_cases hJ10 : a.j ≤ 40
  · apply r5_10 <;> omega
  by_cases hJ11 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 120
    · apply r5_11 <;> omega
    apply r5_12 <;> omega
  by_cases hJ12 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 118
    · apply r5_13 <;> omega
    apply r5_14 <;> omega
  by_cases hJ13 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 115
    · apply r5_15 <;> omega
    apply r5_16 <;> omega
  by_cases hJ14 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 113
    · apply r5_17 <;> omega
    apply r5_18 <;> omega
  by_cases hJ15 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 110
    · apply r5_19 <;> omega
    apply r5_20 <;> omega
  by_cases hJ16 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 108
    · apply r5_21 <;> omega
    apply r5_22 <;> omega
  by_cases hJ17 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 106
    · apply r5_23 <;> omega
    apply r5_24 <;> omega
  by_cases hJ18 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 104
    · apply r5_25 <;> omega
    apply r5_26 <;> omega
  by_cases hB0 : a.b ≤ 102
  · apply r5_27 <;> omega
  by_cases hB1 : a.b ≤ 119
  · apply r5_28 <;> omega
  apply r5_29 <;> omega

private theorem r6_0 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 18 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 18) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_1 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 21) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_2 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 24) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_3 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 27) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 32) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_4 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 30) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_5 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_6 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_7 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 38) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_8 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_9 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 40) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_10 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 41) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_11 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_12 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 42) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_13 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_14 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 43) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_15 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_16 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 111) (h₄ : a.j ≤ 44) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_17 {a : Shape} (h₁ : 112 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_18 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 108) (h₄ : a.j ≤ 45) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_19 {a : Shape} (h₁ : 109 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_20 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 46) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_21 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_22 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 104) (h₄ : a.j ≤ 47) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_23 {a : Shape} (h₁ : 105 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_24 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 102) (h₄ : a.j ≤ 48) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_25 {a : Shape} (h₁ : 103 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 48) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_26 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 48) (ht : a.t = 6) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_27 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 6) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_28 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 100) (h₄ : a.j ≤ 49) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_29 {a : Shape} (h₁ : 101 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 49) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_30 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 49) (ht : a.t = 6) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_31 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 49) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  oldRectangle (l := 50) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_32 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 49) (ht : a.t = 6) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_33 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 6) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact6 (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 6 .empty a.j := by
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
  by_cases hJ7 : a.j ≤ 38
  · apply r6_7 <;> omega
  by_cases hJ8 : a.j ≤ 39
  · apply r6_8 <;> omega
  by_cases hJ9 : a.j ≤ 40
  · apply r6_9 <;> omega
  by_cases hJ10 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 119
    · apply r6_10 <;> omega
    apply r6_11 <;> omega
  by_cases hJ11 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 116
    · apply r6_12 <;> omega
    apply r6_13 <;> omega
  by_cases hJ12 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 113
    · apply r6_14 <;> omega
    apply r6_15 <;> omega
  by_cases hJ13 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 111
    · apply r6_16 <;> omega
    apply r6_17 <;> omega
  by_cases hJ14 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 108
    · apply r6_18 <;> omega
    apply r6_19 <;> omega
  by_cases hJ15 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 106
    · apply r6_20 <;> omega
    apply r6_21 <;> omega
  by_cases hJ16 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 104
    · apply r6_22 <;> omega
    apply r6_23 <;> omega
  by_cases hJ17 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 102
    · apply r6_24 <;> omega
    by_cases hB1 : a.b ≤ 119
    · apply r6_25 <;> omega
    by_cases hB2 : a.b ≤ 120
    · apply r6_26 <;> omega
    apply r6_27 <;> omega
  by_cases hB0 : a.b ≤ 100
  · apply r6_28 <;> omega
  by_cases hB1 : a.b ≤ 117
  · apply r6_29 <;> omega
  by_cases hB2 : a.b ≤ 118
  · apply r6_30 <;> omega
  by_cases hB3 : a.b ≤ 119
  · apply r6_31 <;> omega
  by_cases hB4 : a.b ≤ 120
  · apply r6_32 <;> omega
  apply r6_33 <;> omega

private theorem r7_0 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 21 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 21) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_1 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 24) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 27) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_2 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 27) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 32) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_3 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 30) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_4 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_5 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_6 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 38) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_7 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_8 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 40) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_9 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 41) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_10 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_11 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 42) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_12 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 112) (h₄ : a.j ≤ 43) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_14 {a : Shape} (h₁ : 113 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_15 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 109) (h₄ : a.j ≤ 44) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_16 {a : Shape} (h₁ : 110 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_17 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 45) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_18 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_19 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 46) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_20 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_21 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 102) (h₄ : a.j ≤ 47) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_22 {a : Shape} (h₁ : 103 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 47) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_23 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_24 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 100) (h₄ : a.j ≤ 48) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_25 {a : Shape} (h₁ : 101 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 48) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_26 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 48) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_27 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 48) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_28 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 48) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_29 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_30 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 98) (h₄ : a.j ≤ 49) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_31 {a : Shape} (h₁ : 99 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 49) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_32 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 49) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_33 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 49) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_34 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 49) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_35 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 49) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_36 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 49) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_37 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 7) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact7 (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 7 .empty a.j := by
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
  by_cases hJ6 : a.j ≤ 38
  · apply r7_6 <;> omega
  by_cases hJ7 : a.j ≤ 39
  · apply r7_7 <;> omega
  by_cases hJ8 : a.j ≤ 40
  · apply r7_8 <;> omega
  by_cases hJ9 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 118
    · apply r7_9 <;> omega
    apply r7_10 <;> omega
  by_cases hJ10 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 115
    · apply r7_11 <;> omega
    apply r7_12 <;> omega
  by_cases hJ11 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 112
    · apply r7_13 <;> omega
    apply r7_14 <;> omega
  by_cases hJ12 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 109
    · apply r7_15 <;> omega
    apply r7_16 <;> omega
  by_cases hJ13 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 107
    · apply r7_17 <;> omega
    apply r7_18 <;> omega
  by_cases hJ14 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 105
    · apply r7_19 <;> omega
    apply r7_20 <;> omega
  by_cases hJ15 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 102
    · apply r7_21 <;> omega
    by_cases hB1 : a.b ≤ 120
    · apply r7_22 <;> omega
    apply r7_23 <;> omega
  by_cases hJ16 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 100
    · apply r7_24 <;> omega
    by_cases hB1 : a.b ≤ 117
    · apply r7_25 <;> omega
    by_cases hB2 : a.b ≤ 118
    · apply r7_26 <;> omega
    by_cases hB3 : a.b ≤ 119
    · apply r7_27 <;> omega
    by_cases hB4 : a.b ≤ 120
    · apply r7_28 <;> omega
    apply r7_29 <;> omega
  by_cases hB0 : a.b ≤ 98
  · apply r7_30 <;> omega
  by_cases hB1 : a.b ≤ 115
  · apply r7_31 <;> omega
  by_cases hB2 : a.b ≤ 116
  · apply r7_32 <;> omega
  by_cases hB3 : a.b ≤ 117
  · apply r7_33 <;> omega
  by_cases hB4 : a.b ≤ 118
  · apply r7_34 <;> omega
  by_cases hB5 : a.b ≤ 119
  · apply r7_35 <;> omega
  by_cases hB6 : a.b ≤ 120
  · apply r7_36 <;> omega
  apply r7_37 <;> omega

private theorem r8_0 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 24 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 24) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 32) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_1 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 27) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 32) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_2 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 30) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_3 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_4 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_5 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 38) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_6 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_7 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_8 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 40) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_9 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 41) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_10 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_11 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 42) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_12 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 111) (h₄ : a.j ≤ 43) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_14 {a : Shape} (h₁ : 112 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_15 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 108) (h₄ : a.j ≤ 44) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_16 {a : Shape} (h₁ : 109 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_17 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 45) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_18 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_19 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 103) (h₄ : a.j ≤ 46) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_20 {a : Shape} (h₁ : 104 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_21 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 101) (h₄ : a.j ≤ 47) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_22 {a : Shape} (h₁ : 102 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 47) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_23 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 47) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_24 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_25 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 99) (h₄ : a.j ≤ 48) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_26 {a : Shape} (h₁ : 100 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 48) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_27 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 48) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_28 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 48) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_29 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 48) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_30 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 48) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_31 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_32 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 97) (h₄ : a.j ≤ 49) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_33 {a : Shape} (h₁ : 98 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 49) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_34 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 49) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_35 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 49) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_36 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 49) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_37 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 49) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_38 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 49) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_39 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 49) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_40 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 8) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact8 (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 8 .empty a.j := by
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
  · by_cases hB0 : a.b ≤ 120
    · apply r8_7 <;> omega
    apply r8_8 <;> omega
  by_cases hJ8 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 117
    · apply r8_9 <;> omega
    apply r8_10 <;> omega
  by_cases hJ9 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 114
    · apply r8_11 <;> omega
    apply r8_12 <;> omega
  by_cases hJ10 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 111
    · apply r8_13 <;> omega
    apply r8_14 <;> omega
  by_cases hJ11 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 108
    · apply r8_15 <;> omega
    apply r8_16 <;> omega
  by_cases hJ12 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 106
    · apply r8_17 <;> omega
    apply r8_18 <;> omega
  by_cases hJ13 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 103
    · apply r8_19 <;> omega
    apply r8_20 <;> omega
  by_cases hJ14 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 101
    · apply r8_21 <;> omega
    by_cases hB1 : a.b ≤ 119
    · apply r8_22 <;> omega
    by_cases hB2 : a.b ≤ 120
    · apply r8_23 <;> omega
    apply r8_24 <;> omega
  by_cases hJ15 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 99
    · apply r8_25 <;> omega
    by_cases hB1 : a.b ≤ 116
    · apply r8_26 <;> omega
    by_cases hB2 : a.b ≤ 117
    · apply r8_27 <;> omega
    by_cases hB3 : a.b ≤ 118
    · apply r8_28 <;> omega
    by_cases hB4 : a.b ≤ 119
    · apply r8_29 <;> omega
    by_cases hB5 : a.b ≤ 120
    · apply r8_30 <;> omega
    apply r8_31 <;> omega
  by_cases hB0 : a.b ≤ 97
  · apply r8_32 <;> omega
  by_cases hB1 : a.b ≤ 114
  · apply r8_33 <;> omega
  by_cases hB2 : a.b ≤ 115
  · apply r8_34 <;> omega
  by_cases hB3 : a.b ≤ 116
  · apply r8_35 <;> omega
  by_cases hB4 : a.b ≤ 117
  · apply r8_36 <;> omega
  by_cases hB5 : a.b ≤ 118
  · apply r8_37 <;> omega
  by_cases hB6 : a.b ≤ 119
  · apply r8_38 <;> omega
  by_cases hB7 : a.b ≤ 120
  · apply r8_39 <;> omega
  apply r8_40 <;> omega

private theorem r9_0 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 27) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 37) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_1 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 30) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_2 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_3 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_4 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 38) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_5 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_6 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_7 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 40) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_8 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 41) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_9 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_10 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 42) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_11 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_12 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 43) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_13 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_14 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 108) (h₄ : a.j ≤ 44) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_15 {a : Shape} (h₁ : 109 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_16 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 45) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_17 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_18 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 103) (h₄ : a.j ≤ 46) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_19 {a : Shape} (h₁ : 104 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_20 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 100) (h₄ : a.j ≤ 47) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_21 {a : Shape} (h₁ : 101 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 47) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_22 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 47) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_23 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 47) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_24 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_25 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 98) (h₄ : a.j ≤ 48) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_26 {a : Shape} (h₁ : 99 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 48) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_27 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 48) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_28 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 48) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_29 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 48) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_30 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 48) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_31 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 48) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_32 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_33 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 96) (h₄ : a.j ≤ 49) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_34 {a : Shape} (h₁ : 97 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 49) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_35 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 49) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_36 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 49) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_37 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 49) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_38 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 49) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_39 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 49) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_40 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 49) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_41 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 49) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_42 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 9) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact9 (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 9 .empty a.j := by
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
  · by_cases hB0 : a.b ≤ 120
    · apply r9_6 <;> omega
    apply r9_7 <;> omega
  by_cases hJ7 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 116
    · apply r9_8 <;> omega
    apply r9_9 <;> omega
  by_cases hJ8 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 113
    · apply r9_10 <;> omega
    apply r9_11 <;> omega
  by_cases hJ9 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 110
    · apply r9_12 <;> omega
    apply r9_13 <;> omega
  by_cases hJ10 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 108
    · apply r9_14 <;> omega
    apply r9_15 <;> omega
  by_cases hJ11 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 105
    · apply r9_16 <;> omega
    apply r9_17 <;> omega
  by_cases hJ12 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 103
    · apply r9_18 <;> omega
    apply r9_19 <;> omega
  by_cases hJ13 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 100
    · apply r9_20 <;> omega
    by_cases hB1 : a.b ≤ 118
    · apply r9_21 <;> omega
    by_cases hB2 : a.b ≤ 119
    · apply r9_22 <;> omega
    by_cases hB3 : a.b ≤ 120
    · apply r9_23 <;> omega
    apply r9_24 <;> omega
  by_cases hJ14 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 98
    · apply r9_25 <;> omega
    by_cases hB1 : a.b ≤ 115
    · apply r9_26 <;> omega
    by_cases hB2 : a.b ≤ 116
    · apply r9_27 <;> omega
    by_cases hB3 : a.b ≤ 117
    · apply r9_28 <;> omega
    by_cases hB4 : a.b ≤ 118
    · apply r9_29 <;> omega
    by_cases hB5 : a.b ≤ 119
    · apply r9_30 <;> omega
    by_cases hB6 : a.b ≤ 120
    · apply r9_31 <;> omega
    apply r9_32 <;> omega
  by_cases hB0 : a.b ≤ 96
  · apply r9_33 <;> omega
  by_cases hB1 : a.b ≤ 113
  · apply r9_34 <;> omega
  by_cases hB2 : a.b ≤ 114
  · apply r9_35 <;> omega
  by_cases hB3 : a.b ≤ 115
  · apply r9_36 <;> omega
  by_cases hB4 : a.b ≤ 116
  · apply r9_37 <;> omega
  by_cases hB5 : a.b ≤ 117
  · apply r9_38 <;> omega
  by_cases hB6 : a.b ≤ 118
  · apply r9_39 <;> omega
  by_cases hB7 : a.b ≤ 119
  · apply r9_40 <;> omega
  by_cases hB8 : a.b ≤ 120
  · apply r9_41 <;> omega
  apply r9_42 <;> omega

private theorem r10_0 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 30) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 40) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_1 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_2 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_3 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 38) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_4 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_5 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_6 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 40) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_7 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 41) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_8 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_9 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 42) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_10 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_11 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 43) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_12 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 44) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_14 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_15 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 45) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_16 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_17 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 102) (h₄ : a.j ≤ 46) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_18 {a : Shape} (h₁ : 103 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_19 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_20 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 100) (h₄ : a.j ≤ 47) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_21 {a : Shape} (h₁ : 101 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 47) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_22 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 47) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_23 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 47) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_24 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 47) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_25 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_26 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 97) (h₄ : a.j ≤ 48) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_27 {a : Shape} (h₁ : 98 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 48) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_28 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 48) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_29 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 48) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_30 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 48) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_31 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 48) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_32 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 48) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_33 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_34 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 95) (h₄ : a.j ≤ 49) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_35 {a : Shape} (h₁ : 96 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 112) (h₄ : a.j ≤ 49) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_36 {a : Shape} (h₁ : 113 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 49) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_37 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 49) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_38 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 49) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_39 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 49) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_40 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 49) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_41 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 49) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_42 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 49) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_43 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 49) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_44 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 10) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact10 (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j := by
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
  · by_cases hB0 : a.b ≤ 120
    · apply r10_5 <;> omega
    apply r10_6 <;> omega
  by_cases hJ6 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 116
    · apply r10_7 <;> omega
    apply r10_8 <;> omega
  by_cases hJ7 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 113
    · apply r10_9 <;> omega
    apply r10_10 <;> omega
  by_cases hJ8 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 110
    · apply r10_11 <;> omega
    apply r10_12 <;> omega
  by_cases hJ9 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 107
    · apply r10_13 <;> omega
    apply r10_14 <;> omega
  by_cases hJ10 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 105
    · apply r10_15 <;> omega
    apply r10_16 <;> omega
  by_cases hJ11 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 102
    · apply r10_17 <;> omega
    by_cases hB1 : a.b ≤ 120
    · apply r10_18 <;> omega
    apply r10_19 <;> omega
  by_cases hJ12 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 100
    · apply r10_20 <;> omega
    by_cases hB1 : a.b ≤ 117
    · apply r10_21 <;> omega
    by_cases hB2 : a.b ≤ 118
    · apply r10_22 <;> omega
    by_cases hB3 : a.b ≤ 119
    · apply r10_23 <;> omega
    by_cases hB4 : a.b ≤ 120
    · apply r10_24 <;> omega
    apply r10_25 <;> omega
  by_cases hJ13 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 97
    · apply r10_26 <;> omega
    by_cases hB1 : a.b ≤ 115
    · apply r10_27 <;> omega
    by_cases hB2 : a.b ≤ 116
    · apply r10_28 <;> omega
    by_cases hB3 : a.b ≤ 117
    · apply r10_29 <;> omega
    by_cases hB4 : a.b ≤ 118
    · apply r10_30 <;> omega
    by_cases hB5 : a.b ≤ 119
    · apply r10_31 <;> omega
    by_cases hB6 : a.b ≤ 120
    · apply r10_32 <;> omega
    apply r10_33 <;> omega
  by_cases hB0 : a.b ≤ 95
  · apply r10_34 <;> omega
  by_cases hB1 : a.b ≤ 112
  · apply r10_35 <;> omega
  by_cases hB2 : a.b ≤ 113
  · apply r10_36 <;> omega
  by_cases hB3 : a.b ≤ 114
  · apply r10_37 <;> omega
  by_cases hB4 : a.b ≤ 115
  · apply r10_38 <;> omega
  by_cases hB5 : a.b ≤ 116
  · apply r10_39 <;> omega
  by_cases hB6 : a.b ≤ 117
  · apply r10_40 <;> omega
  by_cases hB7 : a.b ≤ 118
  · apply r10_41 <;> omega
  by_cases hB8 : a.b ≤ 119
  · apply r10_42 <;> omega
  by_cases hB9 : a.b ≤ 120
  · apply r10_43 <;> omega
  apply r10_44 <;> omega

private theorem r11_0 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 33) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_1 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_2 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 38) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_3 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_4 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_5 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 40) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_6 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 41) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_7 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_8 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 42) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_9 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_10 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 43) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_11 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_12 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 44) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_13 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_14 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 45) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_15 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_16 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_17 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 102) (h₄ : a.j ≤ 46) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_18 {a : Shape} (h₁ : 103 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_19 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_20 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 99) (h₄ : a.j ≤ 47) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_21 {a : Shape} (h₁ : 100 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 47) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_22 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 47) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_23 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 47) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_24 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 47) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_25 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_26 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 97) (h₄ : a.j ≤ 48) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_27 {a : Shape} (h₁ : 98 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 48) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_28 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 48) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_29 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 48) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_30 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 48) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_31 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 48) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_32 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 48) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_33 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 48) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_34 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_35 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 95) (h₄ : a.j ≤ 49) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_36 {a : Shape} (h₁ : 96 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 112) (h₄ : a.j ≤ 49) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_37 {a : Shape} (h₁ : 113 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 49) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_38 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 49) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_39 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 49) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_40 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 49) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_41 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 49) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_42 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 49) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_43 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 49) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_44 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 49) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_45 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 11) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact11 (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j := by
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
  · by_cases hB0 : a.b ≤ 120
    · apply r11_4 <;> omega
    apply r11_5 <;> omega
  by_cases hJ5 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 116
    · apply r11_6 <;> omega
    apply r11_7 <;> omega
  by_cases hJ6 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 113
    · apply r11_8 <;> omega
    apply r11_9 <;> omega
  by_cases hJ7 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 110
    · apply r11_10 <;> omega
    apply r11_11 <;> omega
  by_cases hJ8 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 107
    · apply r11_12 <;> omega
    apply r11_13 <;> omega
  by_cases hJ9 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 105
    · apply r11_14 <;> omega
    by_cases hB1 : a.b ≤ 120
    · apply r11_15 <;> omega
    apply r11_16 <;> omega
  by_cases hJ10 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 102
    · apply r11_17 <;> omega
    by_cases hB1 : a.b ≤ 120
    · apply r11_18 <;> omega
    apply r11_19 <;> omega
  by_cases hJ11 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 99
    · apply r11_20 <;> omega
    by_cases hB1 : a.b ≤ 117
    · apply r11_21 <;> omega
    by_cases hB2 : a.b ≤ 118
    · apply r11_22 <;> omega
    by_cases hB3 : a.b ≤ 119
    · apply r11_23 <;> omega
    by_cases hB4 : a.b ≤ 120
    · apply r11_24 <;> omega
    apply r11_25 <;> omega
  by_cases hJ12 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 97
    · apply r11_26 <;> omega
    by_cases hB1 : a.b ≤ 114
    · apply r11_27 <;> omega
    by_cases hB2 : a.b ≤ 115
    · apply r11_28 <;> omega
    by_cases hB3 : a.b ≤ 116
    · apply r11_29 <;> omega
    by_cases hB4 : a.b ≤ 117
    · apply r11_30 <;> omega
    by_cases hB5 : a.b ≤ 118
    · apply r11_31 <;> omega
    by_cases hB6 : a.b ≤ 119
    · apply r11_32 <;> omega
    by_cases hB7 : a.b ≤ 120
    · apply r11_33 <;> omega
    apply r11_34 <;> omega
  by_cases hB0 : a.b ≤ 95
  · apply r11_35 <;> omega
  by_cases hB1 : a.b ≤ 112
  · apply r11_36 <;> omega
  by_cases hB2 : a.b ≤ 113
  · apply r11_37 <;> omega
  by_cases hB3 : a.b ≤ 114
  · apply r11_38 <;> omega
  by_cases hB4 : a.b ≤ 115
  · apply r11_39 <;> omega
  by_cases hB5 : a.b ≤ 116
  · apply r11_40 <;> omega
  by_cases hB6 : a.b ≤ 117
  · apply r11_41 <;> omega
  by_cases hB7 : a.b ≤ 118
  · apply r11_42 <;> omega
  by_cases hB8 : a.b ≤ 119
  · apply r11_43 <;> omega
  by_cases hB9 : a.b ≤ 120
  · apply r11_44 <;> omega
  apply r11_45 <;> omega

private theorem r12_0 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 36) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_1 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 38) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_2 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_3 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_4 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 40) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_5 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 41) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_6 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_7 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 42) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_8 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_9 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 43) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_10 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_11 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 44) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_12 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 45) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_14 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_15 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 102) (h₄ : a.j ≤ 46) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_16 {a : Shape} (h₁ : 103 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_17 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_18 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 99) (h₄ : a.j ≤ 47) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_19 {a : Shape} (h₁ : 100 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 47) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_20 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 47) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_21 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 47) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_22 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 47) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_23 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_24 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 97) (h₄ : a.j ≤ 48) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_25 {a : Shape} (h₁ : 98 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 48) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_26 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 48) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_27 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 48) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_28 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 48) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_29 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 48) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_30 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 48) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_31 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 48) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_32 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_33 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 95) (h₄ : a.j ≤ 49) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_34 {a : Shape} (h₁ : 96 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 112) (h₄ : a.j ≤ 49) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_35 {a : Shape} (h₁ : 113 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 49) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_36 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 49) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_37 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 49) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_38 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 49) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_39 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 49) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_40 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 49) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_41 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 49) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_42 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 49) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_43 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 12) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact12 (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 36
  · apply r12_0 <;> omega
  by_cases hJ1 : a.j ≤ 38
  · apply r12_1 <;> omega
  by_cases hJ2 : a.j ≤ 39
  · apply r12_2 <;> omega
  by_cases hJ3 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 120
    · apply r12_3 <;> omega
    apply r12_4 <;> omega
  by_cases hJ4 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 117
    · apply r12_5 <;> omega
    apply r12_6 <;> omega
  by_cases hJ5 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 113
    · apply r12_7 <;> omega
    apply r12_8 <;> omega
  by_cases hJ6 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 110
    · apply r12_9 <;> omega
    apply r12_10 <;> omega
  by_cases hJ7 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 107
    · apply r12_11 <;> omega
    apply r12_12 <;> omega
  by_cases hJ8 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 105
    · apply r12_13 <;> omega
    apply r12_14 <;> omega
  by_cases hJ9 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 102
    · apply r12_15 <;> omega
    by_cases hB1 : a.b ≤ 120
    · apply r12_16 <;> omega
    apply r12_17 <;> omega
  by_cases hJ10 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 99
    · apply r12_18 <;> omega
    by_cases hB1 : a.b ≤ 117
    · apply r12_19 <;> omega
    by_cases hB2 : a.b ≤ 118
    · apply r12_20 <;> omega
    by_cases hB3 : a.b ≤ 119
    · apply r12_21 <;> omega
    by_cases hB4 : a.b ≤ 120
    · apply r12_22 <;> omega
    apply r12_23 <;> omega
  by_cases hJ11 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 97
    · apply r12_24 <;> omega
    by_cases hB1 : a.b ≤ 114
    · apply r12_25 <;> omega
    by_cases hB2 : a.b ≤ 115
    · apply r12_26 <;> omega
    by_cases hB3 : a.b ≤ 116
    · apply r12_27 <;> omega
    by_cases hB4 : a.b ≤ 117
    · apply r12_28 <;> omega
    by_cases hB5 : a.b ≤ 118
    · apply r12_29 <;> omega
    by_cases hB6 : a.b ≤ 119
    · apply r12_30 <;> omega
    by_cases hB7 : a.b ≤ 120
    · apply r12_31 <;> omega
    apply r12_32 <;> omega
  by_cases hB0 : a.b ≤ 95
  · apply r12_33 <;> omega
  by_cases hB1 : a.b ≤ 112
  · apply r12_34 <;> omega
  by_cases hB2 : a.b ≤ 113
  · apply r12_35 <;> omega
  by_cases hB3 : a.b ≤ 114
  · apply r12_36 <;> omega
  by_cases hB4 : a.b ≤ 115
  · apply r12_37 <;> omega
  by_cases hB5 : a.b ≤ 116
  · apply r12_38 <;> omega
  by_cases hB6 : a.b ≤ 117
  · apply r12_39 <;> omega
  by_cases hB7 : a.b ≤ 118
  · apply r12_40 <;> omega
  by_cases hB8 : a.b ≤ 119
  · apply r12_41 <;> omega
  by_cases hB9 : a.b ≤ 120
  · apply r12_42 <;> omega
  apply r12_43 <;> omega

private theorem r13_0 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 39) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_1 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_2 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 40) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_3 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 41) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_4 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 41) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_5 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 42) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_6 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 42) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_7 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 111) (h₄ : a.j ≤ 43) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_8 {a : Shape} (h₁ : 112 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 43) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_9 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 108) (h₄ : a.j ≤ 44) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_10 {a : Shape} (h₁ : 109 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 44) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_11 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 45) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_12 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 45) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_13 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 102) (h₄ : a.j ≤ 46) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_14 {a : Shape} (h₁ : 103 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_15 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 46) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_16 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 99) (h₄ : a.j ≤ 47) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_17 {a : Shape} (h₁ : 100 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 47) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_18 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 47) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_19 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 47) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_20 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 47) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_21 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 47) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_22 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 97) (h₄ : a.j ≤ 48) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_23 {a : Shape} (h₁ : 98 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 48) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_24 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 48) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_25 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 48) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_26 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 48) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_27 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 48) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_28 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 48) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_29 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 48) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_30 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 95) (h₄ : a.j ≤ 49) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_31 {a : Shape} (h₁ : 96 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 112) (h₄ : a.j ≤ 49) (ht : a.t = 13) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_32 {a : Shape} (h₁ : 113 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 49) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_33 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 49) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_34 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 49) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_35 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 49) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_36 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 49) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_37 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 49) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 49) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_38 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 49) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_39 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 49) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_40 {a : Shape} (h₁ : 121 ≤ a.b) (h₂ : 49 ≤ a.j)
    (h₃ : a.b ≤ 121) (h₄ : a.j ≤ 49) (ht : a.t = 13) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j :=
  point (l := 50) (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht
    (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact13 (a : Shape) (ha : Valid a) (ht : a.t = 13)
    (hb : a.b ≤ 121) (hj : a.j ≤ 49) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 39
  · apply r13_0 <;> omega
  by_cases hJ1 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 120
    · apply r13_1 <;> omega
    apply r13_2 <;> omega
  by_cases hJ2 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 117
    · apply r13_3 <;> omega
    apply r13_4 <;> omega
  by_cases hJ3 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 114
    · apply r13_5 <;> omega
    apply r13_6 <;> omega
  by_cases hJ4 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 111
    · apply r13_7 <;> omega
    apply r13_8 <;> omega
  by_cases hJ5 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 108
    · apply r13_9 <;> omega
    apply r13_10 <;> omega
  by_cases hJ6 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 105
    · apply r13_11 <;> omega
    apply r13_12 <;> omega
  by_cases hJ7 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 102
    · apply r13_13 <;> omega
    by_cases hB1 : a.b ≤ 120
    · apply r13_14 <;> omega
    apply r13_15 <;> omega
  by_cases hJ8 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 99
    · apply r13_16 <;> omega
    by_cases hB1 : a.b ≤ 117
    · apply r13_17 <;> omega
    by_cases hB2 : a.b ≤ 118
    · apply r13_18 <;> omega
    by_cases hB3 : a.b ≤ 119
    · apply r13_19 <;> omega
    by_cases hB4 : a.b ≤ 120
    · apply r13_20 <;> omega
    apply r13_21 <;> omega
  by_cases hJ9 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 97
    · apply r13_22 <;> omega
    by_cases hB1 : a.b ≤ 115
    · apply r13_23 <;> omega
    by_cases hB2 : a.b ≤ 116
    · apply r13_24 <;> omega
    by_cases hB3 : a.b ≤ 117
    · apply r13_25 <;> omega
    by_cases hB4 : a.b ≤ 118
    · apply r13_26 <;> omega
    by_cases hB5 : a.b ≤ 119
    · apply r13_27 <;> omega
    by_cases hB6 : a.b ≤ 120
    · apply r13_28 <;> omega
    apply r13_29 <;> omega
  by_cases hB0 : a.b ≤ 95
  · apply r13_30 <;> omega
  by_cases hB1 : a.b ≤ 112
  · apply r13_31 <;> omega
  by_cases hB2 : a.b ≤ 113
  · apply r13_32 <;> omega
  by_cases hB3 : a.b ≤ 114
  · apply r13_33 <;> omega
  by_cases hB4 : a.b ≤ 115
  · apply r13_34 <;> omega
  by_cases hB5 : a.b ≤ 116
  · apply r13_35 <;> omega
  by_cases hB6 : a.b ≤ 117
  · apply r13_36 <;> omega
  by_cases hB7 : a.b ≤ 118
  · apply r13_37 <;> omega
  by_cases hB8 : a.b ≤ 119
  · apply r13_38 <;> omega
  by_cases hB9 : a.b ≤ 120
  · apply r13_39 <;> omega
  apply r13_40 <;> omega

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .empty).plus a) (fullCap top)) :
    physicalPrice a (order .empty a) ≤ allowance top .empty a.j := by
  change 0+a.b ≤ 121 ∧ 0+a.j ≤ 49 ∧ 0+a.t ≤ top at hc
  obtain ⟨hb, hj, ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 121 := by omega
  have hj' : a.j ≤ 49 := by omega
  have hpt : a.t ≤ 13 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 ∨ a.t = 13 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11 | ht12 | ht13
  · exact (exact1 a ha ht1 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact2 a ha ht2 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact3 a ha ht3 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact4 a ha ht4 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact5 a ha ht5 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact6 a ha ht6 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact7 a ha ht7 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact8 a ha ht8 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact9 a ha ht9 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact10 a ha ht10 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact11 a ha ht11 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact12 a ha ht12 hb' hj').trans (allowance_mono .empty (by omega) htop)
  · exact (exact13 a ha ht13 hb' hj').trans (allowance_mono .empty (by omega) htop)
end Low48PriceTableEmpty
