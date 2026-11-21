import ProximityPrize.SubmissionLower.Low48PriceTableOne

set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
namespace Low48PriceTableTwo
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low48Price (fullCap physicalPrice)
open Low48PriceCaps (order allowance start allowance_mono)
open Low48PriceTableBase (PointClaim RectangleClaim pointBound rectangleBound)

private theorem r1_0 : RectangleClaim 3 .two 1 3 119 3 1 :=
  rectangleBound (l := 10) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1 : RectangleClaim 3 .two 2 4 119 5 1 :=
  rectangleBound (l := 10) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2 : RectangleClaim 3 .two 2 6 119 6 1 :=
  rectangleBound (l := 30) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_3 : RectangleClaim 3 .two 3 7 119 9 1 :=
  rectangleBound (l := 30) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_4 : RectangleClaim 3 .two 4 10 119 12 1 :=
  rectangleBound (l := 62) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_5 : RectangleClaim 3 .two 5 13 119 15 1 :=
  rectangleBound (l := 62) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_6 : RectangleClaim 3 .two 6 16 119 18 1 :=
  rectangleBound (l := 71) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_7 : RectangleClaim 3 .two 7 19 119 21 1 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_8 : RectangleClaim 3 .two 8 22 119 24 1 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_9 : RectangleClaim 3 .two 9 25 119 27 1 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_10 : RectangleClaim 3 .two 10 28 119 30 1 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_11 : RectangleClaim 3 .two 11 31 119 33 1 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_12 : RectangleClaim 3 .two 12 34 119 36 1 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_13 : RectangleClaim 3 .two 13 37 119 39 1 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_14 : RectangleClaim 3 .two 14 40 119 41 1 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_15 : RectangleClaim 3 .two 14 42 119 42 1 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_16 : RectangleClaim 3 .two 15 43 119 43 1 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact1 (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 3
  · apply r1_0 <;> omega
  by_cases hJ1 : a.j ≤ 5
  · apply r1_1 <;> omega
  by_cases hJ2 : a.j ≤ 6
  · apply r1_2 <;> omega
  by_cases hJ3 : a.j ≤ 9
  · apply r1_3 <;> omega
  by_cases hJ4 : a.j ≤ 12
  · apply r1_4 <;> omega
  by_cases hJ5 : a.j ≤ 15
  · apply r1_5 <;> omega
  by_cases hJ6 : a.j ≤ 18
  · apply r1_6 <;> omega
  by_cases hJ7 : a.j ≤ 21
  · apply r1_7 <;> omega
  by_cases hJ8 : a.j ≤ 24
  · apply r1_8 <;> omega
  by_cases hJ9 : a.j ≤ 27
  · apply r1_9 <;> omega
  by_cases hJ10 : a.j ≤ 30
  · apply r1_10 <;> omega
  by_cases hJ11 : a.j ≤ 33
  · apply r1_11 <;> omega
  by_cases hJ12 : a.j ≤ 36
  · apply r1_12 <;> omega
  by_cases hJ13 : a.j ≤ 39
  · apply r1_13 <;> omega
  by_cases hJ14 : a.j ≤ 41
  · apply r1_14 <;> omega
  by_cases hJ15 : a.j ≤ 42
  · apply r1_15 <;> omega
  apply r1_16 <;> omega

private theorem r2_0 : RectangleClaim 4 .two 2 6 119 6 2 :=
  rectangleBound (l := 30) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_1 : RectangleClaim 4 .two 3 7 119 9 2 :=
  rectangleBound (l := 30) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_2 : RectangleClaim 4 .two 4 10 119 12 2 :=
  rectangleBound (l := 62) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_3 : RectangleClaim 4 .two 5 13 119 15 2 :=
  rectangleBound (l := 62) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_4 : RectangleClaim 4 .two 6 16 119 18 2 :=
  rectangleBound (l := 71) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_5 : RectangleClaim 4 .two 7 19 119 21 2 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_6 : RectangleClaim 4 .two 8 22 119 24 2 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_7 : RectangleClaim 4 .two 9 25 119 27 2 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_8 : RectangleClaim 4 .two 10 28 119 30 2 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_9 : RectangleClaim 4 .two 11 31 119 33 2 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_10 : RectangleClaim 4 .two 12 34 119 36 2 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_11 : RectangleClaim 4 .two 13 37 119 39 2 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_12 : RectangleClaim 4 .two 14 40 119 41 2 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_13 : RectangleClaim 4 .two 14 42 119 42 2 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_14 : RectangleClaim 4 .two 15 43 117 43 2 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_15 : RectangleClaim 4 .two 118 43 119 43 2 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact2 (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 6
  · apply r2_0 <;> omega
  by_cases hJ1 : a.j ≤ 9
  · apply r2_1 <;> omega
  by_cases hJ2 : a.j ≤ 12
  · apply r2_2 <;> omega
  by_cases hJ3 : a.j ≤ 15
  · apply r2_3 <;> omega
  by_cases hJ4 : a.j ≤ 18
  · apply r2_4 <;> omega
  by_cases hJ5 : a.j ≤ 21
  · apply r2_5 <;> omega
  by_cases hJ6 : a.j ≤ 24
  · apply r2_6 <;> omega
  by_cases hJ7 : a.j ≤ 27
  · apply r2_7 <;> omega
  by_cases hJ8 : a.j ≤ 30
  · apply r2_8 <;> omega
  by_cases hJ9 : a.j ≤ 33
  · apply r2_9 <;> omega
  by_cases hJ10 : a.j ≤ 36
  · apply r2_10 <;> omega
  by_cases hJ11 : a.j ≤ 39
  · apply r2_11 <;> omega
  by_cases hJ12 : a.j ≤ 41
  · apply r2_12 <;> omega
  by_cases hJ13 : a.j ≤ 42
  · apply r2_13 <;> omega
  by_cases hB0 : a.b ≤ 117
  · apply r2_14 <;> omega
  apply r2_15 <;> omega

private theorem r3_0 : RectangleClaim 5 .two 3 9 119 9 3 :=
  rectangleBound (l := 62) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_1 : RectangleClaim 5 .two 4 10 119 12 3 :=
  rectangleBound (l := 62) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_2 : RectangleClaim 5 .two 5 13 119 15 3 :=
  rectangleBound (l := 62) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_3 : RectangleClaim 5 .two 6 16 119 18 3 :=
  rectangleBound (l := 71) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_4 : RectangleClaim 5 .two 7 19 119 21 3 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_5 : RectangleClaim 5 .two 8 22 119 24 3 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_6 : RectangleClaim 5 .two 9 25 119 27 3 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_7 : RectangleClaim 5 .two 10 28 119 30 3 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_8 : RectangleClaim 5 .two 11 31 119 33 3 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_9 : RectangleClaim 5 .two 12 34 119 36 3 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_10 : RectangleClaim 5 .two 13 37 119 38 3 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_11 : RectangleClaim 5 .two 13 39 119 39 3 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_12 : RectangleClaim 5 .two 14 40 119 40 3 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_13 : RectangleClaim 5 .two 14 41 118 41 3 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_14 : RectangleClaim 5 .two 119 41 119 41 3 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_15 : RectangleClaim 5 .two 14 42 116 42 3 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_16 : RectangleClaim 5 .two 117 42 119 42 3 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_17 : RectangleClaim 5 .two 15 43 114 43 3 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_18 : RectangleClaim 5 .two 115 43 119 43 3 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact3 (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 5 .two a.j := by
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
  by_cases hJ10 : a.j ≤ 38
  · apply r3_10 <;> omega
  by_cases hJ11 : a.j ≤ 39
  · apply r3_11 <;> omega
  by_cases hJ12 : a.j ≤ 40
  · apply r3_12 <;> omega
  by_cases hJ13 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 118
    · apply r3_13 <;> omega
    apply r3_14 <;> omega
  by_cases hJ14 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 116
    · apply r3_15 <;> omega
    apply r3_16 <;> omega
  by_cases hB0 : a.b ≤ 114
  · apply r3_17 <;> omega
  apply r3_18 <;> omega

private theorem r4_0 : RectangleClaim 6 .two 4 12 119 12 4 :=
  rectangleBound (l := 62) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_1 : RectangleClaim 6 .two 5 13 119 15 4 :=
  rectangleBound (l := 62) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_2 : RectangleClaim 6 .two 6 16 119 18 4 :=
  rectangleBound (l := 71) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_3 : RectangleClaim 6 .two 7 19 119 21 4 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_4 : RectangleClaim 6 .two 8 22 119 24 4 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_5 : RectangleClaim 6 .two 9 25 119 27 4 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_6 : RectangleClaim 6 .two 10 28 119 30 4 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_7 : RectangleClaim 6 .two 11 31 119 33 4 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_8 : RectangleClaim 6 .two 12 34 119 36 4 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_9 : RectangleClaim 6 .two 13 37 119 38 4 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_10 : RectangleClaim 6 .two 13 39 119 39 4 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_11 : RectangleClaim 6 .two 14 40 119 40 4 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_12 : RectangleClaim 6 .two 14 41 116 41 4 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_13 : RectangleClaim 6 .two 117 41 119 41 4 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_14 : RectangleClaim 6 .two 14 42 113 42 4 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_15 : RectangleClaim 6 .two 114 42 119 42 4 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_16 : RectangleClaim 6 .two 15 43 111 43 4 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_17 : RectangleClaim 6 .two 112 43 119 43 4 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact4 (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j := by
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
  by_cases hJ9 : a.j ≤ 38
  · apply r4_9 <;> omega
  by_cases hJ10 : a.j ≤ 39
  · apply r4_10 <;> omega
  by_cases hJ11 : a.j ≤ 40
  · apply r4_11 <;> omega
  by_cases hJ12 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 116
    · apply r4_12 <;> omega
    apply r4_13 <;> omega
  by_cases hJ13 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 113
    · apply r4_14 <;> omega
    apply r4_15 <;> omega
  by_cases hB0 : a.b ≤ 111
  · apply r4_16 <;> omega
  apply r4_17 <;> omega

private theorem r5_0 : RectangleClaim 7 .two 5 15 119 15 5 :=
  rectangleBound (l := 71) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_1 : RectangleClaim 7 .two 6 16 119 18 5 :=
  rectangleBound (l := 71) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_2 : RectangleClaim 7 .two 7 19 119 21 5 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_3 : RectangleClaim 7 .two 8 22 119 24 5 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_4 : RectangleClaim 7 .two 9 25 119 27 5 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_5 : RectangleClaim 7 .two 10 28 119 30 5 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_6 : RectangleClaim 7 .two 11 31 119 33 5 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_7 : RectangleClaim 7 .two 12 34 119 36 5 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_8 : RectangleClaim 7 .two 13 37 119 38 5 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_9 : RectangleClaim 7 .two 13 39 119 39 5 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_10 : RectangleClaim 7 .two 14 40 117 40 5 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_11 : RectangleClaim 7 .two 118 40 119 40 5 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_12 : RectangleClaim 7 .two 14 41 114 41 5 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_13 : RectangleClaim 7 .two 115 41 119 41 5 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_14 : RectangleClaim 7 .two 14 42 111 42 5 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_15 : RectangleClaim 7 .two 112 42 119 42 5 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_16 : RectangleClaim 7 .two 15 43 109 43 5 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_17 : RectangleClaim 7 .two 110 43 119 43 5 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact5 (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j := by
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
  · by_cases hB0 : a.b ≤ 117
    · apply r5_10 <;> omega
    apply r5_11 <;> omega
  by_cases hJ11 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 114
    · apply r5_12 <;> omega
    apply r5_13 <;> omega
  by_cases hJ12 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 111
    · apply r5_14 <;> omega
    apply r5_15 <;> omega
  by_cases hB0 : a.b ≤ 109
  · apply r5_16 <;> omega
  apply r5_17 <;> omega

private theorem r6_0 : RectangleClaim 8 .two 6 18 119 18 6 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_1 : RectangleClaim 8 .two 7 19 119 21 6 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_2 : RectangleClaim 8 .two 8 22 119 24 6 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_3 : RectangleClaim 8 .two 9 25 119 27 6 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_4 : RectangleClaim 8 .two 10 28 119 30 6 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_5 : RectangleClaim 8 .two 11 31 119 33 6 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_6 : RectangleClaim 8 .two 12 34 119 36 6 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_7 : RectangleClaim 8 .two 13 37 119 37 6 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_8 : RectangleClaim 8 .two 13 38 119 38 6 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_9 : RectangleClaim 8 .two 13 39 119 39 6 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_10 : RectangleClaim 8 .two 14 40 116 40 6 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_11 : RectangleClaim 8 .two 117 40 119 40 6 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_12 : RectangleClaim 8 .two 14 41 113 41 6 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_13 : RectangleClaim 8 .two 114 41 119 41 6 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_14 : RectangleClaim 8 .two 14 42 110 42 6 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_15 : RectangleClaim 8 .two 111 42 119 42 6 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_16 : RectangleClaim 8 .two 15 43 108 43 6 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_17 : RectangleClaim 8 .two 109 43 119 43 6 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact6 (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j := by
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
  by_cases hJ7 : a.j ≤ 37
  · apply r6_7 <;> omega
  by_cases hJ8 : a.j ≤ 38
  · apply r6_8 <;> omega
  by_cases hJ9 : a.j ≤ 39
  · apply r6_9 <;> omega
  by_cases hJ10 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 116
    · apply r6_10 <;> omega
    apply r6_11 <;> omega
  by_cases hJ11 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 113
    · apply r6_12 <;> omega
    apply r6_13 <;> omega
  by_cases hJ12 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 110
    · apply r6_14 <;> omega
    apply r6_15 <;> omega
  by_cases hB0 : a.b ≤ 108
  · apply r6_16 <;> omega
  apply r6_17 <;> omega

private theorem r7_0 : RectangleClaim 9 .two 7 21 119 21 7 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_1 : RectangleClaim 9 .two 8 22 119 24 7 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_2 : RectangleClaim 9 .two 9 25 119 27 7 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_3 : RectangleClaim 9 .two 10 28 119 30 7 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_4 : RectangleClaim 9 .two 11 31 119 33 7 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_5 : RectangleClaim 9 .two 12 34 119 36 7 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_6 : RectangleClaim 9 .two 13 37 119 37 7 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_7 : RectangleClaim 9 .two 13 38 119 38 7 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_8 : RectangleClaim 9 .two 13 39 118 39 7 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_9 : RectangleClaim 9 .two 119 39 119 39 7 :=
  rectangleBound (l := 86) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_10 : RectangleClaim 9 .two 14 40 115 40 7 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_11 : RectangleClaim 9 .two 116 40 119 40 7 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_12 : RectangleClaim 9 .two 14 41 112 41 7 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_13 : RectangleClaim 9 .two 113 41 119 41 7 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_14 : RectangleClaim 9 .two 14 42 109 42 7 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_15 : RectangleClaim 9 .two 110 42 119 42 7 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_16 : RectangleClaim 9 .two 15 43 107 43 7 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_17 : RectangleClaim 9 .two 108 43 119 43 7 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact7 (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j := by
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
  by_cases hJ6 : a.j ≤ 37
  · apply r7_6 <;> omega
  by_cases hJ7 : a.j ≤ 38
  · apply r7_7 <;> omega
  by_cases hJ8 : a.j ≤ 39
  · by_cases hB0 : a.b ≤ 118
    · apply r7_8 <;> omega
    apply r7_9 <;> omega
  by_cases hJ9 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 115
    · apply r7_10 <;> omega
    apply r7_11 <;> omega
  by_cases hJ10 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 112
    · apply r7_12 <;> omega
    apply r7_13 <;> omega
  by_cases hJ11 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 109
    · apply r7_14 <;> omega
    apply r7_15 <;> omega
  by_cases hB0 : a.b ≤ 107
  · apply r7_16 <;> omega
  apply r7_17 <;> omega

private theorem r8_0 : RectangleClaim 10 .two 8 24 119 24 8 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_1 : RectangleClaim 10 .two 9 25 119 27 8 :=
  rectangleBound (l := 73) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_2 : RectangleClaim 10 .two 10 28 119 30 8 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_3 : RectangleClaim 10 .two 11 31 119 33 8 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_4 : RectangleClaim 10 .two 12 34 119 36 8 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_5 : RectangleClaim 10 .two 13 37 119 37 8 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_6 : RectangleClaim 10 .two 13 38 119 38 8 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_7 : RectangleClaim 10 .two 13 39 118 39 8 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_8 : RectangleClaim 10 .two 119 39 119 39 8 :=
  rectangleBound (l := 86) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_9 : RectangleClaim 10 .two 14 40 115 40 8 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_10 : RectangleClaim 10 .two 116 40 119 40 8 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_11 : RectangleClaim 10 .two 14 41 112 41 8 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_12 : RectangleClaim 10 .two 113 41 119 41 8 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_13 : RectangleClaim 10 .two 14 42 109 42 8 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_14 : RectangleClaim 10 .two 110 42 119 42 8 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_15 : RectangleClaim 10 .two 15 43 106 43 8 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_16 : RectangleClaim 10 .two 107 43 119 43 8 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact8 (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j := by
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
  by_cases hJ5 : a.j ≤ 37
  · apply r8_5 <;> omega
  by_cases hJ6 : a.j ≤ 38
  · apply r8_6 <;> omega
  by_cases hJ7 : a.j ≤ 39
  · by_cases hB0 : a.b ≤ 118
    · apply r8_7 <;> omega
    apply r8_8 <;> omega
  by_cases hJ8 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 115
    · apply r8_9 <;> omega
    apply r8_10 <;> omega
  by_cases hJ9 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 112
    · apply r8_11 <;> omega
    apply r8_12 <;> omega
  by_cases hJ10 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 109
    · apply r8_13 <;> omega
    apply r8_14 <;> omega
  by_cases hB0 : a.b ≤ 106
  · apply r8_15 <;> omega
  apply r8_16 <;> omega

private theorem r9_0 : RectangleClaim 11 .two 9 27 119 27 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_1 : RectangleClaim 11 .two 10 28 119 30 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_2 : RectangleClaim 11 .two 11 31 119 33 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_3 : RectangleClaim 11 .two 12 34 119 36 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_4 : RectangleClaim 11 .two 13 37 119 37 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_5 : RectangleClaim 11 .two 13 38 119 38 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_6 : RectangleClaim 11 .two 13 39 118 39 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_7 : RectangleClaim 11 .two 119 39 119 39 9 :=
  rectangleBound (l := 86) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_8 : RectangleClaim 11 .two 14 40 115 40 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_9 : RectangleClaim 11 .two 116 40 119 40 9 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_10 : RectangleClaim 11 .two 14 41 112 41 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_11 : RectangleClaim 11 .two 113 41 119 41 9 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_12 : RectangleClaim 11 .two 14 42 109 42 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_13 : RectangleClaim 11 .two 110 42 119 42 9 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_14 : RectangleClaim 11 .two 15 43 106 43 9 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_15 : RectangleClaim 11 .two 107 43 119 43 9 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact9 (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 27
  · apply r9_0 <;> omega
  by_cases hJ1 : a.j ≤ 30
  · apply r9_1 <;> omega
  by_cases hJ2 : a.j ≤ 33
  · apply r9_2 <;> omega
  by_cases hJ3 : a.j ≤ 36
  · apply r9_3 <;> omega
  by_cases hJ4 : a.j ≤ 37
  · apply r9_4 <;> omega
  by_cases hJ5 : a.j ≤ 38
  · apply r9_5 <;> omega
  by_cases hJ6 : a.j ≤ 39
  · by_cases hB0 : a.b ≤ 118
    · apply r9_6 <;> omega
    apply r9_7 <;> omega
  by_cases hJ7 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 115
    · apply r9_8 <;> omega
    apply r9_9 <;> omega
  by_cases hJ8 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 112
    · apply r9_10 <;> omega
    apply r9_11 <;> omega
  by_cases hJ9 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 109
    · apply r9_12 <;> omega
    apply r9_13 <;> omega
  by_cases hB0 : a.b ≤ 106
  · apply r9_14 <;> omega
  apply r9_15 <;> omega

private theorem r10_0 : RectangleClaim 12 .two 10 30 119 30 10 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_1 : RectangleClaim 12 .two 11 31 119 33 10 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_2 : RectangleClaim 12 .two 12 34 119 36 10 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_3 : RectangleClaim 12 .two 13 37 119 37 10 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_4 : RectangleClaim 12 .two 13 38 119 38 10 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_5 : RectangleClaim 12 .two 13 39 118 39 10 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_6 : RectangleClaim 12 .two 119 39 119 39 10 :=
  rectangleBound (l := 86) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_7 : RectangleClaim 12 .two 14 40 115 40 10 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_8 : RectangleClaim 12 .two 116 40 119 40 10 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_9 : RectangleClaim 12 .two 14 41 112 41 10 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_10 : RectangleClaim 12 .two 113 41 119 41 10 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_11 : RectangleClaim 12 .two 14 42 109 42 10 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_12 : RectangleClaim 12 .two 110 42 119 42 10 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_13 : RectangleClaim 12 .two 15 43 106 43 10 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_14 : RectangleClaim 12 .two 107 43 119 43 10 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact10 (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 30
  · apply r10_0 <;> omega
  by_cases hJ1 : a.j ≤ 33
  · apply r10_1 <;> omega
  by_cases hJ2 : a.j ≤ 36
  · apply r10_2 <;> omega
  by_cases hJ3 : a.j ≤ 37
  · apply r10_3 <;> omega
  by_cases hJ4 : a.j ≤ 38
  · apply r10_4 <;> omega
  by_cases hJ5 : a.j ≤ 39
  · by_cases hB0 : a.b ≤ 118
    · apply r10_5 <;> omega
    apply r10_6 <;> omega
  by_cases hJ6 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 115
    · apply r10_7 <;> omega
    apply r10_8 <;> omega
  by_cases hJ7 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 112
    · apply r10_9 <;> omega
    apply r10_10 <;> omega
  by_cases hJ8 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 109
    · apply r10_11 <;> omega
    apply r10_12 <;> omega
  by_cases hB0 : a.b ≤ 106
  · apply r10_13 <;> omega
  apply r10_14 <;> omega

private theorem r11_0 : RectangleClaim 13 .two 11 33 119 33 11 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_1 : RectangleClaim 13 .two 12 34 119 36 11 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_2 : RectangleClaim 13 .two 13 37 119 38 11 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_3 : RectangleClaim 13 .two 13 39 119 39 11 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_4 : RectangleClaim 13 .two 14 40 116 40 11 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_5 : RectangleClaim 13 .two 117 40 119 40 11 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_6 : RectangleClaim 13 .two 14 41 112 41 11 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_7 : RectangleClaim 13 .two 113 41 119 41 11 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_8 : RectangleClaim 13 .two 14 42 109 42 11 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_9 : RectangleClaim 13 .two 110 42 119 42 11 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_10 : RectangleClaim 13 .two 15 43 106 43 11 :=
  rectangleBound (l := 77) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_11 : RectangleClaim 13 .two 107 43 119 43 11 :=
  rectangleBound (l := 87) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact11 (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j := by
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
  · by_cases hB0 : a.b ≤ 116
    · apply r11_4 <;> omega
    apply r11_5 <;> omega
  by_cases hJ5 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 112
    · apply r11_6 <;> omega
    apply r11_7 <;> omega
  by_cases hJ6 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 109
    · apply r11_8 <;> omega
    apply r11_9 <;> omega
  by_cases hB0 : a.b ≤ 106
  · apply r11_10 <;> omega
  apply r11_11 <;> omega

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
