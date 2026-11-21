import ProximityPrize.SubmissionLower.Low48PriceTableEmpty

set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
namespace Low48PriceTableOne
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low48Price (fullCap physicalPrice)
open Low48PriceCaps (order allowance start allowance_mono)
open Low48PriceTableBase (PointClaim RectangleClaim pointBound rectangleBound)

private theorem r1_0 : RectangleClaim 2 .one 1 3 120 3 1 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1 : RectangleClaim 2 .one 2 4 66 4 1 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2 : RectangleClaim 2 .one 67 4 120 4 1 :=
  rectangleBound (l := 2) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_3 : RectangleClaim 2 .one 2 5 120 5 1 :=
  rectangleBound (l := 4) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_4 : RectangleClaim 2 .one 2 6 120 6 1 :=
  rectangleBound (l := 11) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_5 : RectangleClaim 2 .one 3 7 120 8 1 :=
  rectangleBound (l := 11) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_6 : RectangleClaim 2 .one 3 9 120 9 1 :=
  rectangleBound (l := 20) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_7 : RectangleClaim 2 .one 4 10 120 12 1 :=
  rectangleBound (l := 20) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_8 : RectangleClaim 2 .one 5 13 120 15 1 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_9 : RectangleClaim 2 .one 6 16 120 18 1 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_10 : RectangleClaim 2 .one 7 19 120 21 1 :=
  rectangleBound (l := 44) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_11 : RectangleClaim 2 .one 8 22 120 24 1 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_12 : RectangleClaim 2 .one 9 25 120 27 1 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_13 : RectangleClaim 2 .one 10 28 120 30 1 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_14 : RectangleClaim 2 .one 11 31 120 33 1 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_15 : RectangleClaim 2 .one 12 34 120 36 1 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_16 : RectangleClaim 2 .one 13 37 120 39 1 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_17 : RectangleClaim 2 .one 14 40 120 42 1 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_18 : RectangleClaim 2 .one 15 43 120 45 1 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_19 : RectangleClaim 2 .one 16 46 120 46 1 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact1 (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 3
  · apply r1_0 <;> omega
  by_cases hJ1 : a.j ≤ 4
  · by_cases hB0 : a.b ≤ 66
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

private theorem r2_0 : RectangleClaim 3 .one 2 6 120 6 2 :=
  rectangleBound (l := 11) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_1 : RectangleClaim 3 .one 3 7 120 8 2 :=
  rectangleBound (l := 11) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_2 : RectangleClaim 3 .one 3 9 120 9 2 :=
  rectangleBound (l := 20) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_3 : RectangleClaim 3 .one 4 10 120 12 2 :=
  rectangleBound (l := 20) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_4 : RectangleClaim 3 .one 5 13 120 15 2 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_5 : RectangleClaim 3 .one 6 16 120 18 2 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_6 : RectangleClaim 3 .one 7 19 120 21 2 :=
  rectangleBound (l := 44) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_7 : RectangleClaim 3 .one 8 22 120 24 2 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_8 : RectangleClaim 3 .one 9 25 120 27 2 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_9 : RectangleClaim 3 .one 10 28 120 30 2 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_10 : RectangleClaim 3 .one 11 31 120 33 2 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_11 : RectangleClaim 3 .one 12 34 120 36 2 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_12 : RectangleClaim 3 .one 13 37 120 39 2 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_13 : RectangleClaim 3 .one 14 40 120 42 2 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_14 : RectangleClaim 3 .one 15 43 120 44 2 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_15 : RectangleClaim 3 .one 15 45 120 45 2 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_16 : RectangleClaim 3 .one 16 46 120 46 2 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r3_0 : RectangleClaim 4 .one 3 9 120 9 3 :=
  rectangleBound (l := 20) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_1 : RectangleClaim 4 .one 4 10 120 12 3 :=
  rectangleBound (l := 20) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_2 : RectangleClaim 4 .one 5 13 120 15 3 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_3 : RectangleClaim 4 .one 6 16 120 18 3 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_4 : RectangleClaim 4 .one 7 19 120 21 3 :=
  rectangleBound (l := 44) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_5 : RectangleClaim 4 .one 8 22 120 24 3 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_6 : RectangleClaim 4 .one 9 25 120 27 3 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_7 : RectangleClaim 4 .one 10 28 120 30 3 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_8 : RectangleClaim 4 .one 11 31 120 33 3 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_9 : RectangleClaim 4 .one 12 34 120 36 3 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_10 : RectangleClaim 4 .one 13 37 120 39 3 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_11 : RectangleClaim 4 .one 14 40 120 42 3 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_12 : RectangleClaim 4 .one 15 43 120 43 3 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_13 : RectangleClaim 4 .one 15 44 120 44 3 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_14 : RectangleClaim 4 .one 15 45 120 45 3 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_15 : RectangleClaim 4 .one 16 46 117 46 3 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_16 : RectangleClaim 4 .one 118 46 120 46 3 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

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
  · apply r3_14 <;> omega
  by_cases hB0 : a.b ≤ 117
  · apply r3_15 <;> omega
  apply r3_16 <;> omega

private theorem r4_0 : RectangleClaim 5 .one 4 12 120 12 4 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_1 : RectangleClaim 5 .one 5 13 120 15 4 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_2 : RectangleClaim 5 .one 6 16 120 18 4 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_3 : RectangleClaim 5 .one 7 19 120 21 4 :=
  rectangleBound (l := 44) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_4 : RectangleClaim 5 .one 8 22 120 24 4 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_5 : RectangleClaim 5 .one 9 25 120 27 4 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_6 : RectangleClaim 5 .one 10 28 120 30 4 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_7 : RectangleClaim 5 .one 11 31 120 33 4 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_8 : RectangleClaim 5 .one 12 34 120 36 4 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_9 : RectangleClaim 5 .one 13 37 120 39 4 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_10 : RectangleClaim 5 .one 14 40 120 41 4 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_11 : RectangleClaim 5 .one 14 42 120 42 4 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_12 : RectangleClaim 5 .one 15 43 120 43 4 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_13 : RectangleClaim 5 .one 15 44 119 44 4 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_14 : RectangleClaim 5 .one 120 44 120 44 4 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_15 : RectangleClaim 5 .one 15 45 116 45 4 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_16 : RectangleClaim 5 .one 117 45 120 45 4 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_17 : RectangleClaim 5 .one 16 46 114 46 4 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_18 : RectangleClaim 5 .one 115 46 120 46 4 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

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
  · by_cases hB0 : a.b ≤ 119
    · apply r4_13 <;> omega
    apply r4_14 <;> omega
  by_cases hJ14 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 116
    · apply r4_15 <;> omega
    apply r4_16 <;> omega
  by_cases hB0 : a.b ≤ 114
  · apply r4_17 <;> omega
  apply r4_18 <;> omega

private theorem r5_0 : RectangleClaim 6 .one 5 15 120 15 5 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_1 : RectangleClaim 6 .one 6 16 120 18 5 :=
  rectangleBound (l := 38) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_2 : RectangleClaim 6 .one 7 19 120 21 5 :=
  rectangleBound (l := 44) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_3 : RectangleClaim 6 .one 8 22 120 24 5 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_4 : RectangleClaim 6 .one 9 25 120 27 5 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_5 : RectangleClaim 6 .one 10 28 120 30 5 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_6 : RectangleClaim 6 .one 11 31 120 33 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_7 : RectangleClaim 6 .one 12 34 120 36 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_8 : RectangleClaim 6 .one 13 37 120 39 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_9 : RectangleClaim 6 .one 14 40 120 41 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_10 : RectangleClaim 6 .one 14 42 120 42 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_11 : RectangleClaim 6 .one 15 43 119 43 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_12 : RectangleClaim 6 .one 120 43 120 43 5 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_13 : RectangleClaim 6 .one 15 44 116 44 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_14 : RectangleClaim 6 .one 117 44 120 44 5 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_15 : RectangleClaim 6 .one 15 45 114 45 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_16 : RectangleClaim 6 .one 115 45 120 45 5 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_17 : RectangleClaim 6 .one 16 46 112 46 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_18 : RectangleClaim 6 .one 113 46 120 46 5 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

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
  · by_cases hB0 : a.b ≤ 119
    · apply r5_11 <;> omega
    apply r5_12 <;> omega
  by_cases hJ12 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 116
    · apply r5_13 <;> omega
    apply r5_14 <;> omega
  by_cases hJ13 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 114
    · apply r5_15 <;> omega
    apply r5_16 <;> omega
  by_cases hB0 : a.b ≤ 112
  · apply r5_17 <;> omega
  apply r5_18 <;> omega

private theorem r6_0 : RectangleClaim 7 .one 6 18 120 18 6 :=
  rectangleBound (l := 44) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_1 : RectangleClaim 7 .one 7 19 120 21 6 :=
  rectangleBound (l := 44) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_2 : RectangleClaim 7 .one 8 22 120 24 6 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_3 : RectangleClaim 7 .one 9 25 120 27 6 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_4 : RectangleClaim 7 .one 10 28 120 30 6 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_5 : RectangleClaim 7 .one 11 31 120 33 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_6 : RectangleClaim 7 .one 12 34 120 36 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_7 : RectangleClaim 7 .one 13 37 120 39 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_8 : RectangleClaim 7 .one 14 40 120 41 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_9 : RectangleClaim 7 .one 14 42 120 42 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_10 : RectangleClaim 7 .one 15 43 117 43 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_11 : RectangleClaim 7 .one 118 43 120 43 6 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_12 : RectangleClaim 7 .one 15 44 115 44 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_13 : RectangleClaim 7 .one 116 44 120 44 6 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_14 : RectangleClaim 7 .one 15 45 112 45 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_15 : RectangleClaim 7 .one 113 45 120 45 6 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_16 : RectangleClaim 7 .one 16 46 110 46 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_17 : RectangleClaim 7 .one 111 46 120 46 6 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

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
  by_cases hJ8 : a.j ≤ 41
  · apply r6_8 <;> omega
  by_cases hJ9 : a.j ≤ 42
  · apply r6_9 <;> omega
  by_cases hJ10 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 117
    · apply r6_10 <;> omega
    apply r6_11 <;> omega
  by_cases hJ11 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 115
    · apply r6_12 <;> omega
    apply r6_13 <;> omega
  by_cases hJ12 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 112
    · apply r6_14 <;> omega
    apply r6_15 <;> omega
  by_cases hB0 : a.b ≤ 110
  · apply r6_16 <;> omega
  apply r6_17 <;> omega

private theorem r7_0 : RectangleClaim 8 .one 7 21 120 21 7 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_1 : RectangleClaim 8 .one 8 22 120 24 7 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_2 : RectangleClaim 8 .one 9 25 120 27 7 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_3 : RectangleClaim 8 .one 10 28 120 30 7 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_4 : RectangleClaim 8 .one 11 31 120 33 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_5 : RectangleClaim 8 .one 12 34 120 36 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_6 : RectangleClaim 8 .one 13 37 120 39 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_7 : RectangleClaim 8 .one 14 40 120 40 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_8 : RectangleClaim 8 .one 14 41 120 41 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_9 : RectangleClaim 8 .one 14 42 119 42 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_10 : RectangleClaim 8 .one 120 42 120 42 7 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_11 : RectangleClaim 8 .one 15 43 116 43 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_12 : RectangleClaim 8 .one 117 43 120 43 7 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_13 : RectangleClaim 8 .one 15 44 113 44 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_14 : RectangleClaim 8 .one 114 44 120 44 7 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_15 : RectangleClaim 8 .one 15 45 111 45 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_16 : RectangleClaim 8 .one 112 45 120 45 7 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_17 : RectangleClaim 8 .one 16 46 108 46 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_18 : RectangleClaim 8 .one 109 46 120 46 7 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

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
  · by_cases hB0 : a.b ≤ 119
    · apply r7_9 <;> omega
    apply r7_10 <;> omega
  by_cases hJ10 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 116
    · apply r7_11 <;> omega
    apply r7_12 <;> omega
  by_cases hJ11 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 113
    · apply r7_13 <;> omega
    apply r7_14 <;> omega
  by_cases hJ12 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 111
    · apply r7_15 <;> omega
    apply r7_16 <;> omega
  by_cases hB0 : a.b ≤ 108
  · apply r7_17 <;> omega
  apply r7_18 <;> omega

private theorem r8_0 : RectangleClaim 9 .one 8 24 120 24 8 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_1 : RectangleClaim 9 .one 9 25 120 27 8 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_2 : RectangleClaim 9 .one 10 28 120 30 8 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_3 : RectangleClaim 9 .one 11 31 120 33 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_4 : RectangleClaim 9 .one 12 34 120 36 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_5 : RectangleClaim 9 .one 13 37 120 39 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_6 : RectangleClaim 9 .one 14 40 120 40 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_7 : RectangleClaim 9 .one 14 41 120 41 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_8 : RectangleClaim 9 .one 14 42 118 42 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_9 : RectangleClaim 9 .one 119 42 120 42 8 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_10 : RectangleClaim 9 .one 15 43 115 43 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_11 : RectangleClaim 9 .one 116 43 120 43 8 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_12 : RectangleClaim 9 .one 15 44 112 44 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_13 : RectangleClaim 9 .one 113 44 120 44 8 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_14 : RectangleClaim 9 .one 15 45 110 45 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_15 : RectangleClaim 9 .one 111 45 120 45 8 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_16 : RectangleClaim 9 .one 16 46 107 46 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_17 : RectangleClaim 9 .one 108 46 120 46 8 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

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
  by_cases hJ5 : a.j ≤ 39
  · apply r8_5 <;> omega
  by_cases hJ6 : a.j ≤ 40
  · apply r8_6 <;> omega
  by_cases hJ7 : a.j ≤ 41
  · apply r8_7 <;> omega
  by_cases hJ8 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 118
    · apply r8_8 <;> omega
    apply r8_9 <;> omega
  by_cases hJ9 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 115
    · apply r8_10 <;> omega
    apply r8_11 <;> omega
  by_cases hJ10 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 112
    · apply r8_12 <;> omega
    apply r8_13 <;> omega
  by_cases hJ11 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 110
    · apply r8_14 <;> omega
    apply r8_15 <;> omega
  by_cases hB0 : a.b ≤ 107
  · apply r8_16 <;> omega
  apply r8_17 <;> omega

private theorem r9_0 : RectangleClaim 10 .one 9 27 120 27 9 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_1 : RectangleClaim 10 .one 10 28 120 30 9 :=
  rectangleBound (l := 46) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_2 : RectangleClaim 10 .one 11 31 120 33 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_3 : RectangleClaim 10 .one 12 34 120 36 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_4 : RectangleClaim 10 .one 13 37 120 39 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_5 : RectangleClaim 10 .one 14 40 120 40 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_6 : RectangleClaim 10 .one 14 41 120 41 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_7 : RectangleClaim 10 .one 14 42 117 42 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_8 : RectangleClaim 10 .one 118 42 120 42 9 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_9 : RectangleClaim 10 .one 15 43 114 43 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_10 : RectangleClaim 10 .one 115 43 120 43 9 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_11 : RectangleClaim 10 .one 15 44 112 44 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_12 : RectangleClaim 10 .one 113 44 120 44 9 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_13 : RectangleClaim 10 .one 15 45 109 45 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_14 : RectangleClaim 10 .one 110 45 120 45 9 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_15 : RectangleClaim 10 .one 16 46 106 46 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_16 : RectangleClaim 10 .one 107 46 120 46 9 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

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
  by_cases hJ4 : a.j ≤ 39
  · apply r9_4 <;> omega
  by_cases hJ5 : a.j ≤ 40
  · apply r9_5 <;> omega
  by_cases hJ6 : a.j ≤ 41
  · apply r9_6 <;> omega
  by_cases hJ7 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 117
    · apply r9_7 <;> omega
    apply r9_8 <;> omega
  by_cases hJ8 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 114
    · apply r9_9 <;> omega
    apply r9_10 <;> omega
  by_cases hJ9 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 112
    · apply r9_11 <;> omega
    apply r9_12 <;> omega
  by_cases hJ10 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 109
    · apply r9_13 <;> omega
    apply r9_14 <;> omega
  by_cases hB0 : a.b ≤ 106
  · apply r9_15 <;> omega
  apply r9_16 <;> omega

private theorem r10_0 : RectangleClaim 11 .one 10 30 120 30 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_1 : RectangleClaim 11 .one 11 31 120 33 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_2 : RectangleClaim 11 .one 12 34 120 36 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_3 : RectangleClaim 11 .one 13 37 120 39 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_4 : RectangleClaim 11 .one 14 40 120 40 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_5 : RectangleClaim 11 .one 14 41 120 41 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_6 : RectangleClaim 11 .one 14 42 117 42 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_7 : RectangleClaim 11 .one 118 42 120 42 10 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_8 : RectangleClaim 11 .one 15 43 114 43 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_9 : RectangleClaim 11 .one 115 43 120 43 10 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_10 : RectangleClaim 11 .one 15 44 111 44 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_11 : RectangleClaim 11 .one 112 44 120 44 10 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_12 : RectangleClaim 11 .one 15 45 109 45 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_13 : RectangleClaim 11 .one 110 45 120 45 10 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_14 : RectangleClaim 11 .one 16 46 106 46 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_15 : RectangleClaim 11 .one 107 46 120 46 10 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

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
  by_cases hJ3 : a.j ≤ 39
  · apply r10_3 <;> omega
  by_cases hJ4 : a.j ≤ 40
  · apply r10_4 <;> omega
  by_cases hJ5 : a.j ≤ 41
  · apply r10_5 <;> omega
  by_cases hJ6 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 117
    · apply r10_6 <;> omega
    apply r10_7 <;> omega
  by_cases hJ7 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 114
    · apply r10_8 <;> omega
    apply r10_9 <;> omega
  by_cases hJ8 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 111
    · apply r10_10 <;> omega
    apply r10_11 <;> omega
  by_cases hJ9 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 109
    · apply r10_12 <;> omega
    apply r10_13 <;> omega
  by_cases hB0 : a.b ≤ 106
  · apply r10_14 <;> omega
  apply r10_15 <;> omega

private theorem r11_0 : RectangleClaim 12 .one 11 33 120 33 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_1 : RectangleClaim 12 .one 12 34 120 36 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_2 : RectangleClaim 12 .one 13 37 120 39 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_3 : RectangleClaim 12 .one 14 40 120 40 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_4 : RectangleClaim 12 .one 14 41 120 41 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_5 : RectangleClaim 12 .one 14 42 117 42 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_6 : RectangleClaim 12 .one 118 42 120 42 11 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_7 : RectangleClaim 12 .one 15 43 114 43 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_8 : RectangleClaim 12 .one 115 43 120 43 11 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_9 : RectangleClaim 12 .one 15 44 111 44 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_10 : RectangleClaim 12 .one 112 44 120 44 11 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_11 : RectangleClaim 12 .one 15 45 109 45 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_12 : RectangleClaim 12 .one 110 45 120 45 11 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_13 : RectangleClaim 12 .one 16 46 106 46 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_14 : RectangleClaim 12 .one 107 46 120 46 11 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact11 (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 33
  · apply r11_0 <;> omega
  by_cases hJ1 : a.j ≤ 36
  · apply r11_1 <;> omega
  by_cases hJ2 : a.j ≤ 39
  · apply r11_2 <;> omega
  by_cases hJ3 : a.j ≤ 40
  · apply r11_3 <;> omega
  by_cases hJ4 : a.j ≤ 41
  · apply r11_4 <;> omega
  by_cases hJ5 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 117
    · apply r11_5 <;> omega
    apply r11_6 <;> omega
  by_cases hJ6 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 114
    · apply r11_7 <;> omega
    apply r11_8 <;> omega
  by_cases hJ7 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 111
    · apply r11_9 <;> omega
    apply r11_10 <;> omega
  by_cases hJ8 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 109
    · apply r11_11 <;> omega
    apply r11_12 <;> omega
  by_cases hB0 : a.b ≤ 106
  · apply r11_13 <;> omega
  apply r11_14 <;> omega

private theorem r12_0 : RectangleClaim 13 .one 12 36 120 36 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_1 : RectangleClaim 13 .one 13 37 120 39 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_2 : RectangleClaim 13 .one 14 40 120 40 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_3 : RectangleClaim 13 .one 14 41 120 41 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_4 : RectangleClaim 13 .one 14 42 118 42 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_5 : RectangleClaim 13 .one 119 42 120 42 12 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_6 : RectangleClaim 13 .one 15 43 115 43 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_7 : RectangleClaim 13 .one 116 43 120 43 12 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_8 : RectangleClaim 13 .one 15 44 112 44 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_9 : RectangleClaim 13 .one 113 44 120 44 12 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_10 : RectangleClaim 13 .one 15 45 109 45 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_11 : RectangleClaim 13 .one 110 45 120 45 12 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_12 : RectangleClaim 13 .one 16 46 106 46 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_13 : RectangleClaim 13 .one 107 46 120 46 12 :=
  rectangleBound (l := 60) (by decide) (by decide +kernel) (by decide +kernel)

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
  · by_cases hB0 : a.b ≤ 118
    · apply r12_4 <;> omega
    apply r12_5 <;> omega
  by_cases hJ5 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 115
    · apply r12_6 <;> omega
    apply r12_7 <;> omega
  by_cases hJ6 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 112
    · apply r12_8 <;> omega
    apply r12_9 <;> omega
  by_cases hJ7 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 109
    · apply r12_10 <;> omega
    apply r12_11 <;> omega
  by_cases hB0 : a.b ≤ 106
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
