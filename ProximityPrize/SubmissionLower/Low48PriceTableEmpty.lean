import ProximityPrize.SubmissionLower.Low48PriceTableBase

set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
namespace Low48PriceTableEmpty
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low48Price (fullCap physicalPrice)
open Low48PriceCaps (order allowance start allowance_mono)
open Low48PriceTableBase (PointClaim RectangleClaim pointBound rectangleBound)

private theorem r1_0 : RectangleClaim 1 .empty 1 3 123 3 1 :=
  rectangleBound (l := 1)

private theorem r1_1 : RectangleClaim 1 .empty 2 4 71 4 1 :=
  rectangleBound (l := 1)

private theorem r1_2 : RectangleClaim 1 .empty 72 4 123 4 1 :=
  rectangleBound (l := 2)

private theorem r1_3 : RectangleClaim 1 .empty 2 5 41 5 1 :=
  rectangleBound (l := 1)

private theorem r1_4 : RectangleClaim 1 .empty 42 5 123 5 1 :=
  rectangleBound (l := 4)

private theorem r1_5 : RectangleClaim 1 .empty 2 6 28 6 1 :=
  rectangleBound (l := 1)

private theorem r1_6 : RectangleClaim 1 .empty 29 6 123 6 1 :=
  rectangleBound (l := 5)

private theorem r1_7 : RectangleClaim 1 .empty 3 7 22 7 1 :=
  rectangleBound (l := 1)

private theorem r1_8 : RectangleClaim 1 .empty 23 7 123 7 1 :=
  rectangleBound (l := 6)

private theorem r1_9 : RectangleClaim 1 .empty 3 8 18 8 1 :=
  rectangleBound (l := 1)

private theorem r1_10 : RectangleClaim 1 .empty 19 8 123 8 1 :=
  rectangleBound (l := 8)

private theorem r1_11 : RectangleClaim 1 .empty 3 9 123 9 1 :=
  rectangleBound (l := 10)

private theorem r1_12 : RectangleClaim 1 .empty 4 10 123 12 1 :=
  rectangleBound (l := 14)

private theorem r1_13 : RectangleClaim 1 .empty 5 13 123 15 1 :=
  rectangleBound (l := 24)

private theorem r1_14 : RectangleClaim 1 .empty 6 16 123 18 1 :=
  rectangleBound (l := 30)

private theorem r1_15 : RectangleClaim 1 .empty 7 19 123 21 1 :=
  rectangleBound (l := 35)

private theorem r1_16 : RectangleClaim 1 .empty 8 22 123 24 1 :=
  rectangleBound (l := 38)

private theorem r1_17 : RectangleClaim 1 .empty 9 25 123 27 1 :=
  rectangleBound (l := 40)

private theorem r1_18 : RectangleClaim 1 .empty 10 28 123 30 1 :=
  rectangleBound (l := 42)

private theorem r1_19 : RectangleClaim 1 .empty 11 31 123 33 1 :=
  rectangleBound (l := 43)

private theorem r1_20 : RectangleClaim 1 .empty 12 34 123 36 1 :=
  rectangleBound (l := 44)

private theorem r1_21 : RectangleClaim 1 .empty 13 37 123 39 1 :=
  rectangleBound (l := 46)

private theorem r1_22 : RectangleClaim 1 .empty 14 40 123 42 1 :=
  rectangleBound (l := 46)

private theorem r1_23 : RectangleClaim 1 .empty 15 43 123 45 1 :=
  rectangleBound (l := 47)

private theorem r1_24 : RectangleClaim 1 .empty 16 46 123 48 1 :=
  rectangleBound (l := 48)

private theorem r1_25 : RectangleClaim 1 .empty 17 49 123 50 1 :=
  rectangleBound (l := 48)

private theorem exact1 (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    physicalPrice a (order .empty a) ≤ allowance 1 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 3
  · apply r1_0 <;> omega
  by_cases hJ1 : a.j ≤ 4
  · by_cases hB0 : a.b ≤ 71
    · apply r1_1 <;> omega
    apply r1_2 <;> omega
  by_cases hJ2 : a.j ≤ 5
  · by_cases hB0 : a.b ≤ 41
    · apply r1_3 <;> omega
    apply r1_4 <;> omega
  by_cases hJ3 : a.j ≤ 6
  · by_cases hB0 : a.b ≤ 28
    · apply r1_5 <;> omega
    apply r1_6 <;> omega
  by_cases hJ4 : a.j ≤ 7
  · by_cases hB0 : a.b ≤ 22
    · apply r1_7 <;> omega
    apply r1_8 <;> omega
  by_cases hJ5 : a.j ≤ 8
  · by_cases hB0 : a.b ≤ 18
    · apply r1_9 <;> omega
    apply r1_10 <;> omega
  by_cases hJ6 : a.j ≤ 9
  · apply r1_11 <;> omega
  by_cases hJ7 : a.j ≤ 12
  · apply r1_12 <;> omega
  by_cases hJ8 : a.j ≤ 15
  · apply r1_13 <;> omega
  by_cases hJ9 : a.j ≤ 18
  · apply r1_14 <;> omega
  by_cases hJ10 : a.j ≤ 21
  · apply r1_15 <;> omega
  by_cases hJ11 : a.j ≤ 24
  · apply r1_16 <;> omega
  by_cases hJ12 : a.j ≤ 27
  · apply r1_17 <;> omega
  by_cases hJ13 : a.j ≤ 30
  · apply r1_18 <;> omega
  by_cases hJ14 : a.j ≤ 33
  · apply r1_19 <;> omega
  by_cases hJ15 : a.j ≤ 36
  · apply r1_20 <;> omega
  by_cases hJ16 : a.j ≤ 39
  · apply r1_21 <;> omega
  by_cases hJ17 : a.j ≤ 42
  · apply r1_22 <;> omega
  by_cases hJ18 : a.j ≤ 45
  · apply r1_23 <;> omega
  by_cases hJ19 : a.j ≤ 48
  · apply r1_24 <;> omega
  apply r1_25 <;> omega

private theorem r2_0 : RectangleClaim 2 .empty 2 6 28 6 2 :=
  rectangleBound (l := 1)

private theorem r2_1 : RectangleClaim 2 .empty 29 6 123 6 2 :=
  rectangleBound (l := 5)

private theorem r2_2 : RectangleClaim 2 .empty 3 7 21 7 2 :=
  rectangleBound (l := 1)

private theorem r2_3 : RectangleClaim 2 .empty 22 7 123 7 2 :=
  rectangleBound (l := 6)

private theorem r2_4 : RectangleClaim 2 .empty 3 8 16 8 2 :=
  rectangleBound (l := 1)

private theorem r2_5 : RectangleClaim 2 .empty 17 8 123 8 2 :=
  rectangleBound (l := 8)

private theorem r2_6 : RectangleClaim 2 .empty 3 9 123 9 2 :=
  rectangleBound (l := 10)

private theorem r2_7 : RectangleClaim 2 .empty 4 10 123 11 2 :=
  rectangleBound (l := 14)

private theorem r2_8 : RectangleClaim 2 .empty 4 12 123 12 2 :=
  rectangleBound (l := 21)

private theorem r2_9 : RectangleClaim 2 .empty 5 13 123 15 2 :=
  rectangleBound (l := 24)

private theorem r2_10 : RectangleClaim 2 .empty 6 16 123 18 2 :=
  rectangleBound (l := 30)

private theorem r2_11 : RectangleClaim 2 .empty 7 19 123 21 2 :=
  rectangleBound (l := 35)

private theorem r2_12 : RectangleClaim 2 .empty 8 22 123 24 2 :=
  rectangleBound (l := 38)

private theorem r2_13 : RectangleClaim 2 .empty 9 25 123 27 2 :=
  rectangleBound (l := 40)

private theorem r2_14 : RectangleClaim 2 .empty 10 28 123 30 2 :=
  rectangleBound (l := 42)

private theorem r2_15 : RectangleClaim 2 .empty 11 31 123 33 2 :=
  rectangleBound (l := 43)

private theorem r2_16 : RectangleClaim 2 .empty 12 34 123 36 2 :=
  rectangleBound (l := 44)

private theorem r2_17 : RectangleClaim 2 .empty 13 37 123 39 2 :=
  rectangleBound (l := 46)

private theorem r2_18 : RectangleClaim 2 .empty 14 40 123 42 2 :=
  rectangleBound (l := 46)

private theorem r2_19 : RectangleClaim 2 .empty 15 43 123 45 2 :=
  rectangleBound (l := 47)

private theorem r2_20 : RectangleClaim 2 .empty 16 46 123 47 2 :=
  rectangleBound (l := 48)

private theorem r2_21 : RectangleClaim 2 .empty 16 48 123 48 2 :=
  rectangleBound (l := 48)

private theorem r2_22 : RectangleClaim 2 .empty 17 49 123 49 2 :=
  rectangleBound (l := 48)

private theorem r2_23 : RectangleClaim 2 .empty 17 50 123 50 2 :=
  rectangleBound (l := 48)

private theorem exact2 (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    physicalPrice a (order .empty a) ≤ allowance 2 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 6
  · by_cases hB0 : a.b ≤ 28
    · apply r2_0 <;> omega
    apply r2_1 <;> omega
  by_cases hJ1 : a.j ≤ 7
  · by_cases hB0 : a.b ≤ 21
    · apply r2_2 <;> omega
    apply r2_3 <;> omega
  by_cases hJ2 : a.j ≤ 8
  · by_cases hB0 : a.b ≤ 16
    · apply r2_4 <;> omega
    apply r2_5 <;> omega
  by_cases hJ3 : a.j ≤ 9
  · apply r2_6 <;> omega
  by_cases hJ4 : a.j ≤ 11
  · apply r2_7 <;> omega
  by_cases hJ5 : a.j ≤ 12
  · apply r2_8 <;> omega
  by_cases hJ6 : a.j ≤ 15
  · apply r2_9 <;> omega
  by_cases hJ7 : a.j ≤ 18
  · apply r2_10 <;> omega
  by_cases hJ8 : a.j ≤ 21
  · apply r2_11 <;> omega
  by_cases hJ9 : a.j ≤ 24
  · apply r2_12 <;> omega
  by_cases hJ10 : a.j ≤ 27
  · apply r2_13 <;> omega
  by_cases hJ11 : a.j ≤ 30
  · apply r2_14 <;> omega
  by_cases hJ12 : a.j ≤ 33
  · apply r2_15 <;> omega
  by_cases hJ13 : a.j ≤ 36
  · apply r2_16 <;> omega
  by_cases hJ14 : a.j ≤ 39
  · apply r2_17 <;> omega
  by_cases hJ15 : a.j ≤ 42
  · apply r2_18 <;> omega
  by_cases hJ16 : a.j ≤ 45
  · apply r2_19 <;> omega
  by_cases hJ17 : a.j ≤ 47
  · apply r2_20 <;> omega
  by_cases hJ18 : a.j ≤ 48
  · apply r2_21 <;> omega
  by_cases hJ19 : a.j ≤ 49
  · apply r2_22 <;> omega
  apply r2_23 <;> omega

private theorem r3_0 : RectangleClaim 3 .empty 3 9 123 9 3 :=
  rectangleBound (l := 10)

private theorem r3_1 : RectangleClaim 3 .empty 4 10 123 11 3 :=
  rectangleBound (l := 14)

private theorem r3_2 : RectangleClaim 3 .empty 4 12 123 12 3 :=
  rectangleBound (l := 21)

private theorem r3_3 : RectangleClaim 3 .empty 5 13 123 15 3 :=
  rectangleBound (l := 24)

private theorem r3_4 : RectangleClaim 3 .empty 6 16 123 18 3 :=
  rectangleBound (l := 30)

private theorem r3_5 : RectangleClaim 3 .empty 7 19 123 21 3 :=
  rectangleBound (l := 35)

private theorem r3_6 : RectangleClaim 3 .empty 8 22 123 24 3 :=
  rectangleBound (l := 38)

private theorem r3_7 : RectangleClaim 3 .empty 9 25 123 27 3 :=
  rectangleBound (l := 40)

private theorem r3_8 : RectangleClaim 3 .empty 10 28 123 30 3 :=
  rectangleBound (l := 42)

private theorem r3_9 : RectangleClaim 3 .empty 11 31 123 33 3 :=
  rectangleBound (l := 43)

private theorem r3_10 : RectangleClaim 3 .empty 12 34 123 36 3 :=
  rectangleBound (l := 44)

private theorem r3_11 : RectangleClaim 3 .empty 13 37 123 39 3 :=
  rectangleBound (l := 46)

private theorem r3_12 : RectangleClaim 3 .empty 14 40 123 42 3 :=
  rectangleBound (l := 46)

private theorem r3_13 : RectangleClaim 3 .empty 15 43 123 44 3 :=
  rectangleBound (l := 47)

private theorem r3_14 : RectangleClaim 3 .empty 15 45 123 45 3 :=
  rectangleBound (l := 48)

private theorem r3_15 : RectangleClaim 3 .empty 16 46 123 47 3 :=
  rectangleBound (l := 48)

private theorem r3_16 : RectangleClaim 3 .empty 16 48 123 48 3 :=
  rectangleBound (l := 48)

private theorem r3_17 : RectangleClaim 3 .empty 17 49 122 49 3 :=
  rectangleBound (l := 48)

private theorem r3_18 : RectangleClaim 3 .empty 123 49 123 49 3 :=
  rectangleBound (l := 50)

private theorem r3_19 : RectangleClaim 3 .empty 17 50 120 50 3 :=
  rectangleBound (l := 48)

private theorem r3_20 : RectangleClaim 3 .empty 121 50 123 50 3 :=
  rectangleBound (l := 51)

private theorem exact3 (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    physicalPrice a (order .empty a) ≤ allowance 3 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 9
  · apply r3_0 <;> omega
  by_cases hJ1 : a.j ≤ 11
  · apply r3_1 <;> omega
  by_cases hJ2 : a.j ≤ 12
  · apply r3_2 <;> omega
  by_cases hJ3 : a.j ≤ 15
  · apply r3_3 <;> omega
  by_cases hJ4 : a.j ≤ 18
  · apply r3_4 <;> omega
  by_cases hJ5 : a.j ≤ 21
  · apply r3_5 <;> omega
  by_cases hJ6 : a.j ≤ 24
  · apply r3_6 <;> omega
  by_cases hJ7 : a.j ≤ 27
  · apply r3_7 <;> omega
  by_cases hJ8 : a.j ≤ 30
  · apply r3_8 <;> omega
  by_cases hJ9 : a.j ≤ 33
  · apply r3_9 <;> omega
  by_cases hJ10 : a.j ≤ 36
  · apply r3_10 <;> omega
  by_cases hJ11 : a.j ≤ 39
  · apply r3_11 <;> omega
  by_cases hJ12 : a.j ≤ 42
  · apply r3_12 <;> omega
  by_cases hJ13 : a.j ≤ 44
  · apply r3_13 <;> omega
  by_cases hJ14 : a.j ≤ 45
  · apply r3_14 <;> omega
  by_cases hJ15 : a.j ≤ 47
  · apply r3_15 <;> omega
  by_cases hJ16 : a.j ≤ 48
  · apply r3_16 <;> omega
  by_cases hJ17 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 122
    · apply r3_17 <;> omega
    apply r3_18 <;> omega
  by_cases hB0 : a.b ≤ 120
  · apply r3_19 <;> omega
  apply r3_20 <;> omega

private theorem r4_0 : RectangleClaim 4 .empty 4 12 123 12 4 :=
  rectangleBound (l := 21)

private theorem r4_1 : RectangleClaim 4 .empty 5 13 123 15 4 :=
  rectangleBound (l := 24)

private theorem r4_2 : RectangleClaim 4 .empty 6 16 123 18 4 :=
  rectangleBound (l := 30)

private theorem r4_3 : RectangleClaim 4 .empty 7 19 123 21 4 :=
  rectangleBound (l := 35)

private theorem r4_4 : RectangleClaim 4 .empty 8 22 123 24 4 :=
  rectangleBound (l := 38)

private theorem r4_5 : RectangleClaim 4 .empty 9 25 123 27 4 :=
  rectangleBound (l := 40)

private theorem r4_6 : RectangleClaim 4 .empty 10 28 123 30 4 :=
  rectangleBound (l := 42)

private theorem r4_7 : RectangleClaim 4 .empty 11 31 123 33 4 :=
  rectangleBound (l := 43)

private theorem r4_8 : RectangleClaim 4 .empty 12 34 123 36 4 :=
  rectangleBound (l := 44)

private theorem r4_9 : RectangleClaim 4 .empty 13 37 123 39 4 :=
  rectangleBound (l := 46)

private theorem r4_10 : RectangleClaim 4 .empty 14 40 123 42 4 :=
  rectangleBound (l := 46)

private theorem r4_11 : RectangleClaim 4 .empty 15 43 123 44 4 :=
  rectangleBound (l := 47)

private theorem r4_12 : RectangleClaim 4 .empty 15 45 123 45 4 :=
  rectangleBound (l := 48)

private theorem r4_13 : RectangleClaim 4 .empty 16 46 123 46 4 :=
  rectangleBound (l := 48)

private theorem r4_14 : RectangleClaim 4 .empty 16 47 123 47 4 :=
  rectangleBound (l := 48)

private theorem r4_15 : RectangleClaim 4 .empty 16 48 121 48 4 :=
  rectangleBound (l := 48)

private theorem r4_16 : RectangleClaim 4 .empty 122 48 123 48 4 :=
  rectangleBound (l := 50)

private theorem r4_17 : RectangleClaim 4 .empty 17 49 119 49 4 :=
  rectangleBound (l := 48)

private theorem r4_18 : RectangleClaim 4 .empty 120 49 123 49 4 :=
  rectangleBound (l := 50)

private theorem r4_19 : RectangleClaim 4 .empty 17 50 117 50 4 :=
  rectangleBound (l := 48)

private theorem r4_20 : RectangleClaim 4 .empty 118 50 122 50 4 :=
  rectangleBound (l := 50)

private theorem r4_21 : RectangleClaim 4 .empty 123 50 123 50 4 :=
  rectangleBound (l := 51)

private theorem exact4 (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
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
  by_cases hJ10 : a.j ≤ 42
  · apply r4_10 <;> omega
  by_cases hJ11 : a.j ≤ 44
  · apply r4_11 <;> omega
  by_cases hJ12 : a.j ≤ 45
  · apply r4_12 <;> omega
  by_cases hJ13 : a.j ≤ 46
  · apply r4_13 <;> omega
  by_cases hJ14 : a.j ≤ 47
  · apply r4_14 <;> omega
  by_cases hJ15 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 121
    · apply r4_15 <;> omega
    apply r4_16 <;> omega
  by_cases hJ16 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 119
    · apply r4_17 <;> omega
    apply r4_18 <;> omega
  by_cases hB0 : a.b ≤ 117
  · apply r4_19 <;> omega
  by_cases hB1 : a.b ≤ 122
  · apply r4_20 <;> omega
  apply r4_21 <;> omega

private theorem r5_0 : RectangleClaim 5 .empty 5 15 123 15 5 :=
  rectangleBound (l := 29)

private theorem r5_1 : RectangleClaim 5 .empty 6 16 123 18 5 :=
  rectangleBound (l := 30)

private theorem r5_2 : RectangleClaim 5 .empty 7 19 123 21 5 :=
  rectangleBound (l := 35)

private theorem r5_3 : RectangleClaim 5 .empty 8 22 123 24 5 :=
  rectangleBound (l := 38)

private theorem r5_4 : RectangleClaim 5 .empty 9 25 123 27 5 :=
  rectangleBound (l := 40)

private theorem r5_5 : RectangleClaim 5 .empty 10 28 123 30 5 :=
  rectangleBound (l := 42)

private theorem r5_6 : RectangleClaim 5 .empty 11 31 123 33 5 :=
  rectangleBound (l := 43)

private theorem r5_7 : RectangleClaim 5 .empty 12 34 123 36 5 :=
  rectangleBound (l := 44)

private theorem r5_8 : RectangleClaim 5 .empty 13 37 123 39 5 :=
  rectangleBound (l := 46)

private theorem r5_9 : RectangleClaim 5 .empty 14 40 123 42 5 :=
  rectangleBound (l := 46)

private theorem r5_10 : RectangleClaim 5 .empty 15 43 123 44 5 :=
  rectangleBound (l := 47)

private theorem r5_11 : RectangleClaim 5 .empty 15 45 123 45 5 :=
  rectangleBound (l := 48)

private theorem r5_12 : RectangleClaim 5 .empty 16 46 123 46 5 :=
  rectangleBound (l := 48)

private theorem r5_13 : RectangleClaim 5 .empty 16 47 121 47 5 :=
  rectangleBound (l := 48)

private theorem r5_14 : RectangleClaim 5 .empty 122 47 123 47 5 :=
  rectangleBound (l := 50)

private theorem r5_15 : RectangleClaim 5 .empty 16 48 119 48 5 :=
  rectangleBound (l := 48)

private theorem r5_16 : RectangleClaim 5 .empty 120 48 123 48 5 :=
  rectangleBound (l := 50)

private theorem r5_17 : RectangleClaim 5 .empty 17 49 117 49 5 :=
  rectangleBound (l := 48)

private theorem r5_18 : RectangleClaim 5 .empty 118 49 121 49 5 :=
  rectangleBound (l := 50)

private theorem r5_19 : PointClaim 5 .empty 122 49 5 :=
  pointBound (l := 50)

private theorem r5_20 : PointClaim 5 .empty 123 49 5 :=
  pointBound (l := 50)

private theorem r5_21 : RectangleClaim 5 .empty 17 50 115 50 5 :=
  rectangleBound (l := 48)

private theorem r5_22 : RectangleClaim 5 .empty 116 50 119 50 5 :=
  rectangleBound (l := 50)

private theorem r5_23 : RectangleClaim 5 .empty 120 50 122 50 5 :=
  rectangleBound (l := 51)

private theorem r5_24 : PointClaim 5 .empty 123 50 5 :=
  pointBound (l := 51)

private theorem exact5 (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
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
  by_cases hJ8 : a.j ≤ 39
  · apply r5_8 <;> omega
  by_cases hJ9 : a.j ≤ 42
  · apply r5_9 <;> omega
  by_cases hJ10 : a.j ≤ 44
  · apply r5_10 <;> omega
  by_cases hJ11 : a.j ≤ 45
  · apply r5_11 <;> omega
  by_cases hJ12 : a.j ≤ 46
  · apply r5_12 <;> omega
  by_cases hJ13 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 121
    · apply r5_13 <;> omega
    apply r5_14 <;> omega
  by_cases hJ14 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 119
    · apply r5_15 <;> omega
    apply r5_16 <;> omega
  by_cases hJ15 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 117
    · apply r5_17 <;> omega
    by_cases hB1 : a.b ≤ 121
    · apply r5_18 <;> omega
    by_cases hB2 : a.b ≤ 122
    · apply r5_19 <;> omega
    apply r5_20 <;> omega
  by_cases hB0 : a.b ≤ 115
  · apply r5_21 <;> omega
  by_cases hB1 : a.b ≤ 119
  · apply r5_22 <;> omega
  by_cases hB2 : a.b ≤ 122
  · apply r5_23 <;> omega
  apply r5_24 <;> omega

private theorem r6_0 : RectangleClaim 6 .empty 6 18 123 18 6 :=
  rectangleBound (l := 33)

private theorem r6_1 : RectangleClaim 6 .empty 7 19 123 21 6 :=
  rectangleBound (l := 35)

private theorem r6_2 : RectangleClaim 6 .empty 8 22 123 24 6 :=
  rectangleBound (l := 38)

private theorem r6_3 : RectangleClaim 6 .empty 9 25 123 27 6 :=
  rectangleBound (l := 40)

private theorem r6_4 : RectangleClaim 6 .empty 10 28 123 30 6 :=
  rectangleBound (l := 42)

private theorem r6_5 : RectangleClaim 6 .empty 11 31 123 33 6 :=
  rectangleBound (l := 43)

private theorem r6_6 : RectangleClaim 6 .empty 12 34 123 36 6 :=
  rectangleBound (l := 44)

private theorem r6_7 : RectangleClaim 6 .empty 13 37 123 39 6 :=
  rectangleBound (l := 46)

private theorem r6_8 : RectangleClaim 6 .empty 14 40 123 41 6 :=
  rectangleBound (l := 46)

private theorem r6_9 : RectangleClaim 6 .empty 14 42 123 42 6 :=
  rectangleBound (l := 47)

private theorem r6_10 : RectangleClaim 6 .empty 15 43 123 43 6 :=
  rectangleBound (l := 47)

private theorem r6_11 : RectangleClaim 6 .empty 15 44 123 44 6 :=
  rectangleBound (l := 48)

private theorem r6_12 : RectangleClaim 6 .empty 15 45 123 45 6 :=
  rectangleBound (l := 48)

private theorem r6_13 : RectangleClaim 6 .empty 16 46 122 46 6 :=
  rectangleBound (l := 48)

private theorem r6_14 : RectangleClaim 6 .empty 123 46 123 46 6 :=
  rectangleBound (l := 50)

private theorem r6_15 : RectangleClaim 6 .empty 16 47 119 47 6 :=
  rectangleBound (l := 48)

private theorem r6_16 : RectangleClaim 6 .empty 120 47 123 47 6 :=
  rectangleBound (l := 50)

private theorem r6_17 : RectangleClaim 6 .empty 16 48 117 48 6 :=
  rectangleBound (l := 48)

private theorem r6_18 : RectangleClaim 6 .empty 118 48 122 48 6 :=
  rectangleBound (l := 50)

private theorem r6_19 : PointClaim 6 .empty 123 48 6 :=
  pointBound (l := 50)

private theorem r6_20 : RectangleClaim 6 .empty 17 49 115 49 6 :=
  rectangleBound (l := 48)

private theorem r6_21 : RectangleClaim 6 .empty 116 49 120 49 6 :=
  rectangleBound (l := 50)

private theorem r6_22 : PointClaim 6 .empty 121 49 6 :=
  pointBound (l := 50)

private theorem r6_23 : PointClaim 6 .empty 122 49 6 :=
  pointBound (l := 50)

private theorem r6_24 : PointClaim 6 .empty 123 49 6 :=
  pointBound (l := 50)

private theorem r6_25 : RectangleClaim 6 .empty 17 50 113 50 6 :=
  rectangleBound (l := 48)

private theorem r6_26 : RectangleClaim 6 .empty 114 50 117 50 6 :=
  rectangleBound (l := 50)

private theorem r6_27 : PointClaim 6 .empty 118 50 6 :=
  pointBound (l := 50)

private theorem r6_28 : RectangleClaim 6 .empty 119 50 120 50 6 :=
  rectangleBound (l := 51)

private theorem r6_29 : PointClaim 6 .empty 121 50 6 :=
  pointBound (l := 51)

private theorem r6_30 : PointClaim 6 .empty 122 50 6 :=
  pointBound (l := 51)

private theorem r6_31 : PointClaim 6 .empty 123 50 6 :=
  pointBound (l := 51)

private theorem exact6 (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
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
  by_cases hJ7 : a.j ≤ 39
  · apply r6_7 <;> omega
  by_cases hJ8 : a.j ≤ 41
  · apply r6_8 <;> omega
  by_cases hJ9 : a.j ≤ 42
  · apply r6_9 <;> omega
  by_cases hJ10 : a.j ≤ 43
  · apply r6_10 <;> omega
  by_cases hJ11 : a.j ≤ 44
  · apply r6_11 <;> omega
  by_cases hJ12 : a.j ≤ 45
  · apply r6_12 <;> omega
  by_cases hJ13 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 122
    · apply r6_13 <;> omega
    apply r6_14 <;> omega
  by_cases hJ14 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 119
    · apply r6_15 <;> omega
    apply r6_16 <;> omega
  by_cases hJ15 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 117
    · apply r6_17 <;> omega
    by_cases hB1 : a.b ≤ 122
    · apply r6_18 <;> omega
    apply r6_19 <;> omega
  by_cases hJ16 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 115
    · apply r6_20 <;> omega
    by_cases hB1 : a.b ≤ 120
    · apply r6_21 <;> omega
    by_cases hB2 : a.b ≤ 121
    · apply r6_22 <;> omega
    by_cases hB3 : a.b ≤ 122
    · apply r6_23 <;> omega
    apply r6_24 <;> omega
  by_cases hB0 : a.b ≤ 113
  · apply r6_25 <;> omega
  by_cases hB1 : a.b ≤ 117
  · apply r6_26 <;> omega
  by_cases hB2 : a.b ≤ 118
  · apply r6_27 <;> omega
  by_cases hB3 : a.b ≤ 120
  · apply r6_28 <;> omega
  by_cases hB4 : a.b ≤ 121
  · apply r6_29 <;> omega
  by_cases hB5 : a.b ≤ 122
  · apply r6_30 <;> omega
  apply r6_31 <;> omega

private theorem r7_0 : RectangleClaim 7 .empty 7 21 123 21 7 :=
  rectangleBound (l := 37)

private theorem r7_1 : RectangleClaim 7 .empty 8 22 123 24 7 :=
  rectangleBound (l := 38)

private theorem r7_2 : RectangleClaim 7 .empty 9 25 123 27 7 :=
  rectangleBound (l := 40)

private theorem r7_3 : RectangleClaim 7 .empty 10 28 123 30 7 :=
  rectangleBound (l := 42)

private theorem r7_4 : RectangleClaim 7 .empty 11 31 123 33 7 :=
  rectangleBound (l := 43)

private theorem r7_5 : RectangleClaim 7 .empty 12 34 123 36 7 :=
  rectangleBound (l := 44)

private theorem r7_6 : RectangleClaim 7 .empty 13 37 123 39 7 :=
  rectangleBound (l := 46)

private theorem r7_7 : RectangleClaim 7 .empty 14 40 123 41 7 :=
  rectangleBound (l := 46)

private theorem r7_8 : RectangleClaim 7 .empty 14 42 123 42 7 :=
  rectangleBound (l := 47)

private theorem r7_9 : RectangleClaim 7 .empty 15 43 123 43 7 :=
  rectangleBound (l := 47)

private theorem r7_10 : RectangleClaim 7 .empty 15 44 123 44 7 :=
  rectangleBound (l := 48)

private theorem r7_11 : RectangleClaim 7 .empty 15 45 123 45 7 :=
  rectangleBound (l := 48)

private theorem r7_12 : RectangleClaim 7 .empty 16 46 121 46 7 :=
  rectangleBound (l := 48)

private theorem r7_13 : RectangleClaim 7 .empty 122 46 123 46 7 :=
  rectangleBound (l := 50)

private theorem r7_14 : RectangleClaim 7 .empty 16 47 118 47 7 :=
  rectangleBound (l := 48)

private theorem r7_15 : RectangleClaim 7 .empty 119 47 123 47 7 :=
  rectangleBound (l := 50)

private theorem r7_16 : RectangleClaim 7 .empty 16 48 116 48 7 :=
  rectangleBound (l := 48)

private theorem r7_17 : RectangleClaim 7 .empty 117 48 121 48 7 :=
  rectangleBound (l := 50)

private theorem r7_18 : PointClaim 7 .empty 122 48 7 :=
  pointBound (l := 50)

private theorem r7_19 : PointClaim 7 .empty 123 48 7 :=
  pointBound (l := 50)

private theorem r7_20 : RectangleClaim 7 .empty 17 49 113 49 7 :=
  rectangleBound (l := 48)

private theorem r7_21 : RectangleClaim 7 .empty 114 49 118 49 7 :=
  rectangleBound (l := 50)

private theorem r7_22 : PointClaim 7 .empty 119 49 7 :=
  pointBound (l := 50)

private theorem r7_23 : PointClaim 7 .empty 120 49 7 :=
  pointBound (l := 50)

private theorem r7_24 : PointClaim 7 .empty 121 49 7 :=
  pointBound (l := 50)

private theorem r7_25 : PointClaim 7 .empty 122 49 7 :=
  pointBound (l := 50)

private theorem r7_26 : PointClaim 7 .empty 123 49 7 :=
  pointBound (l := 50)

private theorem r7_27 : RectangleClaim 7 .empty 17 50 111 50 7 :=
  rectangleBound (l := 48)

private theorem r7_28 : RectangleClaim 7 .empty 112 50 116 50 7 :=
  rectangleBound (l := 50)

private theorem r7_29 : PointClaim 7 .empty 117 50 7 :=
  pointBound (l := 50)

private theorem r7_30 : PointClaim 7 .empty 118 50 7 :=
  pointBound (l := 50)

private theorem r7_31 : PointClaim 7 .empty 119 50 7 :=
  pointBound (l := 51)

private theorem r7_32 : PointClaim 7 .empty 120 50 7 :=
  pointBound (l := 51)

private theorem r7_33 : PointClaim 7 .empty 121 50 7 :=
  pointBound (l := 51)

private theorem r7_34 : PointClaim 7 .empty 122 50 7 :=
  pointBound (l := 51)

private theorem r7_35 : PointClaim 7 .empty 123 50 7 :=
  pointBound (l := 51)

private theorem exact7 (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
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
  by_cases hJ6 : a.j ≤ 39
  · apply r7_6 <;> omega
  by_cases hJ7 : a.j ≤ 41
  · apply r7_7 <;> omega
  by_cases hJ8 : a.j ≤ 42
  · apply r7_8 <;> omega
  by_cases hJ9 : a.j ≤ 43
  · apply r7_9 <;> omega
  by_cases hJ10 : a.j ≤ 44
  · apply r7_10 <;> omega
  by_cases hJ11 : a.j ≤ 45
  · apply r7_11 <;> omega
  by_cases hJ12 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 121
    · apply r7_12 <;> omega
    apply r7_13 <;> omega
  by_cases hJ13 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 118
    · apply r7_14 <;> omega
    apply r7_15 <;> omega
  by_cases hJ14 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 116
    · apply r7_16 <;> omega
    by_cases hB1 : a.b ≤ 121
    · apply r7_17 <;> omega
    by_cases hB2 : a.b ≤ 122
    · apply r7_18 <;> omega
    apply r7_19 <;> omega
  by_cases hJ15 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 113
    · apply r7_20 <;> omega
    by_cases hB1 : a.b ≤ 118
    · apply r7_21 <;> omega
    by_cases hB2 : a.b ≤ 119
    · apply r7_22 <;> omega
    by_cases hB3 : a.b ≤ 120
    · apply r7_23 <;> omega
    by_cases hB4 : a.b ≤ 121
    · apply r7_24 <;> omega
    by_cases hB5 : a.b ≤ 122
    · apply r7_25 <;> omega
    apply r7_26 <;> omega
  by_cases hB0 : a.b ≤ 111
  · apply r7_27 <;> omega
  by_cases hB1 : a.b ≤ 116
  · apply r7_28 <;> omega
  by_cases hB2 : a.b ≤ 117
  · apply r7_29 <;> omega
  by_cases hB3 : a.b ≤ 118
  · apply r7_30 <;> omega
  by_cases hB4 : a.b ≤ 119
  · apply r7_31 <;> omega
  by_cases hB5 : a.b ≤ 120
  · apply r7_32 <;> omega
  by_cases hB6 : a.b ≤ 121
  · apply r7_33 <;> omega
  by_cases hB7 : a.b ≤ 122
  · apply r7_34 <;> omega
  apply r7_35 <;> omega

private theorem r8_0 : RectangleClaim 8 .empty 8 24 123 24 8 :=
  rectangleBound (l := 39)

private theorem r8_1 : RectangleClaim 8 .empty 9 25 123 27 8 :=
  rectangleBound (l := 40)

private theorem r8_2 : RectangleClaim 8 .empty 10 28 123 30 8 :=
  rectangleBound (l := 42)

private theorem r8_3 : RectangleClaim 8 .empty 11 31 123 33 8 :=
  rectangleBound (l := 43)

private theorem r8_4 : RectangleClaim 8 .empty 12 34 123 36 8 :=
  rectangleBound (l := 44)

private theorem r8_5 : RectangleClaim 8 .empty 13 37 123 39 8 :=
  rectangleBound (l := 46)

private theorem r8_6 : RectangleClaim 8 .empty 14 40 123 41 8 :=
  rectangleBound (l := 46)

private theorem r8_7 : RectangleClaim 8 .empty 14 42 123 42 8 :=
  rectangleBound (l := 47)

private theorem r8_8 : RectangleClaim 8 .empty 15 43 123 43 8 :=
  rectangleBound (l := 47)

private theorem r8_9 : RectangleClaim 8 .empty 15 44 123 44 8 :=
  rectangleBound (l := 48)

private theorem r8_10 : RectangleClaim 8 .empty 15 45 122 45 8 :=
  rectangleBound (l := 48)

private theorem r8_11 : RectangleClaim 8 .empty 123 45 123 45 8 :=
  rectangleBound (l := 49)

private theorem r8_12 : RectangleClaim 8 .empty 16 46 120 46 8 :=
  rectangleBound (l := 48)

private theorem r8_13 : RectangleClaim 8 .empty 121 46 123 46 8 :=
  rectangleBound (l := 50)

private theorem r8_14 : RectangleClaim 8 .empty 16 47 117 47 8 :=
  rectangleBound (l := 48)

private theorem r8_15 : RectangleClaim 8 .empty 118 47 122 47 8 :=
  rectangleBound (l := 50)

private theorem r8_16 : PointClaim 8 .empty 123 47 8 :=
  pointBound (l := 50)

private theorem r8_17 : RectangleClaim 8 .empty 16 48 115 48 8 :=
  rectangleBound (l := 48)

private theorem r8_18 : RectangleClaim 8 .empty 116 48 120 48 8 :=
  rectangleBound (l := 50)

private theorem r8_19 : PointClaim 8 .empty 121 48 8 :=
  pointBound (l := 50)

private theorem r8_20 : PointClaim 8 .empty 122 48 8 :=
  pointBound (l := 50)

private theorem r8_21 : PointClaim 8 .empty 123 48 8 :=
  pointBound (l := 50)

private theorem r8_22 : RectangleClaim 8 .empty 17 49 112 49 8 :=
  rectangleBound (l := 48)

private theorem r8_23 : RectangleClaim 8 .empty 113 49 117 49 8 :=
  rectangleBound (l := 50)

private theorem r8_24 : PointClaim 8 .empty 118 49 8 :=
  pointBound (l := 50)

private theorem r8_25 : PointClaim 8 .empty 119 49 8 :=
  pointBound (l := 50)

private theorem r8_26 : PointClaim 8 .empty 120 49 8 :=
  pointBound (l := 50)

private theorem r8_27 : PointClaim 8 .empty 121 49 8 :=
  pointBound (l := 50)

private theorem r8_28 : PointClaim 8 .empty 122 49 8 :=
  pointBound (l := 50)

private theorem r8_29 : PointClaim 8 .empty 123 49 8 :=
  pointBound (l := 50)

private theorem r8_30 : RectangleClaim 8 .empty 17 50 110 50 8 :=
  rectangleBound (l := 48)

private theorem r8_31 : RectangleClaim 8 .empty 111 50 115 50 8 :=
  rectangleBound (l := 50)

private theorem r8_32 : PointClaim 8 .empty 116 50 8 :=
  pointBound (l := 50)

private theorem r8_33 : PointClaim 8 .empty 117 50 8 :=
  pointBound (l := 50)

private theorem r8_34 : PointClaim 8 .empty 118 50 8 :=
  pointBound (l := 50)

private theorem r8_35 : PointClaim 8 .empty 119 50 8 :=
  pointBound (l := 51)

private theorem r8_36 : PointClaim 8 .empty 120 50 8 :=
  pointBound (l := 51)

private theorem r8_37 : PointClaim 8 .empty 121 50 8 :=
  pointBound (l := 51)

private theorem r8_38 : PointClaim 8 .empty 122 50 8 :=
  pointBound (l := 51)

private theorem r8_39 : PointClaim 8 .empty 123 50 8 :=
  pointBound (l := 51)

private theorem exact8 (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
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
  by_cases hJ5 : a.j ≤ 39
  · apply r8_5 <;> omega
  by_cases hJ6 : a.j ≤ 41
  · apply r8_6 <;> omega
  by_cases hJ7 : a.j ≤ 42
  · apply r8_7 <;> omega
  by_cases hJ8 : a.j ≤ 43
  · apply r8_8 <;> omega
  by_cases hJ9 : a.j ≤ 44
  · apply r8_9 <;> omega
  by_cases hJ10 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 122
    · apply r8_10 <;> omega
    apply r8_11 <;> omega
  by_cases hJ11 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 120
    · apply r8_12 <;> omega
    apply r8_13 <;> omega
  by_cases hJ12 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 117
    · apply r8_14 <;> omega
    by_cases hB1 : a.b ≤ 122
    · apply r8_15 <;> omega
    apply r8_16 <;> omega
  by_cases hJ13 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 115
    · apply r8_17 <;> omega
    by_cases hB1 : a.b ≤ 120
    · apply r8_18 <;> omega
    by_cases hB2 : a.b ≤ 121
    · apply r8_19 <;> omega
    by_cases hB3 : a.b ≤ 122
    · apply r8_20 <;> omega
    apply r8_21 <;> omega
  by_cases hJ14 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 112
    · apply r8_22 <;> omega
    by_cases hB1 : a.b ≤ 117
    · apply r8_23 <;> omega
    by_cases hB2 : a.b ≤ 118
    · apply r8_24 <;> omega
    by_cases hB3 : a.b ≤ 119
    · apply r8_25 <;> omega
    by_cases hB4 : a.b ≤ 120
    · apply r8_26 <;> omega
    by_cases hB5 : a.b ≤ 121
    · apply r8_27 <;> omega
    by_cases hB6 : a.b ≤ 122
    · apply r8_28 <;> omega
    apply r8_29 <;> omega
  by_cases hB0 : a.b ≤ 110
  · apply r8_30 <;> omega
  by_cases hB1 : a.b ≤ 115
  · apply r8_31 <;> omega
  by_cases hB2 : a.b ≤ 116
  · apply r8_32 <;> omega
  by_cases hB3 : a.b ≤ 117
  · apply r8_33 <;> omega
  by_cases hB4 : a.b ≤ 118
  · apply r8_34 <;> omega
  by_cases hB5 : a.b ≤ 119
  · apply r8_35 <;> omega
  by_cases hB6 : a.b ≤ 120
  · apply r8_36 <;> omega
  by_cases hB7 : a.b ≤ 121
  · apply r8_37 <;> omega
  by_cases hB8 : a.b ≤ 122
  · apply r8_38 <;> omega
  apply r8_39 <;> omega

private theorem r9_0 : RectangleClaim 9 .empty 9 27 123 27 9 :=
  rectangleBound (l := 41)

private theorem r9_1 : RectangleClaim 9 .empty 10 28 123 30 9 :=
  rectangleBound (l := 42)

private theorem r9_2 : RectangleClaim 9 .empty 11 31 123 33 9 :=
  rectangleBound (l := 43)

private theorem r9_3 : RectangleClaim 9 .empty 12 34 123 36 9 :=
  rectangleBound (l := 44)

private theorem r9_4 : RectangleClaim 9 .empty 13 37 123 39 9 :=
  rectangleBound (l := 46)

private theorem r9_5 : RectangleClaim 9 .empty 14 40 123 41 9 :=
  rectangleBound (l := 46)

private theorem r9_6 : RectangleClaim 9 .empty 14 42 123 42 9 :=
  rectangleBound (l := 47)

private theorem r9_7 : RectangleClaim 9 .empty 15 43 123 43 9 :=
  rectangleBound (l := 47)

private theorem r9_8 : RectangleClaim 9 .empty 15 44 123 44 9 :=
  rectangleBound (l := 48)

private theorem r9_9 : RectangleClaim 9 .empty 15 45 122 45 9 :=
  rectangleBound (l := 48)

private theorem r9_10 : RectangleClaim 9 .empty 123 45 123 45 9 :=
  rectangleBound (l := 49)

private theorem r9_11 : RectangleClaim 9 .empty 16 46 119 46 9 :=
  rectangleBound (l := 48)

private theorem r9_12 : RectangleClaim 9 .empty 120 46 123 46 9 :=
  rectangleBound (l := 50)

private theorem r9_13 : RectangleClaim 9 .empty 16 47 116 47 9 :=
  rectangleBound (l := 48)

private theorem r9_14 : RectangleClaim 9 .empty 117 47 122 47 9 :=
  rectangleBound (l := 50)

private theorem r9_15 : PointClaim 9 .empty 123 47 9 :=
  pointBound (l := 50)

private theorem r9_16 : RectangleClaim 9 .empty 16 48 114 48 9 :=
  rectangleBound (l := 48)

private theorem r9_17 : RectangleClaim 9 .empty 115 48 119 48 9 :=
  rectangleBound (l := 50)

private theorem r9_18 : PointClaim 9 .empty 120 48 9 :=
  pointBound (l := 50)

private theorem r9_19 : PointClaim 9 .empty 121 48 9 :=
  pointBound (l := 50)

private theorem r9_20 : PointClaim 9 .empty 122 48 9 :=
  pointBound (l := 50)

private theorem r9_21 : PointClaim 9 .empty 123 48 9 :=
  pointBound (l := 50)

private theorem r9_22 : RectangleClaim 9 .empty 17 49 111 49 9 :=
  rectangleBound (l := 48)

private theorem r9_23 : RectangleClaim 9 .empty 112 49 116 49 9 :=
  rectangleBound (l := 50)

private theorem r9_24 : PointClaim 9 .empty 117 49 9 :=
  pointBound (l := 50)

private theorem r9_25 : PointClaim 9 .empty 118 49 9 :=
  pointBound (l := 50)

private theorem r9_26 : PointClaim 9 .empty 119 49 9 :=
  pointBound (l := 50)

private theorem r9_27 : PointClaim 9 .empty 120 49 9 :=
  pointBound (l := 50)

private theorem r9_28 : PointClaim 9 .empty 121 49 9 :=
  pointBound (l := 50)

private theorem r9_29 : PointClaim 9 .empty 122 49 9 :=
  pointBound (l := 50)

private theorem r9_30 : PointClaim 9 .empty 123 49 9 :=
  pointBound (l := 50)

private theorem r9_31 : RectangleClaim 9 .empty 17 50 109 50 9 :=
  rectangleBound (l := 48)

private theorem r9_32 : RectangleClaim 9 .empty 110 50 114 50 9 :=
  rectangleBound (l := 50)

private theorem r9_33 : PointClaim 9 .empty 115 50 9 :=
  pointBound (l := 50)

private theorem r9_34 : PointClaim 9 .empty 116 50 9 :=
  pointBound (l := 50)

private theorem r9_35 : PointClaim 9 .empty 117 50 9 :=
  pointBound (l := 50)

private theorem r9_36 : PointClaim 9 .empty 118 50 9 :=
  pointBound (l := 50)

private theorem r9_37 : PointClaim 9 .empty 119 50 9 :=
  pointBound (l := 51)

private theorem r9_38 : PointClaim 9 .empty 120 50 9 :=
  pointBound (l := 51)

private theorem r9_39 : PointClaim 9 .empty 121 50 9 :=
  pointBound (l := 51)

private theorem r9_40 : PointClaim 9 .empty 122 50 9 :=
  pointBound (l := 51)

private theorem r9_41 : PointClaim 9 .empty 123 50 9 :=
  pointBound (l := 51)

private theorem exact9 (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
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
  by_cases hJ4 : a.j ≤ 39
  · apply r9_4 <;> omega
  by_cases hJ5 : a.j ≤ 41
  · apply r9_5 <;> omega
  by_cases hJ6 : a.j ≤ 42
  · apply r9_6 <;> omega
  by_cases hJ7 : a.j ≤ 43
  · apply r9_7 <;> omega
  by_cases hJ8 : a.j ≤ 44
  · apply r9_8 <;> omega
  by_cases hJ9 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 122
    · apply r9_9 <;> omega
    apply r9_10 <;> omega
  by_cases hJ10 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 119
    · apply r9_11 <;> omega
    apply r9_12 <;> omega
  by_cases hJ11 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 116
    · apply r9_13 <;> omega
    by_cases hB1 : a.b ≤ 122
    · apply r9_14 <;> omega
    apply r9_15 <;> omega
  by_cases hJ12 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 114
    · apply r9_16 <;> omega
    by_cases hB1 : a.b ≤ 119
    · apply r9_17 <;> omega
    by_cases hB2 : a.b ≤ 120
    · apply r9_18 <;> omega
    by_cases hB3 : a.b ≤ 121
    · apply r9_19 <;> omega
    by_cases hB4 : a.b ≤ 122
    · apply r9_20 <;> omega
    apply r9_21 <;> omega
  by_cases hJ13 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 111
    · apply r9_22 <;> omega
    by_cases hB1 : a.b ≤ 116
    · apply r9_23 <;> omega
    by_cases hB2 : a.b ≤ 117
    · apply r9_24 <;> omega
    by_cases hB3 : a.b ≤ 118
    · apply r9_25 <;> omega
    by_cases hB4 : a.b ≤ 119
    · apply r9_26 <;> omega
    by_cases hB5 : a.b ≤ 120
    · apply r9_27 <;> omega
    by_cases hB6 : a.b ≤ 121
    · apply r9_28 <;> omega
    by_cases hB7 : a.b ≤ 122
    · apply r9_29 <;> omega
    apply r9_30 <;> omega
  by_cases hB0 : a.b ≤ 109
  · apply r9_31 <;> omega
  by_cases hB1 : a.b ≤ 114
  · apply r9_32 <;> omega
  by_cases hB2 : a.b ≤ 115
  · apply r9_33 <;> omega
  by_cases hB3 : a.b ≤ 116
  · apply r9_34 <;> omega
  by_cases hB4 : a.b ≤ 117
  · apply r9_35 <;> omega
  by_cases hB5 : a.b ≤ 118
  · apply r9_36 <;> omega
  by_cases hB6 : a.b ≤ 119
  · apply r9_37 <;> omega
  by_cases hB7 : a.b ≤ 120
  · apply r9_38 <;> omega
  by_cases hB8 : a.b ≤ 121
  · apply r9_39 <;> omega
  by_cases hB9 : a.b ≤ 122
  · apply r9_40 <;> omega
  apply r9_41 <;> omega

private theorem r10_0 : RectangleClaim 10 .empty 10 30 123 30 10 :=
  rectangleBound (l := 43)

private theorem r10_1 : RectangleClaim 10 .empty 11 31 123 33 10 :=
  rectangleBound (l := 43)

private theorem r10_2 : RectangleClaim 10 .empty 12 34 123 36 10 :=
  rectangleBound (l := 44)

private theorem r10_3 : RectangleClaim 10 .empty 13 37 123 39 10 :=
  rectangleBound (l := 46)

private theorem r10_4 : RectangleClaim 10 .empty 14 40 123 41 10 :=
  rectangleBound (l := 46)

private theorem r10_5 : RectangleClaim 10 .empty 14 42 123 42 10 :=
  rectangleBound (l := 47)

private theorem r10_6 : RectangleClaim 10 .empty 15 43 123 43 10 :=
  rectangleBound (l := 47)

private theorem r10_7 : RectangleClaim 10 .empty 15 44 123 44 10 :=
  rectangleBound (l := 48)

private theorem r10_8 : RectangleClaim 10 .empty 15 45 122 45 10 :=
  rectangleBound (l := 48)

private theorem r10_9 : RectangleClaim 10 .empty 123 45 123 45 10 :=
  rectangleBound (l := 49)

private theorem r10_10 : RectangleClaim 10 .empty 16 46 119 46 10 :=
  rectangleBound (l := 48)

private theorem r10_11 : RectangleClaim 10 .empty 120 46 123 46 10 :=
  rectangleBound (l := 50)

private theorem r10_12 : RectangleClaim 10 .empty 16 47 116 47 10 :=
  rectangleBound (l := 48)

private theorem r10_13 : RectangleClaim 10 .empty 117 47 121 47 10 :=
  rectangleBound (l := 50)

private theorem r10_14 : PointClaim 10 .empty 122 47 10 :=
  pointBound (l := 50)

private theorem r10_15 : PointClaim 10 .empty 123 47 10 :=
  pointBound (l := 50)

private theorem r10_16 : RectangleClaim 10 .empty 16 48 113 48 10 :=
  rectangleBound (l := 48)

private theorem r10_17 : RectangleClaim 10 .empty 114 48 118 48 10 :=
  rectangleBound (l := 50)

private theorem r10_18 : PointClaim 10 .empty 119 48 10 :=
  pointBound (l := 50)

private theorem r10_19 : PointClaim 10 .empty 120 48 10 :=
  pointBound (l := 50)

private theorem r10_20 : PointClaim 10 .empty 121 48 10 :=
  pointBound (l := 50)

private theorem r10_21 : PointClaim 10 .empty 122 48 10 :=
  pointBound (l := 50)

private theorem r10_22 : PointClaim 10 .empty 123 48 10 :=
  pointBound (l := 50)

private theorem r10_23 : RectangleClaim 10 .empty 17 49 111 49 10 :=
  rectangleBound (l := 48)

private theorem r10_24 : RectangleClaim 10 .empty 112 49 116 49 10 :=
  rectangleBound (l := 50)

private theorem r10_25 : PointClaim 10 .empty 117 49 10 :=
  pointBound (l := 50)

private theorem r10_26 : PointClaim 10 .empty 118 49 10 :=
  pointBound (l := 50)

private theorem r10_27 : PointClaim 10 .empty 119 49 10 :=
  pointBound (l := 50)

private theorem r10_28 : PointClaim 10 .empty 120 49 10 :=
  pointBound (l := 50)

private theorem r10_29 : PointClaim 10 .empty 121 49 10 :=
  pointBound (l := 50)

private theorem r10_30 : PointClaim 10 .empty 122 49 10 :=
  pointBound (l := 50)

private theorem r10_31 : PointClaim 10 .empty 123 49 10 :=
  pointBound (l := 50)

private theorem r10_32 : RectangleClaim 10 .empty 17 50 109 50 10 :=
  rectangleBound (l := 48)

private theorem r10_33 : RectangleClaim 10 .empty 110 50 113 50 10 :=
  rectangleBound (l := 50)

private theorem r10_34 : PointClaim 10 .empty 114 50 10 :=
  pointBound (l := 50)

private theorem r10_35 : PointClaim 10 .empty 115 50 10 :=
  pointBound (l := 50)

private theorem r10_36 : PointClaim 10 .empty 116 50 10 :=
  pointBound (l := 50)

private theorem r10_37 : PointClaim 10 .empty 117 50 10 :=
  pointBound (l := 50)

private theorem r10_38 : PointClaim 10 .empty 118 50 10 :=
  pointBound (l := 50)

private theorem r10_39 : PointClaim 10 .empty 119 50 10 :=
  pointBound (l := 51)

private theorem r10_40 : PointClaim 10 .empty 120 50 10 :=
  pointBound (l := 51)

private theorem r10_41 : PointClaim 10 .empty 121 50 10 :=
  pointBound (l := 51)

private theorem r10_42 : PointClaim 10 .empty 122 50 10 :=
  pointBound (l := 51)

private theorem r10_43 : PointClaim 10 .empty 123 50 10 :=
  pointBound (l := 51)

private theorem exact10 (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    physicalPrice a (order .empty a) ≤ allowance 10 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 30
  · apply r10_0 <;> omega
  by_cases hJ1 : a.j ≤ 33
  · apply r10_1 <;> omega
  by_cases hJ2 : a.j ≤ 36
  · apply r10_2 <;> omega
  by_cases hJ3 : a.j ≤ 39
  · apply r10_3 <;> omega
  by_cases hJ4 : a.j ≤ 41
  · apply r10_4 <;> omega
  by_cases hJ5 : a.j ≤ 42
  · apply r10_5 <;> omega
  by_cases hJ6 : a.j ≤ 43
  · apply r10_6 <;> omega
  by_cases hJ7 : a.j ≤ 44
  · apply r10_7 <;> omega
  by_cases hJ8 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 122
    · apply r10_8 <;> omega
    apply r10_9 <;> omega
  by_cases hJ9 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 119
    · apply r10_10 <;> omega
    apply r10_11 <;> omega
  by_cases hJ10 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 116
    · apply r10_12 <;> omega
    by_cases hB1 : a.b ≤ 121
    · apply r10_13 <;> omega
    by_cases hB2 : a.b ≤ 122
    · apply r10_14 <;> omega
    apply r10_15 <;> omega
  by_cases hJ11 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 113
    · apply r10_16 <;> omega
    by_cases hB1 : a.b ≤ 118
    · apply r10_17 <;> omega
    by_cases hB2 : a.b ≤ 119
    · apply r10_18 <;> omega
    by_cases hB3 : a.b ≤ 120
    · apply r10_19 <;> omega
    by_cases hB4 : a.b ≤ 121
    · apply r10_20 <;> omega
    by_cases hB5 : a.b ≤ 122
    · apply r10_21 <;> omega
    apply r10_22 <;> omega
  by_cases hJ12 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 111
    · apply r10_23 <;> omega
    by_cases hB1 : a.b ≤ 116
    · apply r10_24 <;> omega
    by_cases hB2 : a.b ≤ 117
    · apply r10_25 <;> omega
    by_cases hB3 : a.b ≤ 118
    · apply r10_26 <;> omega
    by_cases hB4 : a.b ≤ 119
    · apply r10_27 <;> omega
    by_cases hB5 : a.b ≤ 120
    · apply r10_28 <;> omega
    by_cases hB6 : a.b ≤ 121
    · apply r10_29 <;> omega
    by_cases hB7 : a.b ≤ 122
    · apply r10_30 <;> omega
    apply r10_31 <;> omega
  by_cases hB0 : a.b ≤ 109
  · apply r10_32 <;> omega
  by_cases hB1 : a.b ≤ 113
  · apply r10_33 <;> omega
  by_cases hB2 : a.b ≤ 114
  · apply r10_34 <;> omega
  by_cases hB3 : a.b ≤ 115
  · apply r10_35 <;> omega
  by_cases hB4 : a.b ≤ 116
  · apply r10_36 <;> omega
  by_cases hB5 : a.b ≤ 117
  · apply r10_37 <;> omega
  by_cases hB6 : a.b ≤ 118
  · apply r10_38 <;> omega
  by_cases hB7 : a.b ≤ 119
  · apply r10_39 <;> omega
  by_cases hB8 : a.b ≤ 120
  · apply r10_40 <;> omega
  by_cases hB9 : a.b ≤ 121
  · apply r10_41 <;> omega
  by_cases hB10 : a.b ≤ 122
  · apply r10_42 <;> omega
  apply r10_43 <;> omega

private theorem r11_0 : RectangleClaim 11 .empty 11 33 123 33 11 :=
  rectangleBound (l := 44)

private theorem r11_1 : RectangleClaim 11 .empty 12 34 123 36 11 :=
  rectangleBound (l := 44)

private theorem r11_2 : RectangleClaim 11 .empty 13 37 123 39 11 :=
  rectangleBound (l := 46)

private theorem r11_3 : RectangleClaim 11 .empty 14 40 123 41 11 :=
  rectangleBound (l := 46)

private theorem r11_4 : RectangleClaim 11 .empty 14 42 123 42 11 :=
  rectangleBound (l := 47)

private theorem r11_5 : RectangleClaim 11 .empty 15 43 123 43 11 :=
  rectangleBound (l := 47)

private theorem r11_6 : RectangleClaim 11 .empty 15 44 123 44 11 :=
  rectangleBound (l := 48)

private theorem r11_7 : RectangleClaim 11 .empty 15 45 122 45 11 :=
  rectangleBound (l := 48)

private theorem r11_8 : RectangleClaim 11 .empty 123 45 123 45 11 :=
  rectangleBound (l := 49)

private theorem r11_9 : RectangleClaim 11 .empty 16 46 119 46 11 :=
  rectangleBound (l := 48)

private theorem r11_10 : RectangleClaim 11 .empty 120 46 123 46 11 :=
  rectangleBound (l := 50)

private theorem r11_11 : RectangleClaim 11 .empty 16 47 116 47 11 :=
  rectangleBound (l := 48)

private theorem r11_12 : RectangleClaim 11 .empty 117 47 121 47 11 :=
  rectangleBound (l := 50)

private theorem r11_13 : PointClaim 11 .empty 122 47 11 :=
  pointBound (l := 50)

private theorem r11_14 : PointClaim 11 .empty 123 47 11 :=
  pointBound (l := 50)

private theorem r11_15 : RectangleClaim 11 .empty 16 48 113 48 11 :=
  rectangleBound (l := 48)

private theorem r11_16 : RectangleClaim 11 .empty 114 48 118 48 11 :=
  rectangleBound (l := 50)

private theorem r11_17 : PointClaim 11 .empty 119 48 11 :=
  pointBound (l := 50)

private theorem r11_18 : PointClaim 11 .empty 120 48 11 :=
  pointBound (l := 50)

private theorem r11_19 : PointClaim 11 .empty 121 48 11 :=
  pointBound (l := 50)

private theorem r11_20 : PointClaim 11 .empty 122 48 11 :=
  pointBound (l := 50)

private theorem r11_21 : PointClaim 11 .empty 123 48 11 :=
  pointBound (l := 50)

private theorem r11_22 : RectangleClaim 11 .empty 17 49 111 49 11 :=
  rectangleBound (l := 48)

private theorem r11_23 : RectangleClaim 11 .empty 112 49 116 49 11 :=
  rectangleBound (l := 50)

private theorem r11_24 : PointClaim 11 .empty 117 49 11 :=
  pointBound (l := 50)

private theorem r11_25 : PointClaim 11 .empty 118 49 11 :=
  pointBound (l := 50)

private theorem r11_26 : PointClaim 11 .empty 119 49 11 :=
  pointBound (l := 50)

private theorem r11_27 : PointClaim 11 .empty 120 49 11 :=
  pointBound (l := 50)

private theorem r11_28 : PointClaim 11 .empty 121 49 11 :=
  pointBound (l := 50)

private theorem r11_29 : PointClaim 11 .empty 122 49 11 :=
  pointBound (l := 50)

private theorem r11_30 : PointClaim 11 .empty 123 49 11 :=
  pointBound (l := 50)

private theorem r11_31 : RectangleClaim 11 .empty 17 50 108 50 11 :=
  rectangleBound (l := 48)

private theorem r11_32 : RectangleClaim 11 .empty 109 50 113 50 11 :=
  rectangleBound (l := 50)

private theorem r11_33 : PointClaim 11 .empty 114 50 11 :=
  pointBound (l := 50)

private theorem r11_34 : PointClaim 11 .empty 115 50 11 :=
  pointBound (l := 50)

private theorem r11_35 : PointClaim 11 .empty 116 50 11 :=
  pointBound (l := 50)

private theorem r11_36 : PointClaim 11 .empty 117 50 11 :=
  pointBound (l := 50)

private theorem r11_37 : PointClaim 11 .empty 118 50 11 :=
  pointBound (l := 50)

private theorem r11_38 : PointClaim 11 .empty 119 50 11 :=
  pointBound (l := 51)

private theorem r11_39 : PointClaim 11 .empty 120 50 11 :=
  pointBound (l := 51)

private theorem r11_40 : PointClaim 11 .empty 121 50 11 :=
  pointBound (l := 51)

private theorem r11_41 : PointClaim 11 .empty 122 50 11 :=
  pointBound (l := 51)

private theorem r11_42 : PointClaim 11 .empty 123 50 11 :=
  pointBound (l := 51)

private theorem exact11 (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    physicalPrice a (order .empty a) ≤ allowance 11 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 33
  · apply r11_0 <;> omega
  by_cases hJ1 : a.j ≤ 36
  · apply r11_1 <;> omega
  by_cases hJ2 : a.j ≤ 39
  · apply r11_2 <;> omega
  by_cases hJ3 : a.j ≤ 41
  · apply r11_3 <;> omega
  by_cases hJ4 : a.j ≤ 42
  · apply r11_4 <;> omega
  by_cases hJ5 : a.j ≤ 43
  · apply r11_5 <;> omega
  by_cases hJ6 : a.j ≤ 44
  · apply r11_6 <;> omega
  by_cases hJ7 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 122
    · apply r11_7 <;> omega
    apply r11_8 <;> omega
  by_cases hJ8 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 119
    · apply r11_9 <;> omega
    apply r11_10 <;> omega
  by_cases hJ9 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 116
    · apply r11_11 <;> omega
    by_cases hB1 : a.b ≤ 121
    · apply r11_12 <;> omega
    by_cases hB2 : a.b ≤ 122
    · apply r11_13 <;> omega
    apply r11_14 <;> omega
  by_cases hJ10 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 113
    · apply r11_15 <;> omega
    by_cases hB1 : a.b ≤ 118
    · apply r11_16 <;> omega
    by_cases hB2 : a.b ≤ 119
    · apply r11_17 <;> omega
    by_cases hB3 : a.b ≤ 120
    · apply r11_18 <;> omega
    by_cases hB4 : a.b ≤ 121
    · apply r11_19 <;> omega
    by_cases hB5 : a.b ≤ 122
    · apply r11_20 <;> omega
    apply r11_21 <;> omega
  by_cases hJ11 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 111
    · apply r11_22 <;> omega
    by_cases hB1 : a.b ≤ 116
    · apply r11_23 <;> omega
    by_cases hB2 : a.b ≤ 117
    · apply r11_24 <;> omega
    by_cases hB3 : a.b ≤ 118
    · apply r11_25 <;> omega
    by_cases hB4 : a.b ≤ 119
    · apply r11_26 <;> omega
    by_cases hB5 : a.b ≤ 120
    · apply r11_27 <;> omega
    by_cases hB6 : a.b ≤ 121
    · apply r11_28 <;> omega
    by_cases hB7 : a.b ≤ 122
    · apply r11_29 <;> omega
    apply r11_30 <;> omega
  by_cases hB0 : a.b ≤ 108
  · apply r11_31 <;> omega
  by_cases hB1 : a.b ≤ 113
  · apply r11_32 <;> omega
  by_cases hB2 : a.b ≤ 114
  · apply r11_33 <;> omega
  by_cases hB3 : a.b ≤ 115
  · apply r11_34 <;> omega
  by_cases hB4 : a.b ≤ 116
  · apply r11_35 <;> omega
  by_cases hB5 : a.b ≤ 117
  · apply r11_36 <;> omega
  by_cases hB6 : a.b ≤ 118
  · apply r11_37 <;> omega
  by_cases hB7 : a.b ≤ 119
  · apply r11_38 <;> omega
  by_cases hB8 : a.b ≤ 120
  · apply r11_39 <;> omega
  by_cases hB9 : a.b ≤ 121
  · apply r11_40 <;> omega
  by_cases hB10 : a.b ≤ 122
  · apply r11_41 <;> omega
  apply r11_42 <;> omega

private theorem r12_0 : RectangleClaim 12 .empty 12 36 123 36 12 :=
  rectangleBound (l := 45)

private theorem r12_1 : RectangleClaim 12 .empty 13 37 123 39 12 :=
  rectangleBound (l := 46)

private theorem r12_2 : RectangleClaim 12 .empty 14 40 123 41 12 :=
  rectangleBound (l := 46)

private theorem r12_3 : RectangleClaim 12 .empty 14 42 123 42 12 :=
  rectangleBound (l := 47)

private theorem r12_4 : RectangleClaim 12 .empty 15 43 123 43 12 :=
  rectangleBound (l := 47)

private theorem r12_5 : RectangleClaim 12 .empty 15 44 123 44 12 :=
  rectangleBound (l := 48)

private theorem r12_6 : RectangleClaim 12 .empty 15 45 122 45 12 :=
  rectangleBound (l := 48)

private theorem r12_7 : RectangleClaim 12 .empty 123 45 123 45 12 :=
  rectangleBound (l := 49)

private theorem r12_8 : RectangleClaim 12 .empty 16 46 119 46 12 :=
  rectangleBound (l := 48)

private theorem r12_9 : RectangleClaim 12 .empty 120 46 123 46 12 :=
  rectangleBound (l := 50)

private theorem r12_10 : RectangleClaim 12 .empty 16 47 116 47 12 :=
  rectangleBound (l := 48)

private theorem r12_11 : RectangleClaim 12 .empty 117 47 121 47 12 :=
  rectangleBound (l := 50)

private theorem r12_12 : PointClaim 12 .empty 122 47 12 :=
  pointBound (l := 50)

private theorem r12_13 : PointClaim 12 .empty 123 47 12 :=
  pointBound (l := 50)

private theorem r12_14 : RectangleClaim 12 .empty 16 48 113 48 12 :=
  rectangleBound (l := 48)

private theorem r12_15 : RectangleClaim 12 .empty 114 48 118 48 12 :=
  rectangleBound (l := 50)

private theorem r12_16 : PointClaim 12 .empty 119 48 12 :=
  pointBound (l := 50)

private theorem r12_17 : PointClaim 12 .empty 120 48 12 :=
  pointBound (l := 50)

private theorem r12_18 : PointClaim 12 .empty 121 48 12 :=
  pointBound (l := 50)

private theorem r12_19 : PointClaim 12 .empty 122 48 12 :=
  pointBound (l := 50)

private theorem r12_20 : PointClaim 12 .empty 123 48 12 :=
  pointBound (l := 50)

private theorem r12_21 : RectangleClaim 12 .empty 17 49 111 49 12 :=
  rectangleBound (l := 48)

private theorem r12_22 : RectangleClaim 12 .empty 112 49 115 49 12 :=
  rectangleBound (l := 50)

private theorem r12_23 : PointClaim 12 .empty 116 49 12 :=
  pointBound (l := 50)

private theorem r12_24 : PointClaim 12 .empty 117 49 12 :=
  pointBound (l := 50)

private theorem r12_25 : PointClaim 12 .empty 118 49 12 :=
  pointBound (l := 50)

private theorem r12_26 : PointClaim 12 .empty 119 49 12 :=
  pointBound (l := 50)

private theorem r12_27 : PointClaim 12 .empty 120 49 12 :=
  pointBound (l := 50)

private theorem r12_28 : PointClaim 12 .empty 121 49 12 :=
  pointBound (l := 50)

private theorem r12_29 : PointClaim 12 .empty 122 49 12 :=
  pointBound (l := 50)

private theorem r12_30 : PointClaim 12 .empty 123 49 12 :=
  pointBound (l := 50)

private theorem r12_31 : RectangleClaim 12 .empty 17 50 108 50 12 :=
  rectangleBound (l := 48)

private theorem r12_32 : RectangleClaim 12 .empty 109 50 113 50 12 :=
  rectangleBound (l := 50)

private theorem r12_33 : PointClaim 12 .empty 114 50 12 :=
  pointBound (l := 50)

private theorem r12_34 : PointClaim 12 .empty 115 50 12 :=
  pointBound (l := 50)

private theorem r12_35 : PointClaim 12 .empty 116 50 12 :=
  pointBound (l := 50)

private theorem r12_36 : PointClaim 12 .empty 117 50 12 :=
  pointBound (l := 50)

private theorem r12_37 : PointClaim 12 .empty 118 50 12 :=
  pointBound (l := 50)

private theorem r12_38 : PointClaim 12 .empty 119 50 12 :=
  pointBound (l := 51)

private theorem r12_39 : PointClaim 12 .empty 120 50 12 :=
  pointBound (l := 51)

private theorem r12_40 : PointClaim 12 .empty 121 50 12 :=
  pointBound (l := 51)

private theorem r12_41 : PointClaim 12 .empty 122 50 12 :=
  pointBound (l := 51)

private theorem r12_42 : PointClaim 12 .empty 123 50 12 :=
  pointBound (l := 51)

private theorem exact12 (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    physicalPrice a (order .empty a) ≤ allowance 12 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 36
  · apply r12_0 <;> omega
  by_cases hJ1 : a.j ≤ 39
  · apply r12_1 <;> omega
  by_cases hJ2 : a.j ≤ 41
  · apply r12_2 <;> omega
  by_cases hJ3 : a.j ≤ 42
  · apply r12_3 <;> omega
  by_cases hJ4 : a.j ≤ 43
  · apply r12_4 <;> omega
  by_cases hJ5 : a.j ≤ 44
  · apply r12_5 <;> omega
  by_cases hJ6 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 122
    · apply r12_6 <;> omega
    apply r12_7 <;> omega
  by_cases hJ7 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 119
    · apply r12_8 <;> omega
    apply r12_9 <;> omega
  by_cases hJ8 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 116
    · apply r12_10 <;> omega
    by_cases hB1 : a.b ≤ 121
    · apply r12_11 <;> omega
    by_cases hB2 : a.b ≤ 122
    · apply r12_12 <;> omega
    apply r12_13 <;> omega
  by_cases hJ9 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 113
    · apply r12_14 <;> omega
    by_cases hB1 : a.b ≤ 118
    · apply r12_15 <;> omega
    by_cases hB2 : a.b ≤ 119
    · apply r12_16 <;> omega
    by_cases hB3 : a.b ≤ 120
    · apply r12_17 <;> omega
    by_cases hB4 : a.b ≤ 121
    · apply r12_18 <;> omega
    by_cases hB5 : a.b ≤ 122
    · apply r12_19 <;> omega
    apply r12_20 <;> omega
  by_cases hJ10 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 111
    · apply r12_21 <;> omega
    by_cases hB1 : a.b ≤ 115
    · apply r12_22 <;> omega
    by_cases hB2 : a.b ≤ 116
    · apply r12_23 <;> omega
    by_cases hB3 : a.b ≤ 117
    · apply r12_24 <;> omega
    by_cases hB4 : a.b ≤ 118
    · apply r12_25 <;> omega
    by_cases hB5 : a.b ≤ 119
    · apply r12_26 <;> omega
    by_cases hB6 : a.b ≤ 120
    · apply r12_27 <;> omega
    by_cases hB7 : a.b ≤ 121
    · apply r12_28 <;> omega
    by_cases hB8 : a.b ≤ 122
    · apply r12_29 <;> omega
    apply r12_30 <;> omega
  by_cases hB0 : a.b ≤ 108
  · apply r12_31 <;> omega
  by_cases hB1 : a.b ≤ 113
  · apply r12_32 <;> omega
  by_cases hB2 : a.b ≤ 114
  · apply r12_33 <;> omega
  by_cases hB3 : a.b ≤ 115
  · apply r12_34 <;> omega
  by_cases hB4 : a.b ≤ 116
  · apply r12_35 <;> omega
  by_cases hB5 : a.b ≤ 117
  · apply r12_36 <;> omega
  by_cases hB6 : a.b ≤ 118
  · apply r12_37 <;> omega
  by_cases hB7 : a.b ≤ 119
  · apply r12_38 <;> omega
  by_cases hB8 : a.b ≤ 120
  · apply r12_39 <;> omega
  by_cases hB9 : a.b ≤ 121
  · apply r12_40 <;> omega
  by_cases hB10 : a.b ≤ 122
  · apply r12_41 <;> omega
  apply r12_42 <;> omega

private theorem r13_0 : RectangleClaim 13 .empty 13 39 123 39 13 :=
  rectangleBound (l := 46)

private theorem r13_1 : RectangleClaim 13 .empty 14 40 123 41 13 :=
  rectangleBound (l := 46)

private theorem r13_2 : RectangleClaim 13 .empty 14 42 123 42 13 :=
  rectangleBound (l := 47)

private theorem r13_3 : RectangleClaim 13 .empty 15 43 123 43 13 :=
  rectangleBound (l := 47)

private theorem r13_4 : RectangleClaim 13 .empty 15 44 123 44 13 :=
  rectangleBound (l := 48)

private theorem r13_5 : RectangleClaim 13 .empty 15 45 122 45 13 :=
  rectangleBound (l := 48)

private theorem r13_6 : RectangleClaim 13 .empty 123 45 123 45 13 :=
  rectangleBound (l := 49)

private theorem r13_7 : RectangleClaim 13 .empty 16 46 119 46 13 :=
  rectangleBound (l := 48)

private theorem r13_8 : RectangleClaim 13 .empty 120 46 123 46 13 :=
  rectangleBound (l := 50)

private theorem r13_9 : RectangleClaim 13 .empty 16 47 116 47 13 :=
  rectangleBound (l := 48)

private theorem r13_10 : RectangleClaim 13 .empty 117 47 121 47 13 :=
  rectangleBound (l := 50)

private theorem r13_11 : PointClaim 13 .empty 122 47 13 :=
  pointBound (l := 50)

private theorem r13_12 : PointClaim 13 .empty 123 47 13 :=
  pointBound (l := 50)

private theorem r13_13 : RectangleClaim 13 .empty 16 48 113 48 13 :=
  rectangleBound (l := 48)

private theorem r13_14 : RectangleClaim 13 .empty 114 48 118 48 13 :=
  rectangleBound (l := 50)

private theorem r13_15 : PointClaim 13 .empty 119 48 13 :=
  pointBound (l := 50)

private theorem r13_16 : PointClaim 13 .empty 120 48 13 :=
  pointBound (l := 50)

private theorem r13_17 : PointClaim 13 .empty 121 48 13 :=
  pointBound (l := 50)

private theorem r13_18 : PointClaim 13 .empty 122 48 13 :=
  pointBound (l := 50)

private theorem r13_19 : PointClaim 13 .empty 123 48 13 :=
  pointBound (l := 50)

private theorem r13_20 : RectangleClaim 13 .empty 17 49 111 49 13 :=
  rectangleBound (l := 48)

private theorem r13_21 : RectangleClaim 13 .empty 112 49 116 49 13 :=
  rectangleBound (l := 50)

private theorem r13_22 : PointClaim 13 .empty 117 49 13 :=
  pointBound (l := 50)

private theorem r13_23 : PointClaim 13 .empty 118 49 13 :=
  pointBound (l := 50)

private theorem r13_24 : PointClaim 13 .empty 119 49 13 :=
  pointBound (l := 50)

private theorem r13_25 : PointClaim 13 .empty 120 49 13 :=
  pointBound (l := 50)

private theorem r13_26 : PointClaim 13 .empty 121 49 13 :=
  pointBound (l := 50)

private theorem r13_27 : PointClaim 13 .empty 122 49 13 :=
  pointBound (l := 50)

private theorem r13_28 : PointClaim 13 .empty 123 49 13 :=
  pointBound (l := 50)

private theorem r13_29 : RectangleClaim 13 .empty 17 50 108 50 13 :=
  rectangleBound (l := 48)

private theorem r13_30 : RectangleClaim 13 .empty 109 50 113 50 13 :=
  rectangleBound (l := 50)

private theorem r13_31 : PointClaim 13 .empty 114 50 13 :=
  pointBound (l := 50)

private theorem r13_32 : PointClaim 13 .empty 115 50 13 :=
  pointBound (l := 50)

private theorem r13_33 : PointClaim 13 .empty 116 50 13 :=
  pointBound (l := 50)

private theorem r13_34 : PointClaim 13 .empty 117 50 13 :=
  pointBound (l := 50)

private theorem r13_35 : PointClaim 13 .empty 118 50 13 :=
  pointBound (l := 50)

private theorem r13_36 : PointClaim 13 .empty 119 50 13 :=
  pointBound (l := 51)

private theorem r13_37 : PointClaim 13 .empty 120 50 13 :=
  pointBound (l := 51)

private theorem r13_38 : PointClaim 13 .empty 121 50 13 :=
  pointBound (l := 51)

private theorem r13_39 : PointClaim 13 .empty 122 50 13 :=
  pointBound (l := 51)

private theorem r13_40 : PointClaim 13 .empty 123 50 13 :=
  pointBound (l := 51)

private theorem exact13 (a : Shape) (ha : Valid a) (ht : a.t = 13)
    (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    physicalPrice a (order .empty a) ≤ allowance 13 .empty a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 39
  · apply r13_0 <;> omega
  by_cases hJ1 : a.j ≤ 41
  · apply r13_1 <;> omega
  by_cases hJ2 : a.j ≤ 42
  · apply r13_2 <;> omega
  by_cases hJ3 : a.j ≤ 43
  · apply r13_3 <;> omega
  by_cases hJ4 : a.j ≤ 44
  · apply r13_4 <;> omega
  by_cases hJ5 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 122
    · apply r13_5 <;> omega
    apply r13_6 <;> omega
  by_cases hJ6 : a.j ≤ 46
  · by_cases hB0 : a.b ≤ 119
    · apply r13_7 <;> omega
    apply r13_8 <;> omega
  by_cases hJ7 : a.j ≤ 47
  · by_cases hB0 : a.b ≤ 116
    · apply r13_9 <;> omega
    by_cases hB1 : a.b ≤ 121
    · apply r13_10 <;> omega
    by_cases hB2 : a.b ≤ 122
    · apply r13_11 <;> omega
    apply r13_12 <;> omega
  by_cases hJ8 : a.j ≤ 48
  · by_cases hB0 : a.b ≤ 113
    · apply r13_13 <;> omega
    by_cases hB1 : a.b ≤ 118
    · apply r13_14 <;> omega
    by_cases hB2 : a.b ≤ 119
    · apply r13_15 <;> omega
    by_cases hB3 : a.b ≤ 120
    · apply r13_16 <;> omega
    by_cases hB4 : a.b ≤ 121
    · apply r13_17 <;> omega
    by_cases hB5 : a.b ≤ 122
    · apply r13_18 <;> omega
    apply r13_19 <;> omega
  by_cases hJ9 : a.j ≤ 49
  · by_cases hB0 : a.b ≤ 111
    · apply r13_20 <;> omega
    by_cases hB1 : a.b ≤ 116
    · apply r13_21 <;> omega
    by_cases hB2 : a.b ≤ 117
    · apply r13_22 <;> omega
    by_cases hB3 : a.b ≤ 118
    · apply r13_23 <;> omega
    by_cases hB4 : a.b ≤ 119
    · apply r13_24 <;> omega
    by_cases hB5 : a.b ≤ 120
    · apply r13_25 <;> omega
    by_cases hB6 : a.b ≤ 121
    · apply r13_26 <;> omega
    by_cases hB7 : a.b ≤ 122
    · apply r13_27 <;> omega
    apply r13_28 <;> omega
  by_cases hB0 : a.b ≤ 108
  · apply r13_29 <;> omega
  by_cases hB1 : a.b ≤ 113
  · apply r13_30 <;> omega
  by_cases hB2 : a.b ≤ 114
  · apply r13_31 <;> omega
  by_cases hB3 : a.b ≤ 115
  · apply r13_32 <;> omega
  by_cases hB4 : a.b ≤ 116
  · apply r13_33 <;> omega
  by_cases hB5 : a.b ≤ 117
  · apply r13_34 <;> omega
  by_cases hB6 : a.b ≤ 118
  · apply r13_35 <;> omega
  by_cases hB7 : a.b ≤ 119
  · apply r13_36 <;> omega
  by_cases hB8 : a.b ≤ 120
  · apply r13_37 <;> omega
  by_cases hB9 : a.b ≤ 121
  · apply r13_38 <;> omega
  by_cases hB10 : a.b ≤ 122
  · apply r13_39 <;> omega
  apply r13_40 <;> omega

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .empty).plus a) (fullCap top)) :
    physicalPrice a (order .empty a) ≤ allowance top .empty a.j := by
  change 0+a.b ≤ 123 ∧ 0+a.j ≤ 50 ∧ 0+a.t ≤ top at hc
  obtain ⟨hb, hj, ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 123 := by omega
  have hj' : a.j ≤ 50 := by omega
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
