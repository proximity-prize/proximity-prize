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

private theorem r1_0 : RectangleClaim 1 .empty 1 3 121 3 1 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1 : RectangleClaim 1 .empty 2 4 73 4 1 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2 : RectangleClaim 1 .empty 74 4 121 4 1 :=
  rectangleBound (l := 2) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_3 : RectangleClaim 1 .empty 2 5 41 5 1 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_4 : RectangleClaim 1 .empty 42 5 83 5 1 :=
  rectangleBound (l := 2) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_5 : RectangleClaim 1 .empty 84 5 121 5 1 :=
  rectangleBound (l := 3) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_6 : RectangleClaim 1 .empty 2 6 29 6 1 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_7 : RectangleClaim 1 .empty 30 6 86 6 1 :=
  rectangleBound (l := 3) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_8 : RectangleClaim 1 .empty 87 6 121 6 1 :=
  rectangleBound (l := 10) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_9 : RectangleClaim 1 .empty 3 7 22 7 1 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_10 : RectangleClaim 1 .empty 23 7 66 7 1 :=
  rectangleBound (l := 3) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_11 : RectangleClaim 1 .empty 67 7 121 7 1 :=
  rectangleBound (l := 10) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_12 : RectangleClaim 1 .empty 3 8 18 8 1 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_13 : RectangleClaim 1 .empty 19 8 53 8 1 :=
  rectangleBound (l := 3) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_14 : RectangleClaim 1 .empty 54 8 88 8 1 :=
  rectangleBound (l := 5) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_15 : RectangleClaim 1 .empty 89 8 121 8 1 :=
  rectangleBound (l := 10) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_16 : RectangleClaim 1 .empty 3 9 104 9 1 :=
  rectangleBound (l := 7) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_17 : RectangleClaim 1 .empty 105 9 121 9 1 :=
  rectangleBound (l := 22) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_18 : RectangleClaim 1 .empty 4 10 92 10 1 :=
  rectangleBound (l := 7) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_19 : RectangleClaim 1 .empty 93 10 121 10 1 :=
  rectangleBound (l := 22) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_20 : RectangleClaim 1 .empty 4 11 83 11 1 :=
  rectangleBound (l := 7) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_21 : RectangleClaim 1 .empty 84 11 121 11 1 :=
  rectangleBound (l := 22) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_22 : RectangleClaim 1 .empty 4 12 121 12 1 :=
  rectangleBound (l := 21) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_23 : RectangleClaim 1 .empty 5 13 121 15 1 :=
  rectangleBound (l := 21) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_24 : RectangleClaim 1 .empty 6 16 121 18 1 :=
  rectangleBound (l := 25) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_25 : RectangleClaim 1 .empty 7 19 121 21 1 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_26 : RectangleClaim 1 .empty 8 22 121 24 1 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_27 : RectangleClaim 1 .empty 9 25 121 27 1 :=
  rectangleBound (l := 32) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_28 : RectangleClaim 1 .empty 10 28 121 30 1 :=
  rectangleBound (l := 39) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_29 : RectangleClaim 1 .empty 11 31 121 33 1 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_30 : RectangleClaim 1 .empty 12 34 121 36 1 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_31 : RectangleClaim 1 .empty 13 37 121 39 1 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_32 : RectangleClaim 1 .empty 14 40 121 42 1 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_33 : RectangleClaim 1 .empty 15 43 121 44 1 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_34 : RectangleClaim 1 .empty 15 45 121 45 1 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_35 : RectangleClaim 1 .empty 16 46 121 46 1 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_36 : RectangleClaim 1 .empty 16 47 121 47 1 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_37 : RectangleClaim 1 .empty 16 48 119 48 1 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_38 : RectangleClaim 1 .empty 120 48 121 48 1 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_39 : RectangleClaim 1 .empty 17 49 117 49 1 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_40 : RectangleClaim 1 .empty 118 49 121 49 1 :=
  rectangleBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r2_0 : RectangleClaim 2 .empty 2 6 28 6 2 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_1 : RectangleClaim 2 .empty 29 6 86 6 2 :=
  rectangleBound (l := 3) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_2 : RectangleClaim 2 .empty 87 6 121 6 2 :=
  rectangleBound (l := 10) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_3 : RectangleClaim 2 .empty 3 7 21 7 2 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_4 : RectangleClaim 2 .empty 22 7 65 7 2 :=
  rectangleBound (l := 3) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_5 : RectangleClaim 2 .empty 66 7 121 7 2 :=
  rectangleBound (l := 10) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_6 : RectangleClaim 2 .empty 3 8 17 8 2 :=
  rectangleBound (l := 1) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_7 : RectangleClaim 2 .empty 18 8 52 8 2 :=
  rectangleBound (l := 3) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_8 : RectangleClaim 2 .empty 53 8 87 8 2 :=
  rectangleBound (l := 5) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_9 : RectangleClaim 2 .empty 88 8 121 8 2 :=
  rectangleBound (l := 10) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_10 : RectangleClaim 2 .empty 3 9 104 9 2 :=
  rectangleBound (l := 7) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_11 : RectangleClaim 2 .empty 105 9 121 9 2 :=
  rectangleBound (l := 22) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_12 : RectangleClaim 2 .empty 4 10 91 10 2 :=
  rectangleBound (l := 7) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_13 : RectangleClaim 2 .empty 92 10 121 10 2 :=
  rectangleBound (l := 22) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_14 : RectangleClaim 2 .empty 4 11 82 11 2 :=
  rectangleBound (l := 7) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_15 : RectangleClaim 2 .empty 83 11 121 11 2 :=
  rectangleBound (l := 22) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_16 : RectangleClaim 2 .empty 4 12 121 12 2 :=
  rectangleBound (l := 21) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_17 : RectangleClaim 2 .empty 5 13 121 15 2 :=
  rectangleBound (l := 21) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_18 : RectangleClaim 2 .empty 6 16 121 18 2 :=
  rectangleBound (l := 25) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_19 : RectangleClaim 2 .empty 7 19 121 21 2 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_20 : RectangleClaim 2 .empty 8 22 121 24 2 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_21 : RectangleClaim 2 .empty 9 25 121 27 2 :=
  rectangleBound (l := 32) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_22 : RectangleClaim 2 .empty 10 28 121 30 2 :=
  rectangleBound (l := 39) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_23 : RectangleClaim 2 .empty 11 31 121 33 2 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_24 : RectangleClaim 2 .empty 12 34 121 36 2 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_25 : RectangleClaim 2 .empty 13 37 121 39 2 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_26 : RectangleClaim 2 .empty 14 40 121 42 2 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_27 : RectangleClaim 2 .empty 15 43 121 43 2 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_28 : RectangleClaim 2 .empty 15 44 121 44 2 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_29 : RectangleClaim 2 .empty 15 45 120 45 2 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_30 : RectangleClaim 2 .empty 121 45 121 45 2 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_31 : RectangleClaim 2 .empty 16 46 118 46 2 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_32 : RectangleClaim 2 .empty 119 46 121 46 2 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_33 : RectangleClaim 2 .empty 16 47 116 47 2 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_34 : RectangleClaim 2 .empty 117 47 121 47 2 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_35 : RectangleClaim 2 .empty 16 48 114 48 2 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_36 : RectangleClaim 2 .empty 115 48 121 48 2 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_37 : RectangleClaim 2 .empty 17 49 113 49 2 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_38 : RectangleClaim 2 .empty 114 49 121 49 2 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r3_0 : RectangleClaim 3 .empty 3 9 104 9 3 :=
  rectangleBound (l := 7) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_1 : RectangleClaim 3 .empty 105 9 121 9 3 :=
  rectangleBound (l := 22) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_2 : RectangleClaim 3 .empty 4 10 92 10 3 :=
  rectangleBound (l := 7) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_3 : RectangleClaim 3 .empty 93 10 121 10 3 :=
  rectangleBound (l := 22) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_4 : RectangleClaim 3 .empty 4 11 82 11 3 :=
  rectangleBound (l := 7) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_5 : RectangleClaim 3 .empty 83 11 121 11 3 :=
  rectangleBound (l := 22) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_6 : RectangleClaim 3 .empty 4 12 121 12 3 :=
  rectangleBound (l := 21) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_7 : RectangleClaim 3 .empty 5 13 121 15 3 :=
  rectangleBound (l := 21) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_8 : RectangleClaim 3 .empty 6 16 121 18 3 :=
  rectangleBound (l := 25) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_9 : RectangleClaim 3 .empty 7 19 121 21 3 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_10 : RectangleClaim 3 .empty 8 22 121 24 3 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_11 : RectangleClaim 3 .empty 9 25 121 27 3 :=
  rectangleBound (l := 32) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_12 : RectangleClaim 3 .empty 10 28 121 30 3 :=
  rectangleBound (l := 39) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_13 : RectangleClaim 3 .empty 11 31 121 33 3 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_14 : RectangleClaim 3 .empty 12 34 121 36 3 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_15 : RectangleClaim 3 .empty 13 37 121 39 3 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_16 : RectangleClaim 3 .empty 14 40 121 41 3 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_17 : RectangleClaim 3 .empty 14 42 121 42 3 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_18 : RectangleClaim 3 .empty 15 43 121 43 3 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_19 : RectangleClaim 3 .empty 15 44 118 44 3 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_20 : RectangleClaim 3 .empty 119 44 121 44 3 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_21 : RectangleClaim 3 .empty 15 45 116 45 3 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_22 : RectangleClaim 3 .empty 117 45 121 45 3 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_23 : RectangleClaim 3 .empty 16 46 114 46 3 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_24 : RectangleClaim 3 .empty 115 46 121 46 3 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_25 : RectangleClaim 3 .empty 16 47 112 47 3 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_26 : RectangleClaim 3 .empty 113 47 121 47 3 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_27 : RectangleClaim 3 .empty 16 48 110 48 3 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_28 : RectangleClaim 3 .empty 111 48 121 48 3 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_29 : RectangleClaim 3 .empty 17 49 109 49 3 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_30 : RectangleClaim 3 .empty 110 49 121 49 3 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r4_0 : RectangleClaim 4 .empty 4 12 121 12 4 :=
  rectangleBound (l := 21) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_1 : RectangleClaim 4 .empty 5 13 121 15 4 :=
  rectangleBound (l := 21) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_2 : RectangleClaim 4 .empty 6 16 121 18 4 :=
  rectangleBound (l := 25) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_3 : RectangleClaim 4 .empty 7 19 121 21 4 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_4 : RectangleClaim 4 .empty 8 22 121 24 4 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_5 : RectangleClaim 4 .empty 9 25 121 27 4 :=
  rectangleBound (l := 32) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_6 : RectangleClaim 4 .empty 10 28 121 30 4 :=
  rectangleBound (l := 39) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_7 : RectangleClaim 4 .empty 11 31 121 33 4 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_8 : RectangleClaim 4 .empty 12 34 121 36 4 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_9 : RectangleClaim 4 .empty 13 37 121 39 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_10 : RectangleClaim 4 .empty 14 40 121 40 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_11 : RectangleClaim 4 .empty 14 41 121 41 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_12 : RectangleClaim 4 .empty 14 42 120 42 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_13 : RectangleClaim 4 .empty 121 42 121 42 4 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_14 : RectangleClaim 4 .empty 15 43 118 43 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_15 : RectangleClaim 4 .empty 119 43 121 43 4 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_16 : RectangleClaim 4 .empty 15 44 115 44 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_17 : RectangleClaim 4 .empty 116 44 121 44 4 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_18 : RectangleClaim 4 .empty 15 45 113 45 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_19 : RectangleClaim 4 .empty 114 45 121 45 4 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_20 : RectangleClaim 4 .empty 16 46 111 46 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_21 : RectangleClaim 4 .empty 112 46 121 46 4 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_22 : RectangleClaim 4 .empty 16 47 109 47 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_23 : RectangleClaim 4 .empty 110 47 121 47 4 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_24 : RectangleClaim 4 .empty 16 48 107 48 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_25 : RectangleClaim 4 .empty 108 48 121 48 4 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_26 : RectangleClaim 4 .empty 17 49 105 49 4 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_27 : RectangleClaim 4 .empty 106 49 121 49 4 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r5_0 : RectangleClaim 5 .empty 5 15 121 15 5 :=
  rectangleBound (l := 25) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_1 : RectangleClaim 5 .empty 6 16 121 18 5 :=
  rectangleBound (l := 25) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_2 : RectangleClaim 5 .empty 7 19 121 21 5 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_3 : RectangleClaim 5 .empty 8 22 121 24 5 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_4 : RectangleClaim 5 .empty 9 25 121 27 5 :=
  rectangleBound (l := 32) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_5 : RectangleClaim 5 .empty 10 28 121 30 5 :=
  rectangleBound (l := 39) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_6 : RectangleClaim 5 .empty 11 31 121 33 5 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_7 : RectangleClaim 5 .empty 12 34 121 36 5 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_8 : RectangleClaim 5 .empty 13 37 121 38 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_9 : RectangleClaim 5 .empty 13 39 121 39 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_10 : RectangleClaim 5 .empty 14 40 121 40 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_11 : RectangleClaim 5 .empty 14 41 120 41 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_12 : RectangleClaim 5 .empty 121 41 121 41 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_13 : RectangleClaim 5 .empty 14 42 118 42 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_14 : RectangleClaim 5 .empty 119 42 121 42 5 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_15 : RectangleClaim 5 .empty 15 43 115 43 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_16 : RectangleClaim 5 .empty 116 43 121 43 5 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_17 : RectangleClaim 5 .empty 15 44 113 44 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_18 : RectangleClaim 5 .empty 114 44 121 44 5 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_19 : RectangleClaim 5 .empty 15 45 110 45 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_20 : RectangleClaim 5 .empty 111 45 121 45 5 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_21 : RectangleClaim 5 .empty 16 46 108 46 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_22 : RectangleClaim 5 .empty 109 46 121 46 5 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_23 : RectangleClaim 5 .empty 16 47 106 47 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_24 : RectangleClaim 5 .empty 107 47 121 47 5 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_25 : RectangleClaim 5 .empty 16 48 104 48 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_26 : RectangleClaim 5 .empty 105 48 121 48 5 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_27 : RectangleClaim 5 .empty 17 49 102 49 5 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_28 : RectangleClaim 5 .empty 103 49 119 49 5 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_29 : RectangleClaim 5 .empty 120 49 121 49 5 :=
  rectangleBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r6_0 : RectangleClaim 6 .empty 6 18 121 18 6 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_1 : RectangleClaim 6 .empty 7 19 121 21 6 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_2 : RectangleClaim 6 .empty 8 22 121 24 6 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_3 : RectangleClaim 6 .empty 9 25 121 27 6 :=
  rectangleBound (l := 32) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_4 : RectangleClaim 6 .empty 10 28 121 30 6 :=
  rectangleBound (l := 39) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_5 : RectangleClaim 6 .empty 11 31 121 33 6 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_6 : RectangleClaim 6 .empty 12 34 121 36 6 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_7 : RectangleClaim 6 .empty 13 37 121 38 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_8 : RectangleClaim 6 .empty 13 39 121 39 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_9 : RectangleClaim 6 .empty 14 40 121 40 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_10 : RectangleClaim 6 .empty 14 41 119 41 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_11 : RectangleClaim 6 .empty 120 41 121 41 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_12 : RectangleClaim 6 .empty 14 42 116 42 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_13 : RectangleClaim 6 .empty 117 42 121 42 6 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_14 : RectangleClaim 6 .empty 15 43 113 43 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_15 : RectangleClaim 6 .empty 114 43 121 43 6 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_16 : RectangleClaim 6 .empty 15 44 111 44 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_17 : RectangleClaim 6 .empty 112 44 121 44 6 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_18 : RectangleClaim 6 .empty 15 45 108 45 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_19 : RectangleClaim 6 .empty 109 45 121 45 6 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_20 : RectangleClaim 6 .empty 16 46 106 46 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_21 : RectangleClaim 6 .empty 107 46 121 46 6 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_22 : RectangleClaim 6 .empty 16 47 104 47 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_23 : RectangleClaim 6 .empty 105 47 121 47 6 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_24 : RectangleClaim 6 .empty 16 48 102 48 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_25 : RectangleClaim 6 .empty 103 48 119 48 6 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_26 : PointClaim 6 .empty 120 48 6 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_27 : PointClaim 6 .empty 121 48 6 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_28 : RectangleClaim 6 .empty 17 49 100 49 6 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_29 : RectangleClaim 6 .empty 101 49 117 49 6 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_30 : RectangleClaim 6 .empty 118 49 119 49 6 :=
  rectangleBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_31 : PointClaim 6 .empty 120 49 6 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_32 : PointClaim 6 .empty 121 49 6 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

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
  by_cases hB2 : a.b ≤ 119
  · apply r6_30 <;> omega
  by_cases hB3 : a.b ≤ 120
  · apply r6_31 <;> omega
  apply r6_32 <;> omega

private theorem r7_0 : RectangleClaim 7 .empty 7 21 121 21 7 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_1 : RectangleClaim 7 .empty 8 22 121 24 7 :=
  rectangleBound (l := 27) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_2 : RectangleClaim 7 .empty 9 25 121 27 7 :=
  rectangleBound (l := 32) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_3 : RectangleClaim 7 .empty 10 28 121 30 7 :=
  rectangleBound (l := 39) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_4 : RectangleClaim 7 .empty 11 31 121 33 7 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_5 : RectangleClaim 7 .empty 12 34 121 36 7 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_6 : RectangleClaim 7 .empty 13 37 121 38 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_7 : RectangleClaim 7 .empty 13 39 121 39 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_8 : RectangleClaim 7 .empty 14 40 121 40 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_9 : RectangleClaim 7 .empty 14 41 118 41 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_10 : RectangleClaim 7 .empty 119 41 121 41 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_11 : RectangleClaim 7 .empty 14 42 115 42 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_12 : RectangleClaim 7 .empty 116 42 121 42 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_13 : RectangleClaim 7 .empty 15 43 112 43 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_14 : RectangleClaim 7 .empty 113 43 121 43 7 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_15 : RectangleClaim 7 .empty 15 44 109 44 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_16 : RectangleClaim 7 .empty 110 44 121 44 7 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_17 : RectangleClaim 7 .empty 15 45 107 45 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_18 : RectangleClaim 7 .empty 108 45 121 45 7 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_19 : RectangleClaim 7 .empty 16 46 105 46 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_20 : RectangleClaim 7 .empty 106 46 121 46 7 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_21 : RectangleClaim 7 .empty 16 47 102 47 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_22 : RectangleClaim 7 .empty 103 47 120 47 7 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_23 : PointClaim 7 .empty 121 47 7 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_24 : RectangleClaim 7 .empty 16 48 100 48 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_25 : RectangleClaim 7 .empty 101 48 118 48 7 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_26 : PointClaim 7 .empty 119 48 7 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_27 : PointClaim 7 .empty 120 48 7 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_28 : PointClaim 7 .empty 121 48 7 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_29 : RectangleClaim 7 .empty 17 49 98 49 7 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_30 : RectangleClaim 7 .empty 99 49 115 49 7 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_31 : PointClaim 7 .empty 116 49 7 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_32 : PointClaim 7 .empty 117 49 7 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_33 : RectangleClaim 7 .empty 118 49 118 49 7 :=
  rectangleBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_34 : PointClaim 7 .empty 119 49 7 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_35 : PointClaim 7 .empty 120 49 7 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_36 : PointClaim 7 .empty 121 49 7 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

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
    by_cases hB1 : a.b ≤ 118
    · apply r7_25 <;> omega
    by_cases hB2 : a.b ≤ 119
    · apply r7_26 <;> omega
    by_cases hB3 : a.b ≤ 120
    · apply r7_27 <;> omega
    apply r7_28 <;> omega
  by_cases hB0 : a.b ≤ 98
  · apply r7_29 <;> omega
  by_cases hB1 : a.b ≤ 115
  · apply r7_30 <;> omega
  by_cases hB2 : a.b ≤ 116
  · apply r7_31 <;> omega
  by_cases hB3 : a.b ≤ 117
  · apply r7_32 <;> omega
  by_cases hB4 : a.b ≤ 118
  · apply r7_33 <;> omega
  by_cases hB5 : a.b ≤ 119
  · apply r7_34 <;> omega
  by_cases hB6 : a.b ≤ 120
  · apply r7_35 <;> omega
  apply r7_36 <;> omega

private theorem r8_0 : RectangleClaim 8 .empty 8 24 121 24 8 :=
  rectangleBound (l := 32) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_1 : RectangleClaim 8 .empty 9 25 121 27 8 :=
  rectangleBound (l := 32) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_2 : RectangleClaim 8 .empty 10 28 121 30 8 :=
  rectangleBound (l := 39) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_3 : RectangleClaim 8 .empty 11 31 121 33 8 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_4 : RectangleClaim 8 .empty 12 34 121 36 8 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_5 : RectangleClaim 8 .empty 13 37 121 38 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_6 : RectangleClaim 8 .empty 13 39 121 39 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_7 : RectangleClaim 8 .empty 14 40 120 40 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_8 : RectangleClaim 8 .empty 121 40 121 40 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_9 : RectangleClaim 8 .empty 14 41 117 41 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_10 : RectangleClaim 8 .empty 118 41 121 41 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_11 : RectangleClaim 8 .empty 14 42 114 42 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_12 : RectangleClaim 8 .empty 115 42 121 42 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_13 : RectangleClaim 8 .empty 15 43 111 43 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_14 : RectangleClaim 8 .empty 112 43 121 43 8 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_15 : RectangleClaim 8 .empty 15 44 108 44 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_16 : RectangleClaim 8 .empty 109 44 121 44 8 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_17 : RectangleClaim 8 .empty 15 45 106 45 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_18 : RectangleClaim 8 .empty 107 45 121 45 8 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_19 : RectangleClaim 8 .empty 16 46 103 46 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_20 : RectangleClaim 8 .empty 104 46 121 46 8 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_21 : RectangleClaim 8 .empty 16 47 101 47 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_22 : RectangleClaim 8 .empty 102 47 119 47 8 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_23 : PointClaim 8 .empty 120 47 8 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_24 : PointClaim 8 .empty 121 47 8 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_25 : RectangleClaim 8 .empty 16 48 99 48 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_26 : RectangleClaim 8 .empty 100 48 116 48 8 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_27 : PointClaim 8 .empty 117 48 8 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_28 : PointClaim 8 .empty 118 48 8 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_29 : PointClaim 8 .empty 119 48 8 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_30 : PointClaim 8 .empty 120 48 8 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_31 : PointClaim 8 .empty 121 48 8 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_32 : RectangleClaim 8 .empty 17 49 97 49 8 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_33 : RectangleClaim 8 .empty 98 49 114 49 8 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_34 : PointClaim 8 .empty 115 49 8 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_35 : PointClaim 8 .empty 116 49 8 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_36 : PointClaim 8 .empty 117 49 8 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_37 : PointClaim 8 .empty 118 49 8 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_38 : PointClaim 8 .empty 119 49 8 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_39 : PointClaim 8 .empty 120 49 8 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_40 : PointClaim 8 .empty 121 49 8 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r9_0 : RectangleClaim 9 .empty 9 27 121 27 9 :=
  rectangleBound (l := 37) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_1 : RectangleClaim 9 .empty 10 28 121 30 9 :=
  rectangleBound (l := 39) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_2 : RectangleClaim 9 .empty 11 31 121 33 9 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_3 : RectangleClaim 9 .empty 12 34 121 36 9 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_4 : RectangleClaim 9 .empty 13 37 121 38 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_5 : RectangleClaim 9 .empty 13 39 121 39 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_6 : RectangleClaim 9 .empty 14 40 120 40 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_7 : RectangleClaim 9 .empty 121 40 121 40 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_8 : RectangleClaim 9 .empty 14 41 116 41 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_9 : RectangleClaim 9 .empty 117 41 121 41 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_10 : RectangleClaim 9 .empty 14 42 113 42 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_11 : RectangleClaim 9 .empty 114 42 121 42 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_12 : RectangleClaim 9 .empty 15 43 110 43 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_13 : RectangleClaim 9 .empty 111 43 121 43 9 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_14 : RectangleClaim 9 .empty 15 44 108 44 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_15 : RectangleClaim 9 .empty 109 44 121 44 9 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_16 : RectangleClaim 9 .empty 15 45 105 45 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_17 : RectangleClaim 9 .empty 106 45 121 45 9 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_18 : RectangleClaim 9 .empty 16 46 103 46 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_19 : RectangleClaim 9 .empty 104 46 121 46 9 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_20 : RectangleClaim 9 .empty 16 47 100 47 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_21 : RectangleClaim 9 .empty 101 47 118 47 9 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_22 : PointClaim 9 .empty 119 47 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_23 : PointClaim 9 .empty 120 47 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_24 : PointClaim 9 .empty 121 47 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_25 : RectangleClaim 9 .empty 16 48 98 48 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_26 : RectangleClaim 9 .empty 99 48 115 48 9 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_27 : PointClaim 9 .empty 116 48 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_28 : PointClaim 9 .empty 117 48 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_29 : PointClaim 9 .empty 118 48 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_30 : PointClaim 9 .empty 119 48 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_31 : PointClaim 9 .empty 120 48 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_32 : PointClaim 9 .empty 121 48 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_33 : RectangleClaim 9 .empty 17 49 96 49 9 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_34 : RectangleClaim 9 .empty 97 49 113 49 9 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_35 : PointClaim 9 .empty 114 49 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_36 : PointClaim 9 .empty 115 49 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_37 : PointClaim 9 .empty 116 49 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_38 : PointClaim 9 .empty 117 49 9 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_39 : PointClaim 9 .empty 118 49 9 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_40 : PointClaim 9 .empty 119 49 9 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_41 : PointClaim 9 .empty 120 49 9 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_42 : PointClaim 9 .empty 121 49 9 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r10_0 : RectangleClaim 10 .empty 10 30 121 30 10 :=
  rectangleBound (l := 40) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_1 : RectangleClaim 10 .empty 11 31 121 33 10 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_2 : RectangleClaim 10 .empty 12 34 121 36 10 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_3 : RectangleClaim 10 .empty 13 37 121 38 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_4 : RectangleClaim 10 .empty 13 39 121 39 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_5 : RectangleClaim 10 .empty 14 40 120 40 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_6 : RectangleClaim 10 .empty 121 40 121 40 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_7 : RectangleClaim 10 .empty 14 41 116 41 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_8 : RectangleClaim 10 .empty 117 41 121 41 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_9 : RectangleClaim 10 .empty 14 42 113 42 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_10 : RectangleClaim 10 .empty 114 42 121 42 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_11 : RectangleClaim 10 .empty 15 43 110 43 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_12 : RectangleClaim 10 .empty 111 43 121 43 10 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_13 : RectangleClaim 10 .empty 15 44 107 44 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_14 : RectangleClaim 10 .empty 108 44 121 44 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_15 : RectangleClaim 10 .empty 15 45 105 45 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_16 : RectangleClaim 10 .empty 106 45 121 45 10 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_17 : RectangleClaim 10 .empty 16 46 102 46 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_18 : RectangleClaim 10 .empty 103 46 120 46 10 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_19 : PointClaim 10 .empty 121 46 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_20 : RectangleClaim 10 .empty 16 47 100 47 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_21 : RectangleClaim 10 .empty 101 47 117 47 10 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_22 : PointClaim 10 .empty 118 47 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_23 : PointClaim 10 .empty 119 47 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_24 : PointClaim 10 .empty 120 47 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_25 : PointClaim 10 .empty 121 47 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_26 : RectangleClaim 10 .empty 16 48 97 48 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_27 : RectangleClaim 10 .empty 98 48 115 48 10 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_28 : PointClaim 10 .empty 116 48 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_29 : PointClaim 10 .empty 117 48 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_30 : PointClaim 10 .empty 118 48 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_31 : PointClaim 10 .empty 119 48 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_32 : PointClaim 10 .empty 120 48 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_33 : PointClaim 10 .empty 121 48 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_34 : RectangleClaim 10 .empty 17 49 95 49 10 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_35 : RectangleClaim 10 .empty 96 49 112 49 10 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_36 : PointClaim 10 .empty 113 49 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_37 : PointClaim 10 .empty 114 49 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_38 : PointClaim 10 .empty 115 49 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_39 : PointClaim 10 .empty 116 49 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_40 : PointClaim 10 .empty 117 49 10 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_41 : PointClaim 10 .empty 118 49 10 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_42 : PointClaim 10 .empty 119 49 10 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_43 : PointClaim 10 .empty 120 49 10 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_44 : PointClaim 10 .empty 121 49 10 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r11_0 : RectangleClaim 11 .empty 11 33 121 33 11 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_1 : RectangleClaim 11 .empty 12 34 121 36 11 :=
  rectangleBound (l := 41) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_2 : RectangleClaim 11 .empty 13 37 121 38 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_3 : RectangleClaim 11 .empty 13 39 121 39 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_4 : RectangleClaim 11 .empty 14 40 120 40 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_5 : RectangleClaim 11 .empty 121 40 121 40 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_6 : RectangleClaim 11 .empty 14 41 116 41 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_7 : RectangleClaim 11 .empty 117 41 121 41 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_8 : RectangleClaim 11 .empty 14 42 113 42 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_9 : RectangleClaim 11 .empty 114 42 121 42 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_10 : RectangleClaim 11 .empty 15 43 110 43 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_11 : RectangleClaim 11 .empty 111 43 121 43 11 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_12 : RectangleClaim 11 .empty 15 44 107 44 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_13 : RectangleClaim 11 .empty 108 44 121 44 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_14 : RectangleClaim 11 .empty 15 45 105 45 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_15 : RectangleClaim 11 .empty 106 45 120 45 11 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_16 : RectangleClaim 11 .empty 121 45 121 45 11 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_17 : RectangleClaim 11 .empty 16 46 102 46 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_18 : RectangleClaim 11 .empty 103 46 120 46 11 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_19 : PointClaim 11 .empty 121 46 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_20 : RectangleClaim 11 .empty 16 47 99 47 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_21 : RectangleClaim 11 .empty 100 47 117 47 11 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_22 : PointClaim 11 .empty 118 47 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_23 : PointClaim 11 .empty 119 47 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_24 : PointClaim 11 .empty 120 47 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_25 : PointClaim 11 .empty 121 47 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_26 : RectangleClaim 11 .empty 16 48 97 48 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_27 : RectangleClaim 11 .empty 98 48 114 48 11 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_28 : PointClaim 11 .empty 115 48 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_29 : PointClaim 11 .empty 116 48 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_30 : PointClaim 11 .empty 117 48 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_31 : PointClaim 11 .empty 118 48 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_32 : PointClaim 11 .empty 119 48 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_33 : PointClaim 11 .empty 120 48 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_34 : PointClaim 11 .empty 121 48 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_35 : RectangleClaim 11 .empty 17 49 95 49 11 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_36 : RectangleClaim 11 .empty 96 49 112 49 11 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_37 : PointClaim 11 .empty 113 49 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_38 : PointClaim 11 .empty 114 49 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_39 : PointClaim 11 .empty 115 49 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_40 : PointClaim 11 .empty 116 49 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_41 : PointClaim 11 .empty 117 49 11 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_42 : PointClaim 11 .empty 118 49 11 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_43 : PointClaim 11 .empty 119 49 11 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_44 : PointClaim 11 .empty 120 49 11 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_45 : PointClaim 11 .empty 121 49 11 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r12_0 : RectangleClaim 12 .empty 12 36 121 36 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_1 : RectangleClaim 12 .empty 13 37 121 38 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_2 : RectangleClaim 12 .empty 13 39 121 39 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_3 : RectangleClaim 12 .empty 14 40 120 40 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_4 : RectangleClaim 12 .empty 121 40 121 40 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_5 : RectangleClaim 12 .empty 14 41 117 41 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_6 : RectangleClaim 12 .empty 118 41 121 41 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_7 : RectangleClaim 12 .empty 14 42 113 42 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_8 : RectangleClaim 12 .empty 114 42 121 42 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_9 : RectangleClaim 12 .empty 15 43 110 43 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_10 : RectangleClaim 12 .empty 111 43 121 43 12 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_11 : RectangleClaim 12 .empty 15 44 107 44 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_12 : RectangleClaim 12 .empty 108 44 121 44 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_13 : RectangleClaim 12 .empty 15 45 105 45 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_14 : RectangleClaim 12 .empty 106 45 121 45 12 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_15 : RectangleClaim 12 .empty 16 46 102 46 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_16 : RectangleClaim 12 .empty 103 46 120 46 12 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_17 : PointClaim 12 .empty 121 46 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_18 : RectangleClaim 12 .empty 16 47 99 47 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_19 : RectangleClaim 12 .empty 100 47 117 47 12 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_20 : PointClaim 12 .empty 118 47 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_21 : PointClaim 12 .empty 119 47 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_22 : PointClaim 12 .empty 120 47 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_23 : PointClaim 12 .empty 121 47 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_24 : RectangleClaim 12 .empty 16 48 97 48 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_25 : RectangleClaim 12 .empty 98 48 114 48 12 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_26 : PointClaim 12 .empty 115 48 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_27 : PointClaim 12 .empty 116 48 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_28 : PointClaim 12 .empty 117 48 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_29 : PointClaim 12 .empty 118 48 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_30 : PointClaim 12 .empty 119 48 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_31 : PointClaim 12 .empty 120 48 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_32 : PointClaim 12 .empty 121 48 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_33 : RectangleClaim 12 .empty 17 49 95 49 12 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_34 : RectangleClaim 12 .empty 96 49 112 49 12 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_35 : PointClaim 12 .empty 113 49 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_36 : PointClaim 12 .empty 114 49 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_37 : PointClaim 12 .empty 115 49 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_38 : PointClaim 12 .empty 116 49 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_39 : PointClaim 12 .empty 117 49 12 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_40 : PointClaim 12 .empty 118 49 12 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_41 : PointClaim 12 .empty 119 49 12 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_42 : PointClaim 12 .empty 120 49 12 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_43 : PointClaim 12 .empty 121 49 12 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

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

private theorem r13_0 : RectangleClaim 13 .empty 13 39 121 39 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_1 : RectangleClaim 13 .empty 14 40 120 40 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_2 : RectangleClaim 13 .empty 121 40 121 40 13 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_3 : RectangleClaim 13 .empty 14 41 117 41 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_4 : RectangleClaim 13 .empty 118 41 121 41 13 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_5 : RectangleClaim 13 .empty 14 42 114 42 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_6 : RectangleClaim 13 .empty 115 42 121 42 13 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_7 : RectangleClaim 13 .empty 15 43 111 43 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_8 : RectangleClaim 13 .empty 112 43 121 43 13 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_9 : RectangleClaim 13 .empty 15 44 108 44 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_10 : RectangleClaim 13 .empty 109 44 121 44 13 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_11 : RectangleClaim 13 .empty 15 45 105 45 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_12 : RectangleClaim 13 .empty 106 45 121 45 13 :=
  rectangleBound (l := 48) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_13 : RectangleClaim 13 .empty 16 46 102 46 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_14 : RectangleClaim 13 .empty 103 46 120 46 13 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_15 : PointClaim 13 .empty 121 46 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_16 : RectangleClaim 13 .empty 16 47 100 47 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_17 : RectangleClaim 13 .empty 101 47 117 47 13 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_18 : PointClaim 13 .empty 118 47 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_19 : PointClaim 13 .empty 119 47 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_20 : PointClaim 13 .empty 120 47 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_21 : PointClaim 13 .empty 121 47 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_22 : RectangleClaim 13 .empty 16 48 97 48 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_23 : RectangleClaim 13 .empty 98 48 115 48 13 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_24 : PointClaim 13 .empty 116 48 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_25 : PointClaim 13 .empty 117 48 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_26 : PointClaim 13 .empty 118 48 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_27 : PointClaim 13 .empty 119 48 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_28 : PointClaim 13 .empty 120 48 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_29 : PointClaim 13 .empty 121 48 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_30 : RectangleClaim 13 .empty 17 49 95 49 13 :=
  rectangleBound (l := 42) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_31 : RectangleClaim 13 .empty 96 49 112 49 13 :=
  rectangleBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_32 : PointClaim 13 .empty 113 49 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_33 : PointClaim 13 .empty 114 49 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_34 : PointClaim 13 .empty 115 49 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_35 : PointClaim 13 .empty 116 49 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_36 : PointClaim 13 .empty 117 49 13 :=
  pointBound (l := 49) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_37 : PointClaim 13 .empty 118 49 13 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_38 : PointClaim 13 .empty 119 49 13 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_39 : PointClaim 13 .empty 120 49 13 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r13_40 : PointClaim 13 .empty 121 49 13 :=
  pointBound (l := 50) (by decide) (by decide +kernel) (by decide +kernel)

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
  · by_cases hB0 : a.b ≤ 100
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
