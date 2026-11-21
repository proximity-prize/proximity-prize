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

private theorem r1_0 : RectangleClaim 2 .one 1 3 122 3 1 :=
  rectangleBound (l := 1)

private theorem r1_1 : RectangleClaim 2 .one 2 4 64 4 1 :=
  rectangleBound (l := 1)

private theorem r1_2 : RectangleClaim 2 .one 65 4 122 4 1 :=
  rectangleBound (l := 2)

private theorem r1_3 : RectangleClaim 2 .one 2 5 122 6 1 :=
  rectangleBound (l := 7)

private theorem r1_4 : RectangleClaim 2 .one 3 7 122 9 1 :=
  rectangleBound (l := 22)

private theorem r1_5 : RectangleClaim 2 .one 4 10 122 12 1 :=
  rectangleBound (l := 35)

private theorem r1_6 : RectangleClaim 2 .one 5 13 122 15 1 :=
  rectangleBound (l := 42)

private theorem r1_7 : RectangleClaim 2 .one 6 16 122 18 1 :=
  rectangleBound (l := 47)

private theorem r1_8 : RectangleClaim 2 .one 7 19 122 21 1 :=
  rectangleBound (l := 50)

private theorem r1_9 : RectangleClaim 2 .one 8 22 122 24 1 :=
  rectangleBound (l := 52)

private theorem r1_10 : RectangleClaim 2 .one 9 25 122 27 1 :=
  rectangleBound (l := 54)

private theorem r1_11 : RectangleClaim 2 .one 10 28 122 30 1 :=
  rectangleBound (l := 56)

private theorem r1_12 : RectangleClaim 2 .one 11 31 122 33 1 :=
  rectangleBound (l := 56)

private theorem r1_13 : RectangleClaim 2 .one 12 34 122 36 1 :=
  rectangleBound (l := 56)

private theorem r1_14 : RectangleClaim 2 .one 13 37 122 39 1 :=
  rectangleBound (l := 56)

private theorem r1_15 : RectangleClaim 2 .one 14 40 122 42 1 :=
  rectangleBound (l := 56)

private theorem r1_16 : RectangleClaim 2 .one 15 43 122 45 1 :=
  rectangleBound (l := 56)

private theorem r1_17 : RectangleClaim 2 .one 16 46 122 47 1 :=
  rectangleBound (l := 56)

private theorem exact1 (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 3
  · apply r1_0 <;> omega
  by_cases hJ1 : a.j ≤ 4
  · by_cases hB0 : a.b ≤ 64
    · apply r1_1 <;> omega
    apply r1_2 <;> omega
  by_cases hJ2 : a.j ≤ 6
  · apply r1_3 <;> omega
  by_cases hJ3 : a.j ≤ 9
  · apply r1_4 <;> omega
  by_cases hJ4 : a.j ≤ 12
  · apply r1_5 <;> omega
  by_cases hJ5 : a.j ≤ 15
  · apply r1_6 <;> omega
  by_cases hJ6 : a.j ≤ 18
  · apply r1_7 <;> omega
  by_cases hJ7 : a.j ≤ 21
  · apply r1_8 <;> omega
  by_cases hJ8 : a.j ≤ 24
  · apply r1_9 <;> omega
  by_cases hJ9 : a.j ≤ 27
  · apply r1_10 <;> omega
  by_cases hJ10 : a.j ≤ 30
  · apply r1_11 <;> omega
  by_cases hJ11 : a.j ≤ 33
  · apply r1_12 <;> omega
  by_cases hJ12 : a.j ≤ 36
  · apply r1_13 <;> omega
  by_cases hJ13 : a.j ≤ 39
  · apply r1_14 <;> omega
  by_cases hJ14 : a.j ≤ 42
  · apply r1_15 <;> omega
  by_cases hJ15 : a.j ≤ 45
  · apply r1_16 <;> omega
  apply r1_17 <;> omega

private theorem r2_0 : RectangleClaim 3 .one 2 6 122 6 2 :=
  rectangleBound (l := 16)

private theorem r2_1 : RectangleClaim 3 .one 3 7 122 9 2 :=
  rectangleBound (l := 22)

private theorem r2_2 : RectangleClaim 3 .one 4 10 122 12 2 :=
  rectangleBound (l := 35)

private theorem r2_3 : RectangleClaim 3 .one 5 13 122 15 2 :=
  rectangleBound (l := 42)

private theorem r2_4 : RectangleClaim 3 .one 6 16 122 18 2 :=
  rectangleBound (l := 47)

private theorem r2_5 : RectangleClaim 3 .one 7 19 122 21 2 :=
  rectangleBound (l := 50)

private theorem r2_6 : RectangleClaim 3 .one 8 22 122 24 2 :=
  rectangleBound (l := 52)

private theorem r2_7 : RectangleClaim 3 .one 9 25 122 27 2 :=
  rectangleBound (l := 54)

private theorem r2_8 : RectangleClaim 3 .one 10 28 122 30 2 :=
  rectangleBound (l := 56)

private theorem r2_9 : RectangleClaim 3 .one 11 31 122 33 2 :=
  rectangleBound (l := 56)

private theorem r2_10 : RectangleClaim 3 .one 12 34 122 36 2 :=
  rectangleBound (l := 56)

private theorem r2_11 : RectangleClaim 3 .one 13 37 122 39 2 :=
  rectangleBound (l := 56)

private theorem r2_12 : RectangleClaim 3 .one 14 40 122 42 2 :=
  rectangleBound (l := 56)

private theorem r2_13 : RectangleClaim 3 .one 15 43 122 45 2 :=
  rectangleBound (l := 56)

private theorem r2_14 : RectangleClaim 3 .one 16 46 122 47 2 :=
  rectangleBound (l := 56)

private theorem exact2 (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j := by
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
  by_cases hJ12 : a.j ≤ 42
  · apply r2_12 <;> omega
  by_cases hJ13 : a.j ≤ 45
  · apply r2_13 <;> omega
  apply r2_14 <;> omega

private theorem r3_0 : RectangleClaim 4 .one 3 9 122 9 3 :=
  rectangleBound (l := 31)

private theorem r3_1 : RectangleClaim 4 .one 4 10 122 12 3 :=
  rectangleBound (l := 35)

private theorem r3_2 : RectangleClaim 4 .one 5 13 122 15 3 :=
  rectangleBound (l := 42)

private theorem r3_3 : RectangleClaim 4 .one 6 16 122 18 3 :=
  rectangleBound (l := 47)

private theorem r3_4 : RectangleClaim 4 .one 7 19 122 21 3 :=
  rectangleBound (l := 50)

private theorem r3_5 : RectangleClaim 4 .one 8 22 122 24 3 :=
  rectangleBound (l := 52)

private theorem r3_6 : RectangleClaim 4 .one 9 25 122 27 3 :=
  rectangleBound (l := 54)

private theorem r3_7 : RectangleClaim 4 .one 10 28 122 30 3 :=
  rectangleBound (l := 56)

private theorem r3_8 : RectangleClaim 4 .one 11 31 122 33 3 :=
  rectangleBound (l := 56)

private theorem r3_9 : RectangleClaim 4 .one 12 34 122 36 3 :=
  rectangleBound (l := 56)

private theorem r3_10 : RectangleClaim 4 .one 13 37 122 39 3 :=
  rectangleBound (l := 56)

private theorem r3_11 : RectangleClaim 4 .one 14 40 122 42 3 :=
  rectangleBound (l := 56)

private theorem r3_12 : RectangleClaim 4 .one 15 43 122 45 3 :=
  rectangleBound (l := 56)

private theorem r3_13 : RectangleClaim 4 .one 16 46 122 47 3 :=
  rectangleBound (l := 56)

private theorem exact3 (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
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
  by_cases hJ12 : a.j ≤ 45
  · apply r3_12 <;> omega
  apply r3_13 <;> omega

private theorem r4_0 : RectangleClaim 5 .one 4 12 122 12 4 :=
  rectangleBound (l := 40)

private theorem r4_1 : RectangleClaim 5 .one 5 13 122 15 4 :=
  rectangleBound (l := 42)

private theorem r4_2 : RectangleClaim 5 .one 6 16 122 18 4 :=
  rectangleBound (l := 47)

private theorem r4_3 : RectangleClaim 5 .one 7 19 122 21 4 :=
  rectangleBound (l := 50)

private theorem r4_4 : RectangleClaim 5 .one 8 22 122 24 4 :=
  rectangleBound (l := 52)

private theorem r4_5 : RectangleClaim 5 .one 9 25 122 27 4 :=
  rectangleBound (l := 54)

private theorem r4_6 : RectangleClaim 5 .one 10 28 122 30 4 :=
  rectangleBound (l := 56)

private theorem r4_7 : RectangleClaim 5 .one 11 31 122 33 4 :=
  rectangleBound (l := 56)

private theorem r4_8 : RectangleClaim 5 .one 12 34 122 36 4 :=
  rectangleBound (l := 56)

private theorem r4_9 : RectangleClaim 5 .one 13 37 122 39 4 :=
  rectangleBound (l := 56)

private theorem r4_10 : RectangleClaim 5 .one 14 40 122 42 4 :=
  rectangleBound (l := 56)

private theorem r4_11 : RectangleClaim 5 .one 15 43 122 45 4 :=
  rectangleBound (l := 56)

private theorem r4_12 : RectangleClaim 5 .one 16 46 122 47 4 :=
  rectangleBound (l := 56)

private theorem exact4 (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
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
  by_cases hJ10 : a.j ≤ 42
  · apply r4_10 <;> omega
  by_cases hJ11 : a.j ≤ 45
  · apply r4_11 <;> omega
  apply r4_12 <;> omega

private theorem r5_0 : RectangleClaim 6 .one 5 15 122 15 5 :=
  rectangleBound (l := 45)

private theorem r5_1 : RectangleClaim 6 .one 6 16 122 18 5 :=
  rectangleBound (l := 47)

private theorem r5_2 : RectangleClaim 6 .one 7 19 122 21 5 :=
  rectangleBound (l := 50)

private theorem r5_3 : RectangleClaim 6 .one 8 22 122 24 5 :=
  rectangleBound (l := 52)

private theorem r5_4 : RectangleClaim 6 .one 9 25 122 27 5 :=
  rectangleBound (l := 54)

private theorem r5_5 : RectangleClaim 6 .one 10 28 122 30 5 :=
  rectangleBound (l := 56)

private theorem r5_6 : RectangleClaim 6 .one 11 31 122 33 5 :=
  rectangleBound (l := 56)

private theorem r5_7 : RectangleClaim 6 .one 12 34 122 36 5 :=
  rectangleBound (l := 56)

private theorem r5_8 : RectangleClaim 6 .one 13 37 122 39 5 :=
  rectangleBound (l := 56)

private theorem r5_9 : RectangleClaim 6 .one 14 40 122 42 5 :=
  rectangleBound (l := 56)

private theorem r5_10 : RectangleClaim 6 .one 15 43 122 45 5 :=
  rectangleBound (l := 56)

private theorem r5_11 : RectangleClaim 6 .one 16 46 122 47 5 :=
  rectangleBound (l := 56)

private theorem exact5 (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
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
  by_cases hJ9 : a.j ≤ 42
  · apply r5_9 <;> omega
  by_cases hJ10 : a.j ≤ 45
  · apply r5_10 <;> omega
  apply r5_11 <;> omega

private theorem r6_0 : RectangleClaim 7 .one 6 18 122 18 6 :=
  rectangleBound (l := 49)

private theorem r6_1 : RectangleClaim 7 .one 7 19 122 21 6 :=
  rectangleBound (l := 50)

private theorem r6_2 : RectangleClaim 7 .one 8 22 122 24 6 :=
  rectangleBound (l := 52)

private theorem r6_3 : RectangleClaim 7 .one 9 25 122 27 6 :=
  rectangleBound (l := 54)

private theorem r6_4 : RectangleClaim 7 .one 10 28 122 30 6 :=
  rectangleBound (l := 56)

private theorem r6_5 : RectangleClaim 7 .one 11 31 122 33 6 :=
  rectangleBound (l := 56)

private theorem r6_6 : RectangleClaim 7 .one 12 34 122 36 6 :=
  rectangleBound (l := 56)

private theorem r6_7 : RectangleClaim 7 .one 13 37 122 39 6 :=
  rectangleBound (l := 56)

private theorem r6_8 : RectangleClaim 7 .one 14 40 122 42 6 :=
  rectangleBound (l := 56)

private theorem r6_9 : RectangleClaim 7 .one 15 43 122 45 6 :=
  rectangleBound (l := 56)

private theorem r6_10 : RectangleClaim 7 .one 16 46 122 47 6 :=
  rectangleBound (l := 56)

private theorem exact6 (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
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
  by_cases hJ8 : a.j ≤ 42
  · apply r6_8 <;> omega
  by_cases hJ9 : a.j ≤ 45
  · apply r6_9 <;> omega
  apply r6_10 <;> omega

private theorem r7_0 : RectangleClaim 8 .one 7 21 122 21 7 :=
  rectangleBound (l := 52)

private theorem r7_1 : RectangleClaim 8 .one 8 22 122 24 7 :=
  rectangleBound (l := 52)

private theorem r7_2 : RectangleClaim 8 .one 9 25 122 27 7 :=
  rectangleBound (l := 54)

private theorem r7_3 : RectangleClaim 8 .one 10 28 122 30 7 :=
  rectangleBound (l := 56)

private theorem r7_4 : RectangleClaim 8 .one 11 31 122 33 7 :=
  rectangleBound (l := 56)

private theorem r7_5 : RectangleClaim 8 .one 12 34 122 36 7 :=
  rectangleBound (l := 56)

private theorem r7_6 : RectangleClaim 8 .one 13 37 122 39 7 :=
  rectangleBound (l := 56)

private theorem r7_7 : RectangleClaim 8 .one 14 40 122 42 7 :=
  rectangleBound (l := 56)

private theorem r7_8 : RectangleClaim 8 .one 15 43 122 45 7 :=
  rectangleBound (l := 56)

private theorem r7_9 : RectangleClaim 8 .one 16 46 122 47 7 :=
  rectangleBound (l := 56)

private theorem exact7 (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
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
  by_cases hJ7 : a.j ≤ 42
  · apply r7_7 <;> omega
  by_cases hJ8 : a.j ≤ 45
  · apply r7_8 <;> omega
  apply r7_9 <;> omega

private theorem r8_0 : RectangleClaim 9 .one 8 24 122 24 8 :=
  rectangleBound (l := 54)

private theorem r8_1 : RectangleClaim 9 .one 9 25 122 27 8 :=
  rectangleBound (l := 54)

private theorem r8_2 : RectangleClaim 9 .one 10 28 122 30 8 :=
  rectangleBound (l := 56)

private theorem r8_3 : RectangleClaim 9 .one 11 31 122 33 8 :=
  rectangleBound (l := 56)

private theorem r8_4 : RectangleClaim 9 .one 12 34 122 36 8 :=
  rectangleBound (l := 56)

private theorem r8_5 : RectangleClaim 9 .one 13 37 122 39 8 :=
  rectangleBound (l := 56)

private theorem r8_6 : RectangleClaim 9 .one 14 40 122 42 8 :=
  rectangleBound (l := 56)

private theorem r8_7 : RectangleClaim 9 .one 15 43 122 45 8 :=
  rectangleBound (l := 56)

private theorem r8_8 : RectangleClaim 9 .one 16 46 122 46 8 :=
  rectangleBound (l := 56)

private theorem r8_9 : RectangleClaim 9 .one 16 47 122 47 8 :=
  rectangleBound (l := 56)

private theorem exact8 (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
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
  by_cases hJ6 : a.j ≤ 42
  · apply r8_6 <;> omega
  by_cases hJ7 : a.j ≤ 45
  · apply r8_7 <;> omega
  by_cases hJ8 : a.j ≤ 46
  · apply r8_8 <;> omega
  apply r8_9 <;> omega

private theorem r9_0 : RectangleClaim 10 .one 9 27 122 27 9 :=
  rectangleBound (l := 55)

private theorem r9_1 : RectangleClaim 10 .one 10 28 122 30 9 :=
  rectangleBound (l := 56)

private theorem r9_2 : RectangleClaim 10 .one 11 31 122 33 9 :=
  rectangleBound (l := 56)

private theorem r9_3 : RectangleClaim 10 .one 12 34 122 36 9 :=
  rectangleBound (l := 56)

private theorem r9_4 : RectangleClaim 10 .one 13 37 122 39 9 :=
  rectangleBound (l := 56)

private theorem r9_5 : RectangleClaim 10 .one 14 40 122 42 9 :=
  rectangleBound (l := 56)

private theorem r9_6 : RectangleClaim 10 .one 15 43 122 45 9 :=
  rectangleBound (l := 56)

private theorem r9_7 : RectangleClaim 10 .one 16 46 122 46 9 :=
  rectangleBound (l := 56)

private theorem r9_8 : RectangleClaim 10 .one 16 47 122 47 9 :=
  rectangleBound (l := 56)

private theorem exact9 (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
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
  by_cases hJ5 : a.j ≤ 42
  · apply r9_5 <;> omega
  by_cases hJ6 : a.j ≤ 45
  · apply r9_6 <;> omega
  by_cases hJ7 : a.j ≤ 46
  · apply r9_7 <;> omega
  apply r9_8 <;> omega

private theorem r10_0 : RectangleClaim 11 .one 10 30 122 30 10 :=
  rectangleBound (l := 56)

private theorem r10_1 : RectangleClaim 11 .one 11 31 122 33 10 :=
  rectangleBound (l := 56)

private theorem r10_2 : RectangleClaim 11 .one 12 34 122 36 10 :=
  rectangleBound (l := 56)

private theorem r10_3 : RectangleClaim 11 .one 13 37 122 39 10 :=
  rectangleBound (l := 56)

private theorem r10_4 : RectangleClaim 11 .one 14 40 122 42 10 :=
  rectangleBound (l := 56)

private theorem r10_5 : RectangleClaim 11 .one 15 43 122 45 10 :=
  rectangleBound (l := 56)

private theorem r10_6 : RectangleClaim 11 .one 16 46 122 46 10 :=
  rectangleBound (l := 56)

private theorem r10_7 : RectangleClaim 11 .one 16 47 122 47 10 :=
  rectangleBound (l := 56)

private theorem exact10 (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
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
  by_cases hJ4 : a.j ≤ 42
  · apply r10_4 <;> omega
  by_cases hJ5 : a.j ≤ 45
  · apply r10_5 <;> omega
  by_cases hJ6 : a.j ≤ 46
  · apply r10_6 <;> omega
  apply r10_7 <;> omega

private theorem r11_0 : RectangleClaim 12 .one 11 33 122 33 11 :=
  rectangleBound (l := 56)

private theorem r11_1 : RectangleClaim 12 .one 12 34 122 36 11 :=
  rectangleBound (l := 56)

private theorem r11_2 : RectangleClaim 12 .one 13 37 122 39 11 :=
  rectangleBound (l := 56)

private theorem r11_3 : RectangleClaim 12 .one 14 40 122 42 11 :=
  rectangleBound (l := 56)

private theorem r11_4 : RectangleClaim 12 .one 15 43 122 45 11 :=
  rectangleBound (l := 56)

private theorem r11_5 : RectangleClaim 12 .one 16 46 122 46 11 :=
  rectangleBound (l := 56)

private theorem r11_6 : RectangleClaim 12 .one 16 47 122 47 11 :=
  rectangleBound (l := 56)

private theorem exact11 (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 33
  · apply r11_0 <;> omega
  by_cases hJ1 : a.j ≤ 36
  · apply r11_1 <;> omega
  by_cases hJ2 : a.j ≤ 39
  · apply r11_2 <;> omega
  by_cases hJ3 : a.j ≤ 42
  · apply r11_3 <;> omega
  by_cases hJ4 : a.j ≤ 45
  · apply r11_4 <;> omega
  by_cases hJ5 : a.j ≤ 46
  · apply r11_5 <;> omega
  apply r11_6 <;> omega

private theorem r12_0 : RectangleClaim 13 .one 12 36 122 36 12 :=
  rectangleBound (l := 56)

private theorem r12_1 : RectangleClaim 13 .one 13 37 122 39 12 :=
  rectangleBound (l := 56)

private theorem r12_2 : RectangleClaim 13 .one 14 40 122 42 12 :=
  rectangleBound (l := 56)

private theorem r12_3 : RectangleClaim 13 .one 15 43 122 45 12 :=
  rectangleBound (l := 56)

private theorem r12_4 : RectangleClaim 13 .one 16 46 122 46 12 :=
  rectangleBound (l := 56)

private theorem r12_5 : RectangleClaim 13 .one 16 47 122 47 12 :=
  rectangleBound (l := 56)

private theorem exact12 (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 36
  · apply r12_0 <;> omega
  by_cases hJ1 : a.j ≤ 39
  · apply r12_1 <;> omega
  by_cases hJ2 : a.j ≤ 42
  · apply r12_2 <;> omega
  by_cases hJ3 : a.j ≤ 45
  · apply r12_3 <;> omega
  by_cases hJ4 : a.j ≤ 46
  · apply r12_4 <;> omega
  apply r12_5 <;> omega

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one).plus a) (fullCap top)) :
    physicalPrice a (order .one a) ≤ allowance top .one a.j := by
  change 1+a.b ≤ 123 ∧ 3+a.j ≤ 50 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb, hj, ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 122 := by omega
  have hj' : a.j ≤ 47 := by omega
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
