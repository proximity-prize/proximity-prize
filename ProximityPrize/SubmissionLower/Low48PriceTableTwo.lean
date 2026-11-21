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

private theorem r1_0 : RectangleClaim 3 .two 1 3 121 3 1 :=
  rectangleBound (l := 38)

private theorem r1_1 : RectangleClaim 3 .two 2 4 121 6 1 :=
  rectangleBound (l := 48)

private theorem r1_2 : RectangleClaim 3 .two 3 7 121 9 1 :=
  rectangleBound (l := 65)

private theorem r1_3 : RectangleClaim 3 .two 4 10 121 12 1 :=
  rectangleBound (l := 72)

private theorem r1_4 : RectangleClaim 3 .two 5 13 121 15 1 :=
  rectangleBound (l := 77)

private theorem r1_5 : RectangleClaim 3 .two 6 16 121 18 1 :=
  rectangleBound (l := 80)

private theorem r1_6 : RectangleClaim 3 .two 7 19 121 21 1 :=
  rectangleBound (l := 82)

private theorem r1_7 : RectangleClaim 3 .two 8 22 121 24 1 :=
  rectangleBound (l := 84)

private theorem r1_8 : RectangleClaim 3 .two 9 25 121 27 1 :=
  rectangleBound (l := 85)

private theorem r1_9 : RectangleClaim 3 .two 10 28 121 30 1 :=
  rectangleBound (l := 86)

private theorem r1_10 : RectangleClaim 3 .two 11 31 121 33 1 :=
  rectangleBound (l := 87)

private theorem r1_11 : RectangleClaim 3 .two 12 34 121 36 1 :=
  rectangleBound (l := 88)

private theorem r1_12 : RectangleClaim 3 .two 13 37 121 39 1 :=
  rectangleBound (l := 88)

private theorem r1_13 : RectangleClaim 3 .two 14 40 121 42 1 :=
  rectangleBound (l := 89)

private theorem r1_14 : RectangleClaim 3 .two 15 43 121 44 1 :=
  rectangleBound (l := 89)

private theorem exact1 (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 3
  · apply r1_0 <;> omega
  by_cases hJ1 : a.j ≤ 6
  · apply r1_1 <;> omega
  by_cases hJ2 : a.j ≤ 9
  · apply r1_2 <;> omega
  by_cases hJ3 : a.j ≤ 12
  · apply r1_3 <;> omega
  by_cases hJ4 : a.j ≤ 15
  · apply r1_4 <;> omega
  by_cases hJ5 : a.j ≤ 18
  · apply r1_5 <;> omega
  by_cases hJ6 : a.j ≤ 21
  · apply r1_6 <;> omega
  by_cases hJ7 : a.j ≤ 24
  · apply r1_7 <;> omega
  by_cases hJ8 : a.j ≤ 27
  · apply r1_8 <;> omega
  by_cases hJ9 : a.j ≤ 30
  · apply r1_9 <;> omega
  by_cases hJ10 : a.j ≤ 33
  · apply r1_10 <;> omega
  by_cases hJ11 : a.j ≤ 36
  · apply r1_11 <;> omega
  by_cases hJ12 : a.j ≤ 39
  · apply r1_12 <;> omega
  by_cases hJ13 : a.j ≤ 42
  · apply r1_13 <;> omega
  apply r1_14 <;> omega

private theorem r2_0 : RectangleClaim 4 .two 2 6 121 6 2 :=
  rectangleBound (l := 61)

private theorem r2_1 : RectangleClaim 4 .two 3 7 121 9 2 :=
  rectangleBound (l := 65)

private theorem r2_2 : RectangleClaim 4 .two 4 10 121 12 2 :=
  rectangleBound (l := 72)

private theorem r2_3 : RectangleClaim 4 .two 5 13 121 15 2 :=
  rectangleBound (l := 77)

private theorem r2_4 : RectangleClaim 4 .two 6 16 121 18 2 :=
  rectangleBound (l := 80)

private theorem r2_5 : RectangleClaim 4 .two 7 19 121 21 2 :=
  rectangleBound (l := 82)

private theorem r2_6 : RectangleClaim 4 .two 8 22 121 24 2 :=
  rectangleBound (l := 84)

private theorem r2_7 : RectangleClaim 4 .two 9 25 121 27 2 :=
  rectangleBound (l := 85)

private theorem r2_8 : RectangleClaim 4 .two 10 28 121 30 2 :=
  rectangleBound (l := 86)

private theorem r2_9 : RectangleClaim 4 .two 11 31 121 33 2 :=
  rectangleBound (l := 87)

private theorem r2_10 : RectangleClaim 4 .two 12 34 121 36 2 :=
  rectangleBound (l := 88)

private theorem r2_11 : RectangleClaim 4 .two 13 37 121 39 2 :=
  rectangleBound (l := 88)

private theorem r2_12 : RectangleClaim 4 .two 14 40 121 42 2 :=
  rectangleBound (l := 89)

private theorem r2_13 : RectangleClaim 4 .two 15 43 121 44 2 :=
  rectangleBound (l := 89)

private theorem exact2 (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
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
  by_cases hJ12 : a.j ≤ 42
  · apply r2_12 <;> omega
  apply r2_13 <;> omega

private theorem r3_0 : RectangleClaim 5 .two 3 9 121 9 3 :=
  rectangleBound (l := 70)

private theorem r3_1 : RectangleClaim 5 .two 4 10 121 12 3 :=
  rectangleBound (l := 72)

private theorem r3_2 : RectangleClaim 5 .two 5 13 121 15 3 :=
  rectangleBound (l := 77)

private theorem r3_3 : RectangleClaim 5 .two 6 16 121 18 3 :=
  rectangleBound (l := 80)

private theorem r3_4 : RectangleClaim 5 .two 7 19 121 21 3 :=
  rectangleBound (l := 82)

private theorem r3_5 : RectangleClaim 5 .two 8 22 121 24 3 :=
  rectangleBound (l := 84)

private theorem r3_6 : RectangleClaim 5 .two 9 25 121 27 3 :=
  rectangleBound (l := 85)

private theorem r3_7 : RectangleClaim 5 .two 10 28 121 30 3 :=
  rectangleBound (l := 86)

private theorem r3_8 : RectangleClaim 5 .two 11 31 121 33 3 :=
  rectangleBound (l := 87)

private theorem r3_9 : RectangleClaim 5 .two 12 34 121 36 3 :=
  rectangleBound (l := 88)

private theorem r3_10 : RectangleClaim 5 .two 13 37 121 39 3 :=
  rectangleBound (l := 88)

private theorem r3_11 : RectangleClaim 5 .two 14 40 121 42 3 :=
  rectangleBound (l := 89)

private theorem r3_12 : RectangleClaim 5 .two 15 43 121 44 3 :=
  rectangleBound (l := 89)

private theorem exact3 (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
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
  by_cases hJ10 : a.j ≤ 39
  · apply r3_10 <;> omega
  by_cases hJ11 : a.j ≤ 42
  · apply r3_11 <;> omega
  apply r3_12 <;> omega

private theorem r4_0 : RectangleClaim 6 .two 4 12 121 12 4 :=
  rectangleBound (l := 76)

private theorem r4_1 : RectangleClaim 6 .two 5 13 121 15 4 :=
  rectangleBound (l := 77)

private theorem r4_2 : RectangleClaim 6 .two 6 16 121 18 4 :=
  rectangleBound (l := 80)

private theorem r4_3 : RectangleClaim 6 .two 7 19 121 21 4 :=
  rectangleBound (l := 82)

private theorem r4_4 : RectangleClaim 6 .two 8 22 121 24 4 :=
  rectangleBound (l := 84)

private theorem r4_5 : RectangleClaim 6 .two 9 25 121 27 4 :=
  rectangleBound (l := 85)

private theorem r4_6 : RectangleClaim 6 .two 10 28 121 30 4 :=
  rectangleBound (l := 86)

private theorem r4_7 : RectangleClaim 6 .two 11 31 121 33 4 :=
  rectangleBound (l := 87)

private theorem r4_8 : RectangleClaim 6 .two 12 34 121 36 4 :=
  rectangleBound (l := 88)

private theorem r4_9 : RectangleClaim 6 .two 13 37 121 39 4 :=
  rectangleBound (l := 88)

private theorem r4_10 : RectangleClaim 6 .two 14 40 121 42 4 :=
  rectangleBound (l := 89)

private theorem r4_11 : RectangleClaim 6 .two 15 43 121 44 4 :=
  rectangleBound (l := 89)

private theorem exact4 (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
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
  by_cases hJ9 : a.j ≤ 39
  · apply r4_9 <;> omega
  by_cases hJ10 : a.j ≤ 42
  · apply r4_10 <;> omega
  apply r4_11 <;> omega

private theorem r5_0 : RectangleClaim 7 .two 5 15 121 15 5 :=
  rectangleBound (l := 79)

private theorem r5_1 : RectangleClaim 7 .two 6 16 121 18 5 :=
  rectangleBound (l := 80)

private theorem r5_2 : RectangleClaim 7 .two 7 19 121 21 5 :=
  rectangleBound (l := 82)

private theorem r5_3 : RectangleClaim 7 .two 8 22 121 24 5 :=
  rectangleBound (l := 84)

private theorem r5_4 : RectangleClaim 7 .two 9 25 121 27 5 :=
  rectangleBound (l := 85)

private theorem r5_5 : RectangleClaim 7 .two 10 28 121 30 5 :=
  rectangleBound (l := 86)

private theorem r5_6 : RectangleClaim 7 .two 11 31 121 33 5 :=
  rectangleBound (l := 87)

private theorem r5_7 : RectangleClaim 7 .two 12 34 121 36 5 :=
  rectangleBound (l := 88)

private theorem r5_8 : RectangleClaim 7 .two 13 37 121 39 5 :=
  rectangleBound (l := 88)

private theorem r5_9 : RectangleClaim 7 .two 14 40 121 42 5 :=
  rectangleBound (l := 89)

private theorem r5_10 : RectangleClaim 7 .two 15 43 121 43 5 :=
  rectangleBound (l := 89)

private theorem r5_11 : RectangleClaim 7 .two 15 44 121 44 5 :=
  rectangleBound (l := 89)

private theorem exact5 (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
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
  by_cases hJ8 : a.j ≤ 39
  · apply r5_8 <;> omega
  by_cases hJ9 : a.j ≤ 42
  · apply r5_9 <;> omega
  by_cases hJ10 : a.j ≤ 43
  · apply r5_10 <;> omega
  apply r5_11 <;> omega

private theorem r6_0 : RectangleClaim 8 .two 6 18 121 18 6 :=
  rectangleBound (l := 82)

private theorem r6_1 : RectangleClaim 8 .two 7 19 121 21 6 :=
  rectangleBound (l := 82)

private theorem r6_2 : RectangleClaim 8 .two 8 22 121 24 6 :=
  rectangleBound (l := 84)

private theorem r6_3 : RectangleClaim 8 .two 9 25 121 27 6 :=
  rectangleBound (l := 85)

private theorem r6_4 : RectangleClaim 8 .two 10 28 121 30 6 :=
  rectangleBound (l := 86)

private theorem r6_5 : RectangleClaim 8 .two 11 31 121 33 6 :=
  rectangleBound (l := 87)

private theorem r6_6 : RectangleClaim 8 .two 12 34 121 36 6 :=
  rectangleBound (l := 88)

private theorem r6_7 : RectangleClaim 8 .two 13 37 121 39 6 :=
  rectangleBound (l := 88)

private theorem r6_8 : RectangleClaim 8 .two 14 40 121 42 6 :=
  rectangleBound (l := 89)

private theorem r6_9 : RectangleClaim 8 .two 15 43 121 43 6 :=
  rectangleBound (l := 89)

private theorem r6_10 : RectangleClaim 8 .two 15 44 121 44 6 :=
  rectangleBound (l := 89)

private theorem exact6 (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
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
  by_cases hJ7 : a.j ≤ 39
  · apply r6_7 <;> omega
  by_cases hJ8 : a.j ≤ 42
  · apply r6_8 <;> omega
  by_cases hJ9 : a.j ≤ 43
  · apply r6_9 <;> omega
  apply r6_10 <;> omega

private theorem r7_0 : RectangleClaim 9 .two 7 21 121 21 7 :=
  rectangleBound (l := 83)

private theorem r7_1 : RectangleClaim 9 .two 8 22 121 24 7 :=
  rectangleBound (l := 84)

private theorem r7_2 : RectangleClaim 9 .two 9 25 121 27 7 :=
  rectangleBound (l := 85)

private theorem r7_3 : RectangleClaim 9 .two 10 28 121 30 7 :=
  rectangleBound (l := 86)

private theorem r7_4 : RectangleClaim 9 .two 11 31 121 33 7 :=
  rectangleBound (l := 87)

private theorem r7_5 : RectangleClaim 9 .two 12 34 121 36 7 :=
  rectangleBound (l := 88)

private theorem r7_6 : RectangleClaim 9 .two 13 37 121 39 7 :=
  rectangleBound (l := 88)

private theorem r7_7 : RectangleClaim 9 .two 14 40 121 42 7 :=
  rectangleBound (l := 89)

private theorem r7_8 : RectangleClaim 9 .two 15 43 121 43 7 :=
  rectangleBound (l := 89)

private theorem r7_9 : RectangleClaim 9 .two 15 44 121 44 7 :=
  rectangleBound (l := 89)

private theorem exact7 (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
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
  by_cases hJ6 : a.j ≤ 39
  · apply r7_6 <;> omega
  by_cases hJ7 : a.j ≤ 42
  · apply r7_7 <;> omega
  by_cases hJ8 : a.j ≤ 43
  · apply r7_8 <;> omega
  apply r7_9 <;> omega

private theorem r8_0 : RectangleClaim 10 .two 8 24 121 24 8 :=
  rectangleBound (l := 85)

private theorem r8_1 : RectangleClaim 10 .two 9 25 121 27 8 :=
  rectangleBound (l := 85)

private theorem r8_2 : RectangleClaim 10 .two 10 28 121 30 8 :=
  rectangleBound (l := 86)

private theorem r8_3 : RectangleClaim 10 .two 11 31 121 33 8 :=
  rectangleBound (l := 87)

private theorem r8_4 : RectangleClaim 10 .two 12 34 121 36 8 :=
  rectangleBound (l := 88)

private theorem r8_5 : RectangleClaim 10 .two 13 37 121 39 8 :=
  rectangleBound (l := 88)

private theorem r8_6 : RectangleClaim 10 .two 14 40 121 42 8 :=
  rectangleBound (l := 89)

private theorem r8_7 : RectangleClaim 10 .two 15 43 121 43 8 :=
  rectangleBound (l := 89)

private theorem r8_8 : RectangleClaim 10 .two 15 44 121 44 8 :=
  rectangleBound (l := 89)

private theorem exact8 (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
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
  by_cases hJ5 : a.j ≤ 39
  · apply r8_5 <;> omega
  by_cases hJ6 : a.j ≤ 42
  · apply r8_6 <;> omega
  by_cases hJ7 : a.j ≤ 43
  · apply r8_7 <;> omega
  apply r8_8 <;> omega

private theorem r9_0 : RectangleClaim 11 .two 9 27 121 27 9 :=
  rectangleBound (l := 86)

private theorem r9_1 : RectangleClaim 11 .two 10 28 121 30 9 :=
  rectangleBound (l := 86)

private theorem r9_2 : RectangleClaim 11 .two 11 31 121 33 9 :=
  rectangleBound (l := 87)

private theorem r9_3 : RectangleClaim 11 .two 12 34 121 36 9 :=
  rectangleBound (l := 88)

private theorem r9_4 : RectangleClaim 11 .two 13 37 121 39 9 :=
  rectangleBound (l := 88)

private theorem r9_5 : RectangleClaim 11 .two 14 40 121 42 9 :=
  rectangleBound (l := 89)

private theorem r9_6 : RectangleClaim 11 .two 15 43 121 43 9 :=
  rectangleBound (l := 89)

private theorem r9_7 : RectangleClaim 11 .two 15 44 121 44 9 :=
  rectangleBound (l := 89)

private theorem exact9 (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
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
  by_cases hJ4 : a.j ≤ 39
  · apply r9_4 <;> omega
  by_cases hJ5 : a.j ≤ 42
  · apply r9_5 <;> omega
  by_cases hJ6 : a.j ≤ 43
  · apply r9_6 <;> omega
  apply r9_7 <;> omega

private theorem r10_0 : RectangleClaim 12 .two 10 30 121 30 10 :=
  rectangleBound (l := 87)

private theorem r10_1 : RectangleClaim 12 .two 11 31 121 33 10 :=
  rectangleBound (l := 87)

private theorem r10_2 : RectangleClaim 12 .two 12 34 121 36 10 :=
  rectangleBound (l := 88)

private theorem r10_3 : RectangleClaim 12 .two 13 37 121 39 10 :=
  rectangleBound (l := 88)

private theorem r10_4 : RectangleClaim 12 .two 14 40 121 42 10 :=
  rectangleBound (l := 89)

private theorem r10_5 : RectangleClaim 12 .two 15 43 121 43 10 :=
  rectangleBound (l := 89)

private theorem r10_6 : RectangleClaim 12 .two 15 44 121 44 10 :=
  rectangleBound (l := 89)

private theorem exact10 (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j := by
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
  by_cases hJ5 : a.j ≤ 43
  · apply r10_5 <;> omega
  apply r10_6 <;> omega

private theorem r11_0 : RectangleClaim 13 .two 11 33 121 33 11 :=
  rectangleBound (l := 88)

private theorem r11_1 : RectangleClaim 13 .two 12 34 121 36 11 :=
  rectangleBound (l := 88)

private theorem r11_2 : RectangleClaim 13 .two 13 37 121 39 11 :=
  rectangleBound (l := 88)

private theorem r11_3 : RectangleClaim 13 .two 14 40 121 42 11 :=
  rectangleBound (l := 89)

private theorem r11_4 : RectangleClaim 13 .two 15 43 121 43 11 :=
  rectangleBound (l := 89)

private theorem r11_5 : RectangleClaim 13 .two 15 44 121 44 11 :=
  rectangleBound (l := 89)

private theorem exact11 (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 121) (hj : a.j ≤ 44) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 33
  · apply r11_0 <;> omega
  by_cases hJ1 : a.j ≤ 36
  · apply r11_1 <;> omega
  by_cases hJ2 : a.j ≤ 39
  · apply r11_2 <;> omega
  by_cases hJ3 : a.j ≤ 42
  · apply r11_3 <;> omega
  by_cases hJ4 : a.j ≤ 43
  · apply r11_4 <;> omega
  apply r11_5 <;> omega

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two).plus a) (fullCap top)) :
    physicalPrice a (order .two a) ≤ allowance top .two a.j := by
  change 2+a.b ≤ 123 ∧ 6+a.j ≤ 50 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb, hj, ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 121 := by omega
  have hj' : a.j ≤ 44 := by omega
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
