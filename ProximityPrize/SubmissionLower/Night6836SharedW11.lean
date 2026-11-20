/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT03
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w330 : P33.Window := ⟨5,30,8119,8084,236699350819682664,16905,12000,5000000,81920000000⟩
def h330_0 : Height w330 := ⟨16905,12000,by decide +kernel⟩
def h330_1 : Height w330 := ⟨21390,9000,by decide +kernel⟩
def h330_2 : Height w330 := ⟨31993,6000,by decide +kernel⟩
def pick330 (cl : ℕ) : Height w330 := if cl<5 then (h330_0) else (if cl<728 then (h330_1) else (h330_2))
private theorem k330_1_0 : check w330 pick330 1 t9079 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k330_1_1 : check w330 pick330 1 t2541 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k330_1_2 : check w330 pick330 1 t2559 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k330_1_3 : check w330 pick330 1 t2560 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w330 pick330 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t2541 t2559 k330_1_1 k330_1_2
private theorem k330_1_4 : check w330 pick330 1 t9080 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w330 pick330 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t9079 t2560 k330_1_0 k330_1_3
private theorem k330_1_5 : check w330 pick330 1 t2576 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k330_1_6 : check w330 pick330 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k330_1_7 : check w330 pick330 1 t2577 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w330 pick330 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t2576 t382 k330_1_5 k330_1_6
private theorem k330_1_8 : check w330 pick330 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k330_1_9 : check w330 pick330 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k330_1_10 : check w330 pick330 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w330 pick330 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k330_1_8 k330_1_9
private theorem k330_1_11 : check w330 pick330 1 t9087 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w330 pick330 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t2577 t3548 k330_1_7 k330_1_10
private theorem k330_1_12 : check w330 pick330 1 t9088 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w330 pick330 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t9080 t9087 k330_1_4 k330_1_11
theorem cov330_1 : PA.Covered 1 (OZ.Valid 1 w330.low w330.t w330.y w330.r w330.cap) (P33.root 1) :=
  Night6836Tree.sound w330 pick330 1 t9088 _ k330_1_12
theorem cov330_2 : PA.Covered 2 (OZ.Valid 2 w330.low w330.t w330.y w330.r w330.cap) (P33.root 2) :=
  Night6836Tree.sound w330 pick330 2 t9090 _ (by decide +kernel)
theorem cov330_3 : PA.Covered 3 (OZ.Valid 3 w330.low w330.t w330.y w330.r w330.cap) (P33.root 3) :=
  Night6836Tree.sound w330 pick330 3 t564 _ (by decide +kernel)
theorem cov330_4 : PA.Covered 4 (OZ.Valid 4 w330.low w330.t w330.y w330.r w330.cap) (P33.root 4) :=
  Night6836Tree.sound w330 pick330 4 t565 _ (by decide +kernel)
theorem cov330_5 : PA.Covered 5 (OZ.Valid 5 w330.low w330.t w330.y w330.r w330.cap) (P33.root 5) :=
  Night6836Tree.sound w330 pick330 5 t566 _ (by decide +kernel)
theorem cov330_6 : PA.Covered 6 (OZ.Valid 6 w330.low w330.t w330.y w330.r w330.cap) (P33.root 6) :=
  Night6836Tree.sound w330 pick330 6 t567 _ (by decide +kernel)
theorem cov330_7 : PA.Covered 7 (OZ.Valid 7 w330.low w330.t w330.y w330.r w330.cap) (P33.root 7) :=
  Night6836Tree.sound w330 pick330 7 t568 _ (by decide +kernel)
theorem window330 : P33.WindowCount w330 := by
  apply P33.window_count w330 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov330_1
  · exact cov330_2
  · exact cov330_3
  · exact cov330_4
  · exact cov330_5
  · exact cov330_6
  · exact cov330_7
def w331 : P33.Window := ⟨5,31,8083,8055,240871349278202748,17852,12000,5000000,81920000000⟩
def h331_0 : Height w331 := ⟨17852,12000,by decide +kernel⟩
def h331_1 : Height w331 := ⟨22477,9000,by decide +kernel⟩
def h331_2 : Height w331 := ⟨33529,6000,by decide +kernel⟩
def pick331 (cl : ℕ) : Height w331 := if cl<6 then (h331_0) else (if cl<922 then (h331_1) else (h331_2))
private theorem k331_1_0 : check w331 pick331 1 t9079 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k331_1_1 : check w331 pick331 1 t2541 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k331_1_2 : check w331 pick331 1 t2559 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k331_1_3 : check w331 pick331 1 t2560 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w331 pick331 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t2541 t2559 k331_1_1 k331_1_2
private theorem k331_1_4 : check w331 pick331 1 t9080 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w331 pick331 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t9079 t2560 k331_1_0 k331_1_3
private theorem k331_1_5 : check w331 pick331 1 t2576 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k331_1_6 : check w331 pick331 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k331_1_7 : check w331 pick331 1 t2577 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w331 pick331 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t2576 t382 k331_1_5 k331_1_6
private theorem k331_1_8 : check w331 pick331 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k331_1_9 : check w331 pick331 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k331_1_10 : check w331 pick331 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w331 pick331 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k331_1_8 k331_1_9
private theorem k331_1_11 : check w331 pick331 1 t9087 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w331 pick331 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t2577 t3548 k331_1_7 k331_1_10
private theorem k331_1_12 : check w331 pick331 1 t9088 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w331 pick331 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t9080 t9087 k331_1_4 k331_1_11
theorem cov331_1 : PA.Covered 1 (OZ.Valid 1 w331.low w331.t w331.y w331.r w331.cap) (P33.root 1) :=
  Night6836Tree.sound w331 pick331 1 t9088 _ k331_1_12
theorem cov331_2 : PA.Covered 2 (OZ.Valid 2 w331.low w331.t w331.y w331.r w331.cap) (P33.root 2) :=
  Night6836Tree.sound w331 pick331 2 t9090 _ (by decide +kernel)
theorem cov331_3 : PA.Covered 3 (OZ.Valid 3 w331.low w331.t w331.y w331.r w331.cap) (P33.root 3) :=
  Night6836Tree.sound w331 pick331 3 t564 _ (by decide +kernel)
theorem cov331_4 : PA.Covered 4 (OZ.Valid 4 w331.low w331.t w331.y w331.r w331.cap) (P33.root 4) :=
  Night6836Tree.sound w331 pick331 4 t565 _ (by decide +kernel)
theorem cov331_5 : PA.Covered 5 (OZ.Valid 5 w331.low w331.t w331.y w331.r w331.cap) (P33.root 5) :=
  Night6836Tree.sound w331 pick331 5 t566 _ (by decide +kernel)
theorem cov331_6 : PA.Covered 6 (OZ.Valid 6 w331.low w331.t w331.y w331.r w331.cap) (P33.root 6) :=
  Night6836Tree.sound w331 pick331 6 t567 _ (by decide +kernel)
theorem cov331_7 : PA.Covered 7 (OZ.Valid 7 w331.low w331.t w331.y w331.r w331.cap) (P33.root 7) :=
  Night6836Tree.sound w331 pick331 7 t568 _ (by decide +kernel)
theorem window331 : P33.WindowCount w331 := by
  apply P33.window_count w331 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov331_1
  · exact cov331_2
  · exact cov331_3
  · exact cov331_4
  · exact cov331_5
  · exact cov331_6
  · exact cov331_7
def w332 : P33.Window := ⟨5,32,8047,8017,230535613066322771,18847,12000,5000000,81920000000⟩
def h332_0 : Height w332 := ⟨18847,12000,by decide +kernel⟩
def h332_1 : Height w332 := ⟨23624,9000,by decide +kernel⟩
def h332_2 : Height w332 := ⟨35175,6000,by decide +kernel⟩
def pick332 (cl : ℕ) : Height w332 := if cl<10 then (h332_0) else (if cl<922 then (h332_1) else (h332_2))
private theorem k332_1_0 : check w332 pick332 1 t52 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k332_1_1 : check w332 pick332 1 t9093 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k332_1_2 : check w332 pick332 1 t9094 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w332 pick332 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t52 t9093 k332_1_0 k332_1_1
private theorem k332_1_3 : check w332 pick332 1 t2439 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k332_1_4 : check w332 pick332 1 t2454 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k332_1_5 : check w332 pick332 1 t2455 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w332 pick332 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t2439 t2454 k332_1_3 k332_1_4
private theorem k332_1_6 : check w332 pick332 1 t9095 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w332 pick332 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9094 t2455 k332_1_2 k332_1_5
private theorem k332_1_7 : check w332 pick332 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k332_1_8 : check w332 pick332 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k332_1_9 : check w332 pick332 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w332 pick332 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k332_1_7 k332_1_8
private theorem k332_1_10 : check w332 pick332 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k332_1_11 : check w332 pick332 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k332_1_12 : check w332 pick332 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w332 pick332 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k332_1_10 k332_1_11
private theorem k332_1_13 : check w332 pick332 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w332 pick332 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k332_1_9 k332_1_12
private theorem k332_1_14 : check w332 pick332 1 t9096 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w332 pick332 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9095 t3549 k332_1_6 k332_1_13
theorem cov332_1 : PA.Covered 1 (OZ.Valid 1 w332.low w332.t w332.y w332.r w332.cap) (P33.root 1) :=
  Night6836Tree.sound w332 pick332 1 t9096 _ k332_1_14
theorem cov332_2 : PA.Covered 2 (OZ.Valid 2 w332.low w332.t w332.y w332.r w332.cap) (P33.root 2) :=
  Night6836Tree.sound w332 pick332 2 t9090 _ (by decide +kernel)
theorem cov332_3 : PA.Covered 3 (OZ.Valid 3 w332.low w332.t w332.y w332.r w332.cap) (P33.root 3) :=
  Night6836Tree.sound w332 pick332 3 t564 _ (by decide +kernel)
theorem cov332_4 : PA.Covered 4 (OZ.Valid 4 w332.low w332.t w332.y w332.r w332.cap) (P33.root 4) :=
  Night6836Tree.sound w332 pick332 4 t565 _ (by decide +kernel)
theorem cov332_5 : PA.Covered 5 (OZ.Valid 5 w332.low w332.t w332.y w332.r w332.cap) (P33.root 5) :=
  Night6836Tree.sound w332 pick332 5 t566 _ (by decide +kernel)
theorem cov332_6 : PA.Covered 6 (OZ.Valid 6 w332.low w332.t w332.y w332.r w332.cap) (P33.root 6) :=
  Night6836Tree.sound w332 pick332 6 t567 _ (by decide +kernel)
theorem cov332_7 : PA.Covered 7 (OZ.Valid 7 w332.low w332.t w332.y w332.r w332.cap) (P33.root 7) :=
  Night6836Tree.sound w332 pick332 7 t568 _ (by decide +kernel)
theorem window332 : P33.WindowCount w332 := by
  apply P33.window_count w332 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov332_1
  · exact cov332_2
  · exact cov332_3
  · exact cov332_4
  · exact cov332_5
  · exact cov332_6
  · exact cov332_7
def w333 : P33.Window := ⟨5,44,5543,4544,193467564954643834,48449,23000,5000000,81920000000⟩
def h333_0 : Height w333 := ⟨48449,23000,by decide +kernel⟩
def h333_1 : Height w333 := ⟨54656,19000,by decide +kernel⟩
def h333_2 : Height w333 := ⟨64376,15000,by decide +kernel⟩
def pick333 (cl : ℕ) : Height w333 := if cl<6 then (h333_0) else (if cl<107 then (h333_1) else (h333_2))
private theorem k333_1_0 : check w333 pick333 1 t52 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k333_1_1 : check w333 pick333 1 t9093 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k333_1_2 : check w333 pick333 1 t9094 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w333 pick333 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t52 t9093 k333_1_0 k333_1_1
private theorem k333_1_3 : check w333 pick333 1 t2439 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k333_1_4 : check w333 pick333 1 t2454 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k333_1_5 : check w333 pick333 1 t2455 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w333 pick333 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t2439 t2454 k333_1_3 k333_1_4
private theorem k333_1_6 : check w333 pick333 1 t9095 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w333 pick333 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9094 t2455 k333_1_2 k333_1_5
private theorem k333_1_7 : check w333 pick333 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k333_1_8 : check w333 pick333 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k333_1_9 : check w333 pick333 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w333 pick333 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k333_1_7 k333_1_8
private theorem k333_1_10 : check w333 pick333 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k333_1_11 : check w333 pick333 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k333_1_12 : check w333 pick333 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w333 pick333 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k333_1_10 k333_1_11
private theorem k333_1_13 : check w333 pick333 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w333 pick333 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k333_1_9 k333_1_12
private theorem k333_1_14 : check w333 pick333 1 t9098 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w333 pick333 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9095 t9097 k333_1_6 k333_1_13
theorem cov333_1 : PA.Covered 1 (OZ.Valid 1 w333.low w333.t w333.y w333.r w333.cap) (P33.root 1) :=
  Night6836Tree.sound w333 pick333 1 t9098 _ k333_1_14
theorem cov333_2 : PA.Covered 2 (OZ.Valid 2 w333.low w333.t w333.y w333.r w333.cap) (P33.root 2) :=
  Night6836Tree.sound w333 pick333 2 t2403 _ (by decide +kernel)
theorem cov333_3 : PA.Covered 3 (OZ.Valid 3 w333.low w333.t w333.y w333.r w333.cap) (P33.root 3) :=
  Night6836Tree.sound w333 pick333 3 t564 _ (by decide +kernel)
theorem cov333_4 : PA.Covered 4 (OZ.Valid 4 w333.low w333.t w333.y w333.r w333.cap) (P33.root 4) :=
  Night6836Tree.sound w333 pick333 4 t565 _ (by decide +kernel)
theorem cov333_5 : PA.Covered 5 (OZ.Valid 5 w333.low w333.t w333.y w333.r w333.cap) (P33.root 5) :=
  Night6836Tree.sound w333 pick333 5 t566 _ (by decide +kernel)
theorem cov333_6 : PA.Covered 6 (OZ.Valid 6 w333.low w333.t w333.y w333.r w333.cap) (P33.root 6) :=
  Night6836Tree.sound w333 pick333 6 t567 _ (by decide +kernel)
theorem cov333_7 : PA.Covered 7 (OZ.Valid 7 w333.low w333.t w333.y w333.r w333.cap) (P33.root 7) :=
  Night6836Tree.sound w333 pick333 7 t2134 _ (by decide +kernel)
theorem window333 : P33.WindowCount w333 := by
  apply P33.window_count w333 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov333_1
  · exact cov333_2
  · exact cov333_3
  · exact cov333_4
  · exact cov333_5
  · exact cov333_6
  · exact cov333_7
def w334 : P33.Window := ⟨5,64,4515,4073,235473589526203524,79754,30000,5000000,81920000000⟩
def h334_0 : Height w334 := ⟨79754,30000,by decide +kernel⟩
def h334_1 : Height w334 := ⟨84003,27000,by decide +kernel⟩
def h334_2 : Height w334 := ⟨89168,24000,by decide +kernel⟩
def h334_3 : Height w334 := ⟨95799,21000,by decide +kernel⟩
def h334_4 : Height w334 := ⟨104993,18000,by decide +kernel⟩
def pick334 (cl : ℕ) : Height w334 := if cl<18 then (if cl<4 then (h334_0) else (h334_1)) else (if cl<70 then (h334_2) else (if cl<302 then (h334_3) else (h334_4)))
private theorem k334_1_0 : check w334 pick334 1 t9079 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k334_1_1 : check w334 pick334 1 t2541 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k334_1_2 : check w334 pick334 1 t9107 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k334_1_3 : check w334 pick334 1 t9108 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w334 pick334 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t2541 t9107 k334_1_1 k334_1_2
private theorem k334_1_4 : check w334 pick334 1 t9109 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w334 pick334 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t9079 t9108 k334_1_0 k334_1_3
private theorem k334_1_5 : check w334 pick334 1 t2576 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k334_1_6 : check w334 pick334 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k334_1_7 : check w334 pick334 1 t2577 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w334 pick334 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t2576 t382 k334_1_5 k334_1_6
private theorem k334_1_8 : check w334 pick334 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k334_1_9 : check w334 pick334 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k334_1_10 : check w334 pick334 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w334 pick334 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k334_1_8 k334_1_9
private theorem k334_1_11 : check w334 pick334 1 t9085 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w334 pick334 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t2577 t9084 k334_1_7 k334_1_10
private theorem k334_1_12 : check w334 pick334 1 t9110 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w334 pick334 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t9109 t9085 k334_1_4 k334_1_11
theorem cov334_1 : PA.Covered 1 (OZ.Valid 1 w334.low w334.t w334.y w334.r w334.cap) (P33.root 1) :=
  Night6836Tree.sound w334 pick334 1 t9110 _ k334_1_12
theorem cov334_2 : PA.Covered 2 (OZ.Valid 2 w334.low w334.t w334.y w334.r w334.cap) (P33.root 2) :=
  Night6836Tree.sound w334 pick334 2 t2603 _ (by decide +kernel)
theorem cov334_3 : PA.Covered 3 (OZ.Valid 3 w334.low w334.t w334.y w334.r w334.cap) (P33.root 3) :=
  Night6836Tree.sound w334 pick334 3 t564 _ (by decide +kernel)
theorem cov334_4 : PA.Covered 4 (OZ.Valid 4 w334.low w334.t w334.y w334.r w334.cap) (P33.root 4) :=
  Night6836Tree.sound w334 pick334 4 t565 _ (by decide +kernel)
theorem cov334_5 : PA.Covered 5 (OZ.Valid 5 w334.low w334.t w334.y w334.r w334.cap) (P33.root 5) :=
  Night6836Tree.sound w334 pick334 5 t566 _ (by decide +kernel)
theorem cov334_6 : PA.Covered 6 (OZ.Valid 6 w334.low w334.t w334.y w334.r w334.cap) (P33.root 6) :=
  Night6836Tree.sound w334 pick334 6 t567 _ (by decide +kernel)
theorem cov334_7 : PA.Covered 7 (OZ.Valid 7 w334.low w334.t w334.y w334.r w334.cap) (P33.root 7) :=
  Night6836Tree.sound w334 pick334 7 t2134 _ (by decide +kernel)
theorem window334 : P33.WindowCount w334 := by
  apply P33.window_count w334 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov334_1
  · exact cov334_2
  · exact cov334_3
  · exact cov334_4
  · exact cov334_5
  · exact cov334_6
  · exact cov334_7
def w335 : P33.Window := ⟨5,65,4072,3614,234899335625994096,92675,33000,5000000,81920000000⟩
def h335_0 : Height w335 := ⟨92675,33000,by decide +kernel⟩
def h335_1 : Height w335 := ⟨97101,30000,by decide +kernel⟩
def h335_2 : Height w335 := ⟨102394,27000,by decide +kernel⟩
def h335_3 : Height w335 := ⟨109005,24000,by decide +kernel⟩
def h335_4 : Height w335 := ⟨117764,21000,by decide +kernel⟩
def pick335 (cl : ℕ) : Height w335 := if cl<32 then (if cl<5 then (h335_0) else (h335_1)) else (if cl<70 then (h335_2) else (if cl<264 then (h335_3) else (h335_4)))
private theorem k335_1_0 : check w335 pick335 1 t9079 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k335_1_1 : check w335 pick335 1 t9116 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k335_1_2 : check w335 pick335 1 t9117 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w335 pick335 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9079 t9116 k335_1_0 k335_1_1
private theorem k335_1_3 : check w335 pick335 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k335_1_4 : check w335 pick335 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k335_1_5 : check w335 pick335 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w335 pick335 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k335_1_3 k335_1_4
private theorem k335_1_6 : check w335 pick335 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k335_1_7 : check w335 pick335 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w335 pick335 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k335_1_5 k335_1_6
private theorem k335_1_8 : check w335 pick335 1 t9118 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w335 pick335 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9117 t5276 k335_1_2 k335_1_7
theorem cov335_1 : PA.Covered 1 (OZ.Valid 1 w335.low w335.t w335.y w335.r w335.cap) (P33.root 1) :=
  Night6836Tree.sound w335 pick335 1 t9118 _ k335_1_8
theorem cov335_2 : PA.Covered 2 (OZ.Valid 2 w335.low w335.t w335.y w335.r w335.cap) (P33.root 2) :=
  Night6836Tree.sound w335 pick335 2 t2603 _ (by decide +kernel)
theorem cov335_3 : PA.Covered 3 (OZ.Valid 3 w335.low w335.t w335.y w335.r w335.cap) (P33.root 3) :=
  Night6836Tree.sound w335 pick335 3 t564 _ (by decide +kernel)
theorem cov335_4 : PA.Covered 4 (OZ.Valid 4 w335.low w335.t w335.y w335.r w335.cap) (P33.root 4) :=
  Night6836Tree.sound w335 pick335 4 t565 _ (by decide +kernel)
theorem cov335_5 : PA.Covered 5 (OZ.Valid 5 w335.low w335.t w335.y w335.r w335.cap) (P33.root 5) :=
  Night6836Tree.sound w335 pick335 5 t566 _ (by decide +kernel)
theorem cov335_6 : PA.Covered 6 (OZ.Valid 6 w335.low w335.t w335.y w335.r w335.cap) (P33.root 6) :=
  Night6836Tree.sound w335 pick335 6 t567 _ (by decide +kernel)
theorem cov335_7 : PA.Covered 7 (OZ.Valid 7 w335.low w335.t w335.y w335.r w335.cap) (P33.root 7) :=
  Night6836Tree.sound w335 pick335 7 t2134 _ (by decide +kernel)
theorem window335 : P33.WindowCount w335 := by
  apply P33.window_count w335 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov335_1
  · exact cov335_2
  · exact cov335_3
  · exact cov335_4
  · exact cov335_5
  · exact cov335_6
  · exact cov335_7
def w336 : P33.Window := ⟨5,66,3613,3287,211723667827580022,100251,39000,5000000,81920000000⟩
def h336_0 : Height w336 := ⟨100251,39000,by decide +kernel⟩
def h336_1 : Height w336 := ⟨104176,36000,by decide +kernel⟩
def h336_2 : Height w336 := ⟨108670,33000,by decide +kernel⟩
def h336_3 : Height w336 := ⟨113958,30000,by decide +kernel⟩
def h336_4 : Height w336 := ⟨120405,27000,by decide +kernel⟩
def h336_5 : Height w336 := ⟨128637,24000,by decide +kernel⟩
def pick336 (cl : ℕ) : Height w336 := if cl<32 then (if cl<2 then (h336_0) else (if cl<5 then (h336_1) else (h336_2))) else (if cl<55 then (h336_3) else (if cl<213 then (h336_4) else (h336_5)))
private theorem k336_1_0 : check w336 pick336 1 t9079 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k336_1_1 : check w336 pick336 1 t9116 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k336_1_2 : check w336 pick336 1 t9117 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w336 pick336 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9079 t9116 k336_1_0 k336_1_1
private theorem k336_1_3 : check w336 pick336 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k336_1_4 : check w336 pick336 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k336_1_5 : check w336 pick336 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w336 pick336 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k336_1_3 k336_1_4
private theorem k336_1_6 : check w336 pick336 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k336_1_7 : check w336 pick336 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w336 pick336 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k336_1_5 k336_1_6
private theorem k336_1_8 : check w336 pick336 1 t9118 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w336 pick336 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9117 t5276 k336_1_2 k336_1_7
theorem cov336_1 : PA.Covered 1 (OZ.Valid 1 w336.low w336.t w336.y w336.r w336.cap) (P33.root 1) :=
  Night6836Tree.sound w336 pick336 1 t9118 _ k336_1_8
theorem cov336_2 : PA.Covered 2 (OZ.Valid 2 w336.low w336.t w336.y w336.r w336.cap) (P33.root 2) :=
  Night6836Tree.sound w336 pick336 2 t9121 _ (by decide +kernel)
theorem cov336_3 : PA.Covered 3 (OZ.Valid 3 w336.low w336.t w336.y w336.r w336.cap) (P33.root 3) :=
  Night6836Tree.sound w336 pick336 3 t564 _ (by decide +kernel)
theorem cov336_4 : PA.Covered 4 (OZ.Valid 4 w336.low w336.t w336.y w336.r w336.cap) (P33.root 4) :=
  Night6836Tree.sound w336 pick336 4 t565 _ (by decide +kernel)
theorem cov336_5 : PA.Covered 5 (OZ.Valid 5 w336.low w336.t w336.y w336.r w336.cap) (P33.root 5) :=
  Night6836Tree.sound w336 pick336 5 t566 _ (by decide +kernel)
theorem cov336_6 : PA.Covered 6 (OZ.Valid 6 w336.low w336.t w336.y w336.r w336.cap) (P33.root 6) :=
  Night6836Tree.sound w336 pick336 6 t567 _ (by decide +kernel)
theorem cov336_7 : PA.Covered 7 (OZ.Valid 7 w336.low w336.t w336.y w336.r w336.cap) (P33.root 7) :=
  Night6836Tree.sound w336 pick336 7 t2134 _ (by decide +kernel)
theorem window336 : P33.WindowCount w336 := by
  apply P33.window_count w336 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov336_1
  · exact cov336_2
  · exact cov336_3
  · exact cov336_4
  · exact cov336_5
  · exact cov336_6
  · exact cov336_7
def w337 : P33.Window := ⟨6,25,8175,8141,216764378809793871,13493,12000,5000000,81920000000⟩
def h337_0 : Height w337 := ⟨13493,12000,by decide +kernel⟩
def h337_1 : Height w337 := ⟨18358,9000,by decide +kernel⟩
def pick337 (cl : ℕ) : Height w337 := if cl<12 then (h337_0) else (h337_1)
private theorem k337_1_0 : check w337 pick337 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k337_1_1 : check w337 pick337 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k337_1_2 : check w337 pick337 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w337 pick337 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k337_1_0 k337_1_1
private theorem k337_1_3 : check w337 pick337 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k337_1_4 : check w337 pick337 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k337_1_5 : check w337 pick337 1 t5902 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w337 pick337 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t5307 k337_1_3 k337_1_4
private theorem k337_1_6 : check w337 pick337 1 t9122 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w337 pick337 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t5902 k337_1_2 k337_1_5
private theorem k337_1_7 : check w337 pick337 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k337_1_8 : check w337 pick337 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k337_1_9 : check w337 pick337 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w337 pick337 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k337_1_7 k337_1_8
private theorem k337_1_10 : check w337 pick337 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k337_1_11 : check w337 pick337 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k337_1_12 : check w337 pick337 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w337 pick337 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k337_1_10 k337_1_11
private theorem k337_1_13 : check w337 pick337 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w337 pick337 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k337_1_9 k337_1_12
private theorem k337_1_14 : check w337 pick337 1 t9123 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w337 pick337 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9122 t2461 k337_1_6 k337_1_13
theorem cov337_1 : PA.Covered 1 (OZ.Valid 1 w337.low w337.t w337.y w337.r w337.cap) (P33.root 1) :=
  Night6836Tree.sound w337 pick337 1 t9123 _ k337_1_14
theorem cov337_2 : PA.Covered 2 (OZ.Valid 2 w337.low w337.t w337.y w337.r w337.cap) (P33.root 2) :=
  Night6836Tree.sound w337 pick337 2 t5320 _ (by decide +kernel)
theorem cov337_3 : PA.Covered 3 (OZ.Valid 3 w337.low w337.t w337.y w337.r w337.cap) (P33.root 3) :=
  Night6836Tree.sound w337 pick337 3 t564 _ (by decide +kernel)
theorem cov337_4 : PA.Covered 4 (OZ.Valid 4 w337.low w337.t w337.y w337.r w337.cap) (P33.root 4) :=
  Night6836Tree.sound w337 pick337 4 t565 _ (by decide +kernel)
theorem cov337_5 : PA.Covered 5 (OZ.Valid 5 w337.low w337.t w337.y w337.r w337.cap) (P33.root 5) :=
  Night6836Tree.sound w337 pick337 5 t566 _ (by decide +kernel)
theorem cov337_6 : PA.Covered 6 (OZ.Valid 6 w337.low w337.t w337.y w337.r w337.cap) (P33.root 6) :=
  Night6836Tree.sound w337 pick337 6 t567 _ (by decide +kernel)
theorem cov337_7 : PA.Covered 7 (OZ.Valid 7 w337.low w337.t w337.y w337.r w337.cap) (P33.root 7) :=
  Night6836Tree.sound w337 pick337 7 t568 _ (by decide +kernel)
theorem window337 : P33.WindowCount w337 := by
  apply P33.window_count w337 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov337_1
  · exact cov337_2
  · exact cov337_3
  · exact cov337_4
  · exact cov337_5
  · exact cov337_6
  · exact cov337_7
def w338 : P33.Window := ⟨6,26,8140,8106,220916400485155488,14505,12000,5000000,81920000000⟩
def h338_0 : Height w338 := ⟨14505,12000,by decide +kernel⟩
def h338_1 : Height w338 := ⟨19570,9000,by decide +kernel⟩
def pick338 (cl : ℕ) : Height w338 := if cl<18 then (h338_0) else (h338_1)
private theorem k338_1_0 : check w338 pick338 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k338_1_1 : check w338 pick338 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k338_1_2 : check w338 pick338 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w338 pick338 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k338_1_0 k338_1_1
private theorem k338_1_3 : check w338 pick338 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k338_1_4 : check w338 pick338 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k338_1_5 : check w338 pick338 1 t5902 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w338 pick338 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t5307 k338_1_3 k338_1_4
private theorem k338_1_6 : check w338 pick338 1 t9122 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w338 pick338 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t5902 k338_1_2 k338_1_5
private theorem k338_1_7 : check w338 pick338 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k338_1_8 : check w338 pick338 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k338_1_9 : check w338 pick338 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w338 pick338 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k338_1_7 k338_1_8
private theorem k338_1_10 : check w338 pick338 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k338_1_11 : check w338 pick338 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k338_1_12 : check w338 pick338 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w338 pick338 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k338_1_10 k338_1_11
private theorem k338_1_13 : check w338 pick338 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w338 pick338 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k338_1_9 k338_1_12
private theorem k338_1_14 : check w338 pick338 1 t9123 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w338 pick338 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9122 t2461 k338_1_6 k338_1_13
theorem cov338_1 : PA.Covered 1 (OZ.Valid 1 w338.low w338.t w338.y w338.r w338.cap) (P33.root 1) :=
  Night6836Tree.sound w338 pick338 1 t9123 _ k338_1_14
theorem cov338_2 : PA.Covered 2 (OZ.Valid 2 w338.low w338.t w338.y w338.r w338.cap) (P33.root 2) :=
  Night6836Tree.sound w338 pick338 2 t5320 _ (by decide +kernel)
theorem cov338_3 : PA.Covered 3 (OZ.Valid 3 w338.low w338.t w338.y w338.r w338.cap) (P33.root 3) :=
  Night6836Tree.sound w338 pick338 3 t564 _ (by decide +kernel)
theorem cov338_4 : PA.Covered 4 (OZ.Valid 4 w338.low w338.t w338.y w338.r w338.cap) (P33.root 4) :=
  Night6836Tree.sound w338 pick338 4 t565 _ (by decide +kernel)
theorem cov338_5 : PA.Covered 5 (OZ.Valid 5 w338.low w338.t w338.y w338.r w338.cap) (P33.root 5) :=
  Night6836Tree.sound w338 pick338 5 t566 _ (by decide +kernel)
theorem cov338_6 : PA.Covered 6 (OZ.Valid 6 w338.low w338.t w338.y w338.r w338.cap) (P33.root 6) :=
  Night6836Tree.sound w338 pick338 6 t567 _ (by decide +kernel)
theorem cov338_7 : PA.Covered 7 (OZ.Valid 7 w338.low w338.t w338.y w338.r w338.cap) (P33.root 7) :=
  Night6836Tree.sound w338 pick338 7 t568 _ (by decide +kernel)
theorem window338 : P33.WindowCount w338 := by
  apply P33.window_count w338 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov338_1
  · exact cov338_2
  · exact cov338_3
  · exact cov338_4
  · exact cov338_5
  · exact cov338_6
  · exact cov338_7
def w339 : P33.Window := ⟨6,27,8105,8071,225023967114523474,15530,12000,5000000,81920000000⟩
def h339_0 : Height w339 := ⟨15530,12000,by decide +kernel⟩
def h339_1 : Height w339 := ⟨20799,9000,by decide +kernel⟩
def pick339 (cl : ℕ) : Height w339 := if cl<32 then (h339_0) else (h339_1)
private theorem k339_1_0 : check w339 pick339 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k339_1_1 : check w339 pick339 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k339_1_2 : check w339 pick339 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w339 pick339 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k339_1_0 k339_1_1
private theorem k339_1_3 : check w339 pick339 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k339_1_4 : check w339 pick339 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k339_1_5 : check w339 pick339 1 t5902 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w339 pick339 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t5307 k339_1_3 k339_1_4
private theorem k339_1_6 : check w339 pick339 1 t9122 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w339 pick339 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t5902 k339_1_2 k339_1_5
private theorem k339_1_7 : check w339 pick339 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k339_1_8 : check w339 pick339 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k339_1_9 : check w339 pick339 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w339 pick339 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k339_1_7 k339_1_8
private theorem k339_1_10 : check w339 pick339 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k339_1_11 : check w339 pick339 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k339_1_12 : check w339 pick339 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w339 pick339 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k339_1_10 k339_1_11
private theorem k339_1_13 : check w339 pick339 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w339 pick339 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k339_1_9 k339_1_12
private theorem k339_1_14 : check w339 pick339 1 t9124 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w339 pick339 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9122 t3549 k339_1_6 k339_1_13
theorem cov339_1 : PA.Covered 1 (OZ.Valid 1 w339.low w339.t w339.y w339.r w339.cap) (P33.root 1) :=
  Night6836Tree.sound w339 pick339 1 t9124 _ k339_1_14
theorem cov339_2 : PA.Covered 2 (OZ.Valid 2 w339.low w339.t w339.y w339.r w339.cap) (P33.root 2) :=
  Night6836Tree.sound w339 pick339 2 t5320 _ (by decide +kernel)
theorem cov339_3 : PA.Covered 3 (OZ.Valid 3 w339.low w339.t w339.y w339.r w339.cap) (P33.root 3) :=
  Night6836Tree.sound w339 pick339 3 t564 _ (by decide +kernel)
theorem cov339_4 : PA.Covered 4 (OZ.Valid 4 w339.low w339.t w339.y w339.r w339.cap) (P33.root 4) :=
  Night6836Tree.sound w339 pick339 4 t565 _ (by decide +kernel)
theorem cov339_5 : PA.Covered 5 (OZ.Valid 5 w339.low w339.t w339.y w339.r w339.cap) (P33.root 5) :=
  Night6836Tree.sound w339 pick339 5 t566 _ (by decide +kernel)
theorem cov339_6 : PA.Covered 6 (OZ.Valid 6 w339.low w339.t w339.y w339.r w339.cap) (P33.root 6) :=
  Night6836Tree.sound w339 pick339 6 t567 _ (by decide +kernel)
theorem cov339_7 : PA.Covered 7 (OZ.Valid 7 w339.low w339.t w339.y w339.r w339.cap) (P33.root 7) :=
  Night6836Tree.sound w339 pick339 7 t568 _ (by decide +kernel)
theorem window339 : P33.WindowCount w339 := by
  apply P33.window_count w339 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov339_1
  · exact cov339_2
  · exact cov339_3
  · exact cov339_4
  · exact cov339_5
  · exact cov339_6
  · exact cov339_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w340 : P33.Window := ⟨6,28,8070,8035,229087078697897831,16572,12000,5000000,81920000000⟩
def h340_0 : Height w340 := ⟨16572,12000,by decide +kernel⟩
def h340_1 : Height w340 := ⟨22053,9000,by decide +kernel⟩
def pick340 (cl : ℕ) : Height w340 := if cl<32 then (h340_0) else (h340_1)
private theorem k340_1_0 : check w340 pick340 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k340_1_1 : check w340 pick340 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k340_1_2 : check w340 pick340 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w340 pick340 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k340_1_0 k340_1_1
private theorem k340_1_3 : check w340 pick340 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k340_1_4 : check w340 pick340 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k340_1_5 : check w340 pick340 1 t5902 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w340 pick340 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t5307 k340_1_3 k340_1_4
private theorem k340_1_6 : check w340 pick340 1 t9125 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w340 pick340 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t5902 k340_1_2 k340_1_5
private theorem k340_1_7 : check w340 pick340 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k340_1_8 : check w340 pick340 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k340_1_9 : check w340 pick340 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w340 pick340 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k340_1_7 k340_1_8
private theorem k340_1_10 : check w340 pick340 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k340_1_11 : check w340 pick340 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k340_1_12 : check w340 pick340 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w340 pick340 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k340_1_10 k340_1_11
private theorem k340_1_13 : check w340 pick340 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w340 pick340 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k340_1_9 k340_1_12
private theorem k340_1_14 : check w340 pick340 1 t9126 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w340 pick340 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9125 t3549 k340_1_6 k340_1_13
theorem cov340_1 : PA.Covered 1 (OZ.Valid 1 w340.low w340.t w340.y w340.r w340.cap) (P33.root 1) :=
  Night6836Tree.sound w340 pick340 1 t9126 _ k340_1_14
theorem cov340_2 : PA.Covered 2 (OZ.Valid 2 w340.low w340.t w340.y w340.r w340.cap) (P33.root 2) :=
  Night6836Tree.sound w340 pick340 2 t5320 _ (by decide +kernel)
theorem cov340_3 : PA.Covered 3 (OZ.Valid 3 w340.low w340.t w340.y w340.r w340.cap) (P33.root 3) :=
  Night6836Tree.sound w340 pick340 3 t564 _ (by decide +kernel)
theorem cov340_4 : PA.Covered 4 (OZ.Valid 4 w340.low w340.t w340.y w340.r w340.cap) (P33.root 4) :=
  Night6836Tree.sound w340 pick340 4 t565 _ (by decide +kernel)
theorem cov340_5 : PA.Covered 5 (OZ.Valid 5 w340.low w340.t w340.y w340.r w340.cap) (P33.root 5) :=
  Night6836Tree.sound w340 pick340 5 t566 _ (by decide +kernel)
theorem cov340_6 : PA.Covered 6 (OZ.Valid 6 w340.low w340.t w340.y w340.r w340.cap) (P33.root 6) :=
  Night6836Tree.sound w340 pick340 6 t567 _ (by decide +kernel)
theorem cov340_7 : PA.Covered 7 (OZ.Valid 7 w340.low w340.t w340.y w340.r w340.cap) (P33.root 7) :=
  Night6836Tree.sound w340 pick340 7 t568 _ (by decide +kernel)
theorem window340 : P33.WindowCount w340 := by
  apply P33.window_count w340 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov340_1
  · exact cov340_2
  · exact cov340_3
  · exact cov340_4
  · exact cov340_5
  · exact cov340_6
  · exact cov340_7
def w341 : P33.Window := ⟨6,29,8034,7999,233076694709531927,17627,12000,5000000,81920000000⟩
def h341_0 : Height w341 := ⟨17627,12000,by decide +kernel⟩
def h341_1 : Height w341 := ⟨23325,9000,by decide +kernel⟩
def pick341 (cl : ℕ) : Height w341 := if cl<32 then (h341_0) else (h341_1)
private theorem k341_1_0 : check w341 pick341 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k341_1_1 : check w341 pick341 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k341_1_2 : check w341 pick341 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w341 pick341 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k341_1_0 k341_1_1
private theorem k341_1_3 : check w341 pick341 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k341_1_4 : check w341 pick341 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k341_1_5 : check w341 pick341 1 t5902 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w341 pick341 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t5307 k341_1_3 k341_1_4
private theorem k341_1_6 : check w341 pick341 1 t9125 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w341 pick341 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t5902 k341_1_2 k341_1_5
private theorem k341_1_7 : check w341 pick341 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k341_1_8 : check w341 pick341 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k341_1_9 : check w341 pick341 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w341 pick341 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k341_1_7 k341_1_8
private theorem k341_1_10 : check w341 pick341 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k341_1_11 : check w341 pick341 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k341_1_12 : check w341 pick341 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w341 pick341 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k341_1_10 k341_1_11
private theorem k341_1_13 : check w341 pick341 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w341 pick341 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k341_1_9 k341_1_12
private theorem k341_1_14 : check w341 pick341 1 t9126 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w341 pick341 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9125 t3549 k341_1_6 k341_1_13
theorem cov341_1 : PA.Covered 1 (OZ.Valid 1 w341.low w341.t w341.y w341.r w341.cap) (P33.root 1) :=
  Night6836Tree.sound w341 pick341 1 t9126 _ k341_1_14
theorem cov341_2 : PA.Covered 2 (OZ.Valid 2 w341.low w341.t w341.y w341.r w341.cap) (P33.root 2) :=
  Night6836Tree.sound w341 pick341 2 t5320 _ (by decide +kernel)
theorem cov341_3 : PA.Covered 3 (OZ.Valid 3 w341.low w341.t w341.y w341.r w341.cap) (P33.root 3) :=
  Night6836Tree.sound w341 pick341 3 t564 _ (by decide +kernel)
theorem cov341_4 : PA.Covered 4 (OZ.Valid 4 w341.low w341.t w341.y w341.r w341.cap) (P33.root 4) :=
  Night6836Tree.sound w341 pick341 4 t565 _ (by decide +kernel)
theorem cov341_5 : PA.Covered 5 (OZ.Valid 5 w341.low w341.t w341.y w341.r w341.cap) (P33.root 5) :=
  Night6836Tree.sound w341 pick341 5 t566 _ (by decide +kernel)
theorem cov341_6 : PA.Covered 6 (OZ.Valid 6 w341.low w341.t w341.y w341.r w341.cap) (P33.root 6) :=
  Night6836Tree.sound w341 pick341 6 t567 _ (by decide +kernel)
theorem cov341_7 : PA.Covered 7 (OZ.Valid 7 w341.low w341.t w341.y w341.r w341.cap) (P33.root 7) :=
  Night6836Tree.sound w341 pick341 7 t568 _ (by decide +kernel)
theorem window341 : P33.WindowCount w341 := by
  apply P33.window_count w341 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov341_1
  · exact cov341_2
  · exact cov341_3
  · exact cov341_4
  · exact cov341_5
  · exact cov341_6
  · exact cov341_7
def w342 : P33.Window := ⟨6,30,7998,7963,237020603419890791,18697,12000,5000000,81920000000⟩
def h342_0 : Height w342 := ⟨18697,12000,by decide +kernel⟩
def h342_1 : Height w342 := ⟨24617,9000,by decide +kernel⟩
def pick342 (cl : ℕ) : Height w342 := if cl<36 then (h342_0) else (h342_1)
private theorem k342_1_0 : check w342 pick342 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k342_1_1 : check w342 pick342 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k342_1_2 : check w342 pick342 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w342 pick342 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k342_1_0 k342_1_1
private theorem k342_1_3 : check w342 pick342 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k342_1_4 : check w342 pick342 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k342_1_5 : check w342 pick342 1 t5902 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w342 pick342 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t5307 k342_1_3 k342_1_4
private theorem k342_1_6 : check w342 pick342 1 t9125 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w342 pick342 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t5902 k342_1_2 k342_1_5
private theorem k342_1_7 : check w342 pick342 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k342_1_8 : check w342 pick342 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k342_1_9 : check w342 pick342 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w342 pick342 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k342_1_7 k342_1_8
private theorem k342_1_10 : check w342 pick342 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k342_1_11 : check w342 pick342 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k342_1_12 : check w342 pick342 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w342 pick342 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k342_1_10 k342_1_11
private theorem k342_1_13 : check w342 pick342 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w342 pick342 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k342_1_9 k342_1_12
private theorem k342_1_14 : check w342 pick342 1 t9126 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w342 pick342 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9125 t3549 k342_1_6 k342_1_13
theorem cov342_1 : PA.Covered 1 (OZ.Valid 1 w342.low w342.t w342.y w342.r w342.cap) (P33.root 1) :=
  Night6836Tree.sound w342 pick342 1 t9126 _ k342_1_14
theorem cov342_2 : PA.Covered 2 (OZ.Valid 2 w342.low w342.t w342.y w342.r w342.cap) (P33.root 2) :=
  Night6836Tree.sound w342 pick342 2 t5320 _ (by decide +kernel)
theorem cov342_3 : PA.Covered 3 (OZ.Valid 3 w342.low w342.t w342.y w342.r w342.cap) (P33.root 3) :=
  Night6836Tree.sound w342 pick342 3 t564 _ (by decide +kernel)
theorem cov342_4 : PA.Covered 4 (OZ.Valid 4 w342.low w342.t w342.y w342.r w342.cap) (P33.root 4) :=
  Night6836Tree.sound w342 pick342 4 t565 _ (by decide +kernel)
theorem cov342_5 : PA.Covered 5 (OZ.Valid 5 w342.low w342.t w342.y w342.r w342.cap) (P33.root 5) :=
  Night6836Tree.sound w342 pick342 5 t566 _ (by decide +kernel)
theorem cov342_6 : PA.Covered 6 (OZ.Valid 6 w342.low w342.t w342.y w342.r w342.cap) (P33.root 6) :=
  Night6836Tree.sound w342 pick342 6 t567 _ (by decide +kernel)
theorem cov342_7 : PA.Covered 7 (OZ.Valid 7 w342.low w342.t w342.y w342.r w342.cap) (P33.root 7) :=
  Night6836Tree.sound w342 pick342 7 t568 _ (by decide +kernel)
theorem window342 : P33.WindowCount w342 := by
  apply P33.window_count w342 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov342_1
  · exact cov342_2
  · exact cov342_3
  · exact cov342_4
  · exact cov342_5
  · exact cov342_6
  · exact cov342_7
def w343 : P33.Window := ⟨6,31,6830,5831,200024672835053857,23406,19000,5000000,81920000000⟩
def h343_0 : Height w343 := ⟨23406,19000,by decide +kernel⟩
def h343_1 : Height w343 := ⟨29001,15000,by decide +kernel⟩
def h343_2 : Height w343 := ⟨39471,11000,by decide +kernel⟩
def pick343 (cl : ℕ) : Height w343 := if cl<4 then (h343_0) else (if cl<167 then (h343_1) else (h343_2))
private theorem k343_1_0 : check w343 pick343 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k343_1_1 : check w343 pick343 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k343_1_2 : check w343 pick343 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w343 pick343 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k343_1_0 k343_1_1
private theorem k343_1_3 : check w343 pick343 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k343_1_4 : check w343 pick343 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k343_1_5 : check w343 pick343 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w343 pick343 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k343_1_3 k343_1_4
private theorem k343_1_6 : check w343 pick343 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w343 pick343 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k343_1_2 k343_1_5
private theorem k343_1_7 : check w343 pick343 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k343_1_8 : check w343 pick343 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k343_1_9 : check w343 pick343 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w343 pick343 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k343_1_7 k343_1_8
private theorem k343_1_10 : check w343 pick343 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k343_1_11 : check w343 pick343 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k343_1_12 : check w343 pick343 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w343 pick343 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k343_1_10 k343_1_11
private theorem k343_1_13 : check w343 pick343 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w343 pick343 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k343_1_9 k343_1_12
private theorem k343_1_14 : check w343 pick343 1 t9129 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w343 pick343 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t3549 k343_1_6 k343_1_13
theorem cov343_1 : PA.Covered 1 (OZ.Valid 1 w343.low w343.t w343.y w343.r w343.cap) (P33.root 1) :=
  Night6836Tree.sound w343 pick343 1 t9129 _ k343_1_14
theorem cov343_2 : PA.Covered 2 (OZ.Valid 2 w343.low w343.t w343.y w343.r w343.cap) (P33.root 2) :=
  Night6836Tree.sound w343 pick343 2 t5366 _ (by decide +kernel)
theorem cov343_3 : PA.Covered 3 (OZ.Valid 3 w343.low w343.t w343.y w343.r w343.cap) (P33.root 3) :=
  Night6836Tree.sound w343 pick343 3 t564 _ (by decide +kernel)
theorem cov343_4 : PA.Covered 4 (OZ.Valid 4 w343.low w343.t w343.y w343.r w343.cap) (P33.root 4) :=
  Night6836Tree.sound w343 pick343 4 t565 _ (by decide +kernel)
theorem cov343_5 : PA.Covered 5 (OZ.Valid 5 w343.low w343.t w343.y w343.r w343.cap) (P33.root 5) :=
  Night6836Tree.sound w343 pick343 5 t566 _ (by decide +kernel)
theorem cov343_6 : PA.Covered 6 (OZ.Valid 6 w343.low w343.t w343.y w343.r w343.cap) (P33.root 6) :=
  Night6836Tree.sound w343 pick343 6 t567 _ (by decide +kernel)
theorem cov343_7 : PA.Covered 7 (OZ.Valid 7 w343.low w343.t w343.y w343.r w343.cap) (P33.root 7) :=
  Night6836Tree.sound w343 pick343 7 t568 _ (by decide +kernel)
theorem window343 : P33.WindowCount w343 := by
  apply P33.window_count w343 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov343_1
  · exact cov343_2
  · exact cov343_3
  · exact cov343_4
  · exact cov343_5
  · exact cov343_6
  · exact cov343_7
def w344 : P33.Window := ⟨6,31,7683,6734,232467118922097524,22054,15000,5000000,81920000000⟩
def h344_0 : Height w344 := ⟨22054,15000,by decide +kernel⟩
def h344_1 : Height w344 := ⟨27023,12000,by decide +kernel⟩
def h344_2 : Height w344 := ⟨36538,9000,by decide +kernel⟩
def pick344 (cl : ℕ) : Height w344 := if cl<13 then (h344_0) else (if cl<318 then (h344_1) else (h344_2))
private theorem k344_1_0 : check w344 pick344 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k344_1_1 : check w344 pick344 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k344_1_2 : check w344 pick344 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w344 pick344 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k344_1_0 k344_1_1
private theorem k344_1_3 : check w344 pick344 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k344_1_4 : check w344 pick344 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k344_1_5 : check w344 pick344 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w344 pick344 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k344_1_3 k344_1_4
private theorem k344_1_6 : check w344 pick344 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w344 pick344 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k344_1_2 k344_1_5
private theorem k344_1_7 : check w344 pick344 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k344_1_8 : check w344 pick344 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k344_1_9 : check w344 pick344 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w344 pick344 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k344_1_7 k344_1_8
private theorem k344_1_10 : check w344 pick344 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k344_1_11 : check w344 pick344 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k344_1_12 : check w344 pick344 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w344 pick344 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k344_1_10 k344_1_11
private theorem k344_1_13 : check w344 pick344 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w344 pick344 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k344_1_9 k344_1_12
private theorem k344_1_14 : check w344 pick344 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w344 pick344 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k344_1_6 k344_1_13
theorem cov344_1 : PA.Covered 1 (OZ.Valid 1 w344.low w344.t w344.y w344.r w344.cap) (P33.root 1) :=
  Night6836Tree.sound w344 pick344 1 t9130 _ k344_1_14
theorem cov344_2 : PA.Covered 2 (OZ.Valid 2 w344.low w344.t w344.y w344.r w344.cap) (P33.root 2) :=
  Night6836Tree.sound w344 pick344 2 t9132 _ (by decide +kernel)
theorem cov344_3 : PA.Covered 3 (OZ.Valid 3 w344.low w344.t w344.y w344.r w344.cap) (P33.root 3) :=
  Night6836Tree.sound w344 pick344 3 t564 _ (by decide +kernel)
theorem cov344_4 : PA.Covered 4 (OZ.Valid 4 w344.low w344.t w344.y w344.r w344.cap) (P33.root 4) :=
  Night6836Tree.sound w344 pick344 4 t565 _ (by decide +kernel)
theorem cov344_5 : PA.Covered 5 (OZ.Valid 5 w344.low w344.t w344.y w344.r w344.cap) (P33.root 5) :=
  Night6836Tree.sound w344 pick344 5 t566 _ (by decide +kernel)
theorem cov344_6 : PA.Covered 6 (OZ.Valid 6 w344.low w344.t w344.y w344.r w344.cap) (P33.root 6) :=
  Night6836Tree.sound w344 pick344 6 t567 _ (by decide +kernel)
theorem cov344_7 : PA.Covered 7 (OZ.Valid 7 w344.low w344.t w344.y w344.r w344.cap) (P33.root 7) :=
  Night6836Tree.sound w344 pick344 7 t568 _ (by decide +kernel)
theorem window344 : P33.WindowCount w344 := by
  apply P33.window_count w344 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov344_1
  · exact cov344_2
  · exact cov344_3
  · exact cov344_4
  · exact cov344_5
  · exact cov344_6
  · exact cov344_7
def w345 : P33.Window := ⟨6,31,7962,7926,240918804828974424,19785,12000,5000000,81920000000⟩
def h345_0 : Height w345 := ⟨19785,12000,by decide +kernel⟩
def h345_1 : Height w345 := ⟨25935,9000,by decide +kernel⟩
def pick345 (cl : ℕ) : Height w345 := if cl<43 then (h345_0) else (h345_1)
private theorem k345_1_0 : check w345 pick345 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k345_1_1 : check w345 pick345 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k345_1_2 : check w345 pick345 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w345 pick345 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k345_1_0 k345_1_1
private theorem k345_1_3 : check w345 pick345 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k345_1_4 : check w345 pick345 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k345_1_5 : check w345 pick345 1 t5902 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w345 pick345 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t5307 k345_1_3 k345_1_4
private theorem k345_1_6 : check w345 pick345 1 t9125 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w345 pick345 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t5902 k345_1_2 k345_1_5
private theorem k345_1_7 : check w345 pick345 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k345_1_8 : check w345 pick345 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k345_1_9 : check w345 pick345 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w345 pick345 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k345_1_7 k345_1_8
private theorem k345_1_10 : check w345 pick345 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k345_1_11 : check w345 pick345 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k345_1_12 : check w345 pick345 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w345 pick345 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k345_1_10 k345_1_11
private theorem k345_1_13 : check w345 pick345 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w345 pick345 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k345_1_9 k345_1_12
private theorem k345_1_14 : check w345 pick345 1 t9126 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w345 pick345 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9125 t3549 k345_1_6 k345_1_13
theorem cov345_1 : PA.Covered 1 (OZ.Valid 1 w345.low w345.t w345.y w345.r w345.cap) (P33.root 1) :=
  Night6836Tree.sound w345 pick345 1 t9126 _ k345_1_14
theorem cov345_2 : PA.Covered 2 (OZ.Valid 2 w345.low w345.t w345.y w345.r w345.cap) (P33.root 2) :=
  Night6836Tree.sound w345 pick345 2 t5320 _ (by decide +kernel)
theorem cov345_3 : PA.Covered 3 (OZ.Valid 3 w345.low w345.t w345.y w345.r w345.cap) (P33.root 3) :=
  Night6836Tree.sound w345 pick345 3 t564 _ (by decide +kernel)
theorem cov345_4 : PA.Covered 4 (OZ.Valid 4 w345.low w345.t w345.y w345.r w345.cap) (P33.root 4) :=
  Night6836Tree.sound w345 pick345 4 t565 _ (by decide +kernel)
theorem cov345_5 : PA.Covered 5 (OZ.Valid 5 w345.low w345.t w345.y w345.r w345.cap) (P33.root 5) :=
  Night6836Tree.sound w345 pick345 5 t566 _ (by decide +kernel)
theorem cov345_6 : PA.Covered 6 (OZ.Valid 6 w345.low w345.t w345.y w345.r w345.cap) (P33.root 6) :=
  Night6836Tree.sound w345 pick345 6 t567 _ (by decide +kernel)
theorem cov345_7 : PA.Covered 7 (OZ.Valid 7 w345.low w345.t w345.y w345.r w345.cap) (P33.root 7) :=
  Night6836Tree.sound w345 pick345 7 t568 _ (by decide +kernel)
theorem window345 : P33.WindowCount w345 := by
  apply P33.window_count w345 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov345_1
  · exact cov345_2
  · exact cov345_3
  · exact cov345_4
  · exact cov345_5
  · exact cov345_6
  · exact cov345_7
def w346 : P33.Window := ⟨6,32,7925,7889,236979581794544295,20887,12000,5000000,81920000000⟩
def h346_0 : Height w346 := ⟨20887,12000,by decide +kernel⟩
def h346_1 : Height w346 := ⟨27275,9000,by decide +kernel⟩
def pick346 (cl : ℕ) : Height w346 := if cl<51 then (h346_0) else (h346_1)
private theorem k346_1_0 : check w346 pick346 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k346_1_1 : check w346 pick346 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k346_1_2 : check w346 pick346 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w346 pick346 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k346_1_0 k346_1_1
private theorem k346_1_3 : check w346 pick346 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k346_1_4 : check w346 pick346 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k346_1_5 : check w346 pick346 1 t5902 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w346 pick346 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t5307 k346_1_3 k346_1_4
private theorem k346_1_6 : check w346 pick346 1 t9125 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w346 pick346 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t5902 k346_1_2 k346_1_5
private theorem k346_1_7 : check w346 pick346 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k346_1_8 : check w346 pick346 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k346_1_9 : check w346 pick346 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w346 pick346 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k346_1_7 k346_1_8
private theorem k346_1_10 : check w346 pick346 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k346_1_11 : check w346 pick346 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k346_1_12 : check w346 pick346 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w346 pick346 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k346_1_10 k346_1_11
private theorem k346_1_13 : check w346 pick346 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w346 pick346 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k346_1_9 k346_1_12
private theorem k346_1_14 : check w346 pick346 1 t9126 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w346 pick346 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9125 t3549 k346_1_6 k346_1_13
theorem cov346_1 : PA.Covered 1 (OZ.Valid 1 w346.low w346.t w346.y w346.r w346.cap) (P33.root 1) :=
  Night6836Tree.sound w346 pick346 1 t9126 _ k346_1_14
theorem cov346_2 : PA.Covered 2 (OZ.Valid 2 w346.low w346.t w346.y w346.r w346.cap) (P33.root 2) :=
  Night6836Tree.sound w346 pick346 2 t5366 _ (by decide +kernel)
theorem cov346_3 : PA.Covered 3 (OZ.Valid 3 w346.low w346.t w346.y w346.r w346.cap) (P33.root 3) :=
  Night6836Tree.sound w346 pick346 3 t564 _ (by decide +kernel)
theorem cov346_4 : PA.Covered 4 (OZ.Valid 4 w346.low w346.t w346.y w346.r w346.cap) (P33.root 4) :=
  Night6836Tree.sound w346 pick346 4 t565 _ (by decide +kernel)
theorem cov346_5 : PA.Covered 5 (OZ.Valid 5 w346.low w346.t w346.y w346.r w346.cap) (P33.root 5) :=
  Night6836Tree.sound w346 pick346 5 t566 _ (by decide +kernel)
theorem cov346_6 : PA.Covered 6 (OZ.Valid 6 w346.low w346.t w346.y w346.r w346.cap) (P33.root 6) :=
  Night6836Tree.sound w346 pick346 6 t567 _ (by decide +kernel)
theorem cov346_7 : PA.Covered 7 (OZ.Valid 7 w346.low w346.t w346.y w346.r w346.cap) (P33.root 7) :=
  Night6836Tree.sound w346 pick346 7 t568 _ (by decide +kernel)
theorem window346 : P33.WindowCount w346 := by
  apply P33.window_count w346 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov346_1
  · exact cov346_2
  · exact cov346_3
  · exact cov346_4
  · exact cov346_5
  · exact cov346_6
  · exact cov346_7
def w347 : P33.Window := ⟨6,33,6832,5833,194180327772116806,25737,19000,5000000,81920000000⟩
def h347_0 : Height w347 := ⟨25737,19000,by decide +kernel⟩
def h347_1 : Height w347 := ⟨31583,15000,by decide +kernel⟩
def h347_2 : Height w347 := ⟨42639,11000,by decide +kernel⟩
def pick347 (cl : ℕ) : Height w347 := if cl<5 then (h347_0) else (if cl<210 then (h347_1) else (h347_2))
private theorem k347_1_0 : check w347 pick347 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k347_1_1 : check w347 pick347 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k347_1_2 : check w347 pick347 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w347 pick347 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k347_1_0 k347_1_1
private theorem k347_1_3 : check w347 pick347 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k347_1_4 : check w347 pick347 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k347_1_5 : check w347 pick347 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w347 pick347 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k347_1_3 k347_1_4
private theorem k347_1_6 : check w347 pick347 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w347 pick347 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k347_1_2 k347_1_5
private theorem k347_1_7 : check w347 pick347 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k347_1_8 : check w347 pick347 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k347_1_9 : check w347 pick347 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w347 pick347 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k347_1_7 k347_1_8
private theorem k347_1_10 : check w347 pick347 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k347_1_11 : check w347 pick347 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k347_1_12 : check w347 pick347 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w347 pick347 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k347_1_10 k347_1_11
private theorem k347_1_13 : check w347 pick347 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w347 pick347 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k347_1_9 k347_1_12
private theorem k347_1_14 : check w347 pick347 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w347 pick347 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k347_1_6 k347_1_13
theorem cov347_1 : PA.Covered 1 (OZ.Valid 1 w347.low w347.t w347.y w347.r w347.cap) (P33.root 1) :=
  Night6836Tree.sound w347 pick347 1 t9130 _ k347_1_14
private theorem k347_2_0 : check w347 pick347 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k347_2_1 : check w347 pick347 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k347_2_2 : check w347 pick347 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w347 pick347 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k347_2_0 k347_2_1
theorem cov347_2 : PA.Covered 2 (OZ.Valid 2 w347.low w347.t w347.y w347.r w347.cap) (P33.root 2) :=
  Night6836Tree.sound w347 pick347 2 t9134 _ k347_2_2
theorem cov347_3 : PA.Covered 3 (OZ.Valid 3 w347.low w347.t w347.y w347.r w347.cap) (P33.root 3) :=
  Night6836Tree.sound w347 pick347 3 t564 _ (by decide +kernel)
theorem cov347_4 : PA.Covered 4 (OZ.Valid 4 w347.low w347.t w347.y w347.r w347.cap) (P33.root 4) :=
  Night6836Tree.sound w347 pick347 4 t565 _ (by decide +kernel)
theorem cov347_5 : PA.Covered 5 (OZ.Valid 5 w347.low w347.t w347.y w347.r w347.cap) (P33.root 5) :=
  Night6836Tree.sound w347 pick347 5 t566 _ (by decide +kernel)
theorem cov347_6 : PA.Covered 6 (OZ.Valid 6 w347.low w347.t w347.y w347.r w347.cap) (P33.root 6) :=
  Night6836Tree.sound w347 pick347 6 t567 _ (by decide +kernel)
theorem cov347_7 : PA.Covered 7 (OZ.Valid 7 w347.low w347.t w347.y w347.r w347.cap) (P33.root 7) :=
  Night6836Tree.sound w347 pick347 7 t568 _ (by decide +kernel)
theorem window347 : P33.WindowCount w347 := by
  apply P33.window_count w347 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov347_1
  · exact cov347_2
  · exact cov347_3
  · exact cov347_4
  · exact cov347_5
  · exact cov347_6
  · exact cov347_7
def w348 : P33.Window := ⟨6,33,7888,7852,240814847535324884,22005,12000,5000000,81920000000⟩
def h348_0 : Height w348 := ⟨22005,12000,by decide +kernel⟩
def h348_1 : Height w348 := ⟨28636,9000,by decide +kernel⟩
def pick348 (cl : ℕ) : Height w348 := if cl<70 then (h348_0) else (h348_1)
private theorem k348_1_0 : check w348 pick348 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k348_1_1 : check w348 pick348 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k348_1_2 : check w348 pick348 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w348 pick348 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k348_1_0 k348_1_1
private theorem k348_1_3 : check w348 pick348 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k348_1_4 : check w348 pick348 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k348_1_5 : check w348 pick348 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w348 pick348 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k348_1_3 k348_1_4
private theorem k348_1_6 : check w348 pick348 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w348 pick348 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k348_1_2 k348_1_5
private theorem k348_1_7 : check w348 pick348 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k348_1_8 : check w348 pick348 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k348_1_9 : check w348 pick348 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w348 pick348 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k348_1_7 k348_1_8
private theorem k348_1_10 : check w348 pick348 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k348_1_11 : check w348 pick348 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k348_1_12 : check w348 pick348 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w348 pick348 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k348_1_10 k348_1_11
private theorem k348_1_13 : check w348 pick348 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w348 pick348 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k348_1_9 k348_1_12
private theorem k348_1_14 : check w348 pick348 1 t9129 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w348 pick348 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t3549 k348_1_6 k348_1_13
theorem cov348_1 : PA.Covered 1 (OZ.Valid 1 w348.low w348.t w348.y w348.r w348.cap) (P33.root 1) :=
  Night6836Tree.sound w348 pick348 1 t9129 _ k348_1_14
theorem cov348_2 : PA.Covered 2 (OZ.Valid 2 w348.low w348.t w348.y w348.r w348.cap) (P33.root 2) :=
  Night6836Tree.sound w348 pick348 2 t5366 _ (by decide +kernel)
theorem cov348_3 : PA.Covered 3 (OZ.Valid 3 w348.low w348.t w348.y w348.r w348.cap) (P33.root 3) :=
  Night6836Tree.sound w348 pick348 3 t564 _ (by decide +kernel)
theorem cov348_4 : PA.Covered 4 (OZ.Valid 4 w348.low w348.t w348.y w348.r w348.cap) (P33.root 4) :=
  Night6836Tree.sound w348 pick348 4 t565 _ (by decide +kernel)
theorem cov348_5 : PA.Covered 5 (OZ.Valid 5 w348.low w348.t w348.y w348.r w348.cap) (P33.root 5) :=
  Night6836Tree.sound w348 pick348 5 t566 _ (by decide +kernel)
theorem cov348_6 : PA.Covered 6 (OZ.Valid 6 w348.low w348.t w348.y w348.r w348.cap) (P33.root 6) :=
  Night6836Tree.sound w348 pick348 6 t567 _ (by decide +kernel)
theorem cov348_7 : PA.Covered 7 (OZ.Valid 7 w348.low w348.t w348.y w348.r w348.cap) (P33.root 7) :=
  Night6836Tree.sound w348 pick348 7 t568 _ (by decide +kernel)
theorem window348 : P33.WindowCount w348 := by
  apply P33.window_count w348 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov348_1
  · exact cov348_2
  · exact cov348_3
  · exact cov348_4
  · exact cov348_5
  · exact cov348_6
  · exact cov348_7
def w349 : P33.Window := ⟨6,34,6833,5834,199083779518165363,26901,19000,5000000,81920000000⟩
def h349_0 : Height w349 := ⟨26901,19000,by decide +kernel⟩
def h349_1 : Height w349 := ⟨32872,15000,by decide +kernel⟩
def h349_2 : Height w349 := ⟨44221,11000,by decide +kernel⟩
def pick349 (cl : ℕ) : Height w349 := if cl<5 then (h349_0) else (if cl<257 then (h349_1) else (h349_2))
private theorem k349_1_0 : check w349 pick349 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k349_1_1 : check w349 pick349 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k349_1_2 : check w349 pick349 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w349 pick349 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k349_1_0 k349_1_1
private theorem k349_1_3 : check w349 pick349 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k349_1_4 : check w349 pick349 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k349_1_5 : check w349 pick349 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w349 pick349 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k349_1_3 k349_1_4
private theorem k349_1_6 : check w349 pick349 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w349 pick349 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k349_1_2 k349_1_5
private theorem k349_1_7 : check w349 pick349 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k349_1_8 : check w349 pick349 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k349_1_9 : check w349 pick349 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w349 pick349 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k349_1_7 k349_1_8
private theorem k349_1_10 : check w349 pick349 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k349_1_11 : check w349 pick349 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k349_1_12 : check w349 pick349 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w349 pick349 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k349_1_10 k349_1_11
private theorem k349_1_13 : check w349 pick349 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w349 pick349 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k349_1_9 k349_1_12
private theorem k349_1_14 : check w349 pick349 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w349 pick349 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k349_1_6 k349_1_13
theorem cov349_1 : PA.Covered 1 (OZ.Valid 1 w349.low w349.t w349.y w349.r w349.cap) (P33.root 1) :=
  Night6836Tree.sound w349 pick349 1 t9130 _ k349_1_14
private theorem k349_2_0 : check w349 pick349 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k349_2_1 : check w349 pick349 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k349_2_2 : check w349 pick349 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w349 pick349 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k349_2_0 k349_2_1
theorem cov349_2 : PA.Covered 2 (OZ.Valid 2 w349.low w349.t w349.y w349.r w349.cap) (P33.root 2) :=
  Night6836Tree.sound w349 pick349 2 t9134 _ k349_2_2
theorem cov349_3 : PA.Covered 3 (OZ.Valid 3 w349.low w349.t w349.y w349.r w349.cap) (P33.root 3) :=
  Night6836Tree.sound w349 pick349 3 t564 _ (by decide +kernel)
theorem cov349_4 : PA.Covered 4 (OZ.Valid 4 w349.low w349.t w349.y w349.r w349.cap) (P33.root 4) :=
  Night6836Tree.sound w349 pick349 4 t565 _ (by decide +kernel)
theorem cov349_5 : PA.Covered 5 (OZ.Valid 5 w349.low w349.t w349.y w349.r w349.cap) (P33.root 5) :=
  Night6836Tree.sound w349 pick349 5 t566 _ (by decide +kernel)
theorem cov349_6 : PA.Covered 6 (OZ.Valid 6 w349.low w349.t w349.y w349.r w349.cap) (P33.root 6) :=
  Night6836Tree.sound w349 pick349 6 t567 _ (by decide +kernel)
theorem cov349_7 : PA.Covered 7 (OZ.Valid 7 w349.low w349.t w349.y w349.r w349.cap) (P33.root 7) :=
  Night6836Tree.sound w349 pick349 7 t568 _ (by decide +kernel)
theorem window349 : P33.WindowCount w349 := by
  apply P33.window_count w349 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov349_1
  · exact cov349_2
  · exact cov349_3
  · exact cov349_4
  · exact cov349_5
  · exact cov349_6
  · exact cov349_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w350 : P33.Window := ⟨6,34,7851,7814,227737212470941602,19148,15000,5000000,81920000000⟩
def h350_0 : Height w350 := ⟨19148,15000,by decide +kernel⟩
def h350_1 : Height w350 := ⟨23144,12000,by decide +kernel⟩
def h350_2 : Height w350 := ⟨30027,9000,by decide +kernel⟩
def pick350 (cl : ℕ) : Height w350 := if cl<2 then (h350_0) else (if cl<83 then (h350_1) else (h350_2))
private theorem k350_1_0 : check w350 pick350 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k350_1_1 : check w350 pick350 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k350_1_2 : check w350 pick350 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w350 pick350 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k350_1_0 k350_1_1
private theorem k350_1_3 : check w350 pick350 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k350_1_4 : check w350 pick350 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k350_1_5 : check w350 pick350 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w350 pick350 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k350_1_3 k350_1_4
private theorem k350_1_6 : check w350 pick350 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w350 pick350 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k350_1_2 k350_1_5
private theorem k350_1_7 : check w350 pick350 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k350_1_8 : check w350 pick350 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k350_1_9 : check w350 pick350 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w350 pick350 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k350_1_7 k350_1_8
private theorem k350_1_10 : check w350 pick350 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k350_1_11 : check w350 pick350 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k350_1_12 : check w350 pick350 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w350 pick350 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k350_1_10 k350_1_11
private theorem k350_1_13 : check w350 pick350 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w350 pick350 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k350_1_9 k350_1_12
private theorem k350_1_14 : check w350 pick350 1 t9129 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w350 pick350 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t3549 k350_1_6 k350_1_13
theorem cov350_1 : PA.Covered 1 (OZ.Valid 1 w350.low w350.t w350.y w350.r w350.cap) (P33.root 1) :=
  Night6836Tree.sound w350 pick350 1 t9129 _ k350_1_14
private theorem k350_2_0 : check w350 pick350 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k350_2_1 : check w350 pick350 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k350_2_2 : check w350 pick350 2 t9136 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w350 pick350 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9135 k350_2_0 k350_2_1
theorem cov350_2 : PA.Covered 2 (OZ.Valid 2 w350.low w350.t w350.y w350.r w350.cap) (P33.root 2) :=
  Night6836Tree.sound w350 pick350 2 t9136 _ k350_2_2
theorem cov350_3 : PA.Covered 3 (OZ.Valid 3 w350.low w350.t w350.y w350.r w350.cap) (P33.root 3) :=
  Night6836Tree.sound w350 pick350 3 t564 _ (by decide +kernel)
theorem cov350_4 : PA.Covered 4 (OZ.Valid 4 w350.low w350.t w350.y w350.r w350.cap) (P33.root 4) :=
  Night6836Tree.sound w350 pick350 4 t565 _ (by decide +kernel)
theorem cov350_5 : PA.Covered 5 (OZ.Valid 5 w350.low w350.t w350.y w350.r w350.cap) (P33.root 5) :=
  Night6836Tree.sound w350 pick350 5 t566 _ (by decide +kernel)
theorem cov350_6 : PA.Covered 6 (OZ.Valid 6 w350.low w350.t w350.y w350.r w350.cap) (P33.root 6) :=
  Night6836Tree.sound w350 pick350 6 t567 _ (by decide +kernel)
theorem cov350_7 : PA.Covered 7 (OZ.Valid 7 w350.low w350.t w350.y w350.r w350.cap) (P33.root 7) :=
  Night6836Tree.sound w350 pick350 7 t568 _ (by decide +kernel)
theorem window350 : P33.WindowCount w350 := by
  apply P33.window_count w350 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov350_1
  · exact cov350_2
  · exact cov350_3
  · exact cov350_4
  · exact cov350_5
  · exact cov350_6
  · exact cov350_7
def w351 : P33.Window := ⟨6,35,7813,7012,232216400037441906,24400,15000,5000000,81920000000⟩
def h351_0 : Height w351 := ⟨24400,15000,by decide +kernel⟩
def h351_1 : Height w351 := ⟨29414,12000,by decide +kernel⟩
def h351_2 : Height w351 := ⟨38858,9000,by decide +kernel⟩
def pick351 (cl : ℕ) : Height w351 := if cl<14 then (h351_0) else (if cl<312 then (h351_1) else (h351_2))
private theorem k351_1_0 : check w351 pick351 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k351_1_1 : check w351 pick351 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k351_1_2 : check w351 pick351 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w351 pick351 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k351_1_0 k351_1_1
private theorem k351_1_3 : check w351 pick351 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k351_1_4 : check w351 pick351 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k351_1_5 : check w351 pick351 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w351 pick351 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k351_1_3 k351_1_4
private theorem k351_1_6 : check w351 pick351 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w351 pick351 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k351_1_2 k351_1_5
private theorem k351_1_7 : check w351 pick351 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k351_1_8 : check w351 pick351 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k351_1_9 : check w351 pick351 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w351 pick351 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k351_1_7 k351_1_8
private theorem k351_1_10 : check w351 pick351 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k351_1_11 : check w351 pick351 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k351_1_12 : check w351 pick351 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w351 pick351 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k351_1_10 k351_1_11
private theorem k351_1_13 : check w351 pick351 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w351 pick351 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k351_1_9 k351_1_12
private theorem k351_1_14 : check w351 pick351 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w351 pick351 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k351_1_6 k351_1_13
theorem cov351_1 : PA.Covered 1 (OZ.Valid 1 w351.low w351.t w351.y w351.r w351.cap) (P33.root 1) :=
  Night6836Tree.sound w351 pick351 1 t9130 _ k351_1_14
private theorem k351_2_0 : check w351 pick351 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k351_2_1 : check w351 pick351 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k351_2_2 : check w351 pick351 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w351 pick351 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k351_2_0 k351_2_1
theorem cov351_2 : PA.Covered 2 (OZ.Valid 2 w351.low w351.t w351.y w351.r w351.cap) (P33.root 2) :=
  Night6836Tree.sound w351 pick351 2 t9134 _ k351_2_2
theorem cov351_3 : PA.Covered 3 (OZ.Valid 3 w351.low w351.t w351.y w351.r w351.cap) (P33.root 3) :=
  Night6836Tree.sound w351 pick351 3 t564 _ (by decide +kernel)
theorem cov351_4 : PA.Covered 4 (OZ.Valid 4 w351.low w351.t w351.y w351.r w351.cap) (P33.root 4) :=
  Night6836Tree.sound w351 pick351 4 t565 _ (by decide +kernel)
theorem cov351_5 : PA.Covered 5 (OZ.Valid 5 w351.low w351.t w351.y w351.r w351.cap) (P33.root 5) :=
  Night6836Tree.sound w351 pick351 5 t566 _ (by decide +kernel)
theorem cov351_6 : PA.Covered 6 (OZ.Valid 6 w351.low w351.t w351.y w351.r w351.cap) (P33.root 6) :=
  Night6836Tree.sound w351 pick351 6 t567 _ (by decide +kernel)
theorem cov351_7 : PA.Covered 7 (OZ.Valid 7 w351.low w351.t w351.y w351.r w351.cap) (P33.root 7) :=
  Night6836Tree.sound w351 pick351 7 t568 _ (by decide +kernel)
theorem window351 : P33.WindowCount w351 := by
  apply P33.window_count w351 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov351_1
  · exact cov351_2
  · exact cov351_3
  · exact cov351_4
  · exact cov351_5
  · exact cov351_6
  · exact cov351_7
def w352 : P33.Window := ⟨6,36,7775,7737,236642672848298554,21246,15000,5000000,81920000000⟩
def h352_0 : Height w352 := ⟨21246,15000,by decide +kernel⟩
def h352_1 : Height w352 := ⟨25476,12000,by decide +kernel⟩
def h352_2 : Height w352 := ⟨32888,9000,by decide +kernel⟩
def pick352 (cl : ℕ) : Height w352 := if cl<4 then (h352_0) else (if cl<132 then (h352_1) else (h352_2))
private theorem k352_1_0 : check w352 pick352 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k352_1_1 : check w352 pick352 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k352_1_2 : check w352 pick352 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w352 pick352 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k352_1_0 k352_1_1
private theorem k352_1_3 : check w352 pick352 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k352_1_4 : check w352 pick352 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k352_1_5 : check w352 pick352 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w352 pick352 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k352_1_3 k352_1_4
private theorem k352_1_6 : check w352 pick352 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w352 pick352 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k352_1_2 k352_1_5
private theorem k352_1_7 : check w352 pick352 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k352_1_8 : check w352 pick352 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k352_1_9 : check w352 pick352 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w352 pick352 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k352_1_7 k352_1_8
private theorem k352_1_10 : check w352 pick352 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k352_1_11 : check w352 pick352 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k352_1_12 : check w352 pick352 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w352 pick352 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k352_1_10 k352_1_11
private theorem k352_1_13 : check w352 pick352 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w352 pick352 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k352_1_9 k352_1_12
private theorem k352_1_14 : check w352 pick352 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w352 pick352 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k352_1_6 k352_1_13
theorem cov352_1 : PA.Covered 1 (OZ.Valid 1 w352.low w352.t w352.y w352.r w352.cap) (P33.root 1) :=
  Night6836Tree.sound w352 pick352 1 t9130 _ k352_1_14
private theorem k352_2_0 : check w352 pick352 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k352_2_1 : check w352 pick352 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k352_2_2 : check w352 pick352 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w352 pick352 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k352_2_0 k352_2_1
theorem cov352_2 : PA.Covered 2 (OZ.Valid 2 w352.low w352.t w352.y w352.r w352.cap) (P33.root 2) :=
  Night6836Tree.sound w352 pick352 2 t9134 _ k352_2_2
theorem cov352_3 : PA.Covered 3 (OZ.Valid 3 w352.low w352.t w352.y w352.r w352.cap) (P33.root 3) :=
  Night6836Tree.sound w352 pick352 3 t564 _ (by decide +kernel)
theorem cov352_4 : PA.Covered 4 (OZ.Valid 4 w352.low w352.t w352.y w352.r w352.cap) (P33.root 4) :=
  Night6836Tree.sound w352 pick352 4 t565 _ (by decide +kernel)
theorem cov352_5 : PA.Covered 5 (OZ.Valid 5 w352.low w352.t w352.y w352.r w352.cap) (P33.root 5) :=
  Night6836Tree.sound w352 pick352 5 t566 _ (by decide +kernel)
theorem cov352_6 : PA.Covered 6 (OZ.Valid 6 w352.low w352.t w352.y w352.r w352.cap) (P33.root 6) :=
  Night6836Tree.sound w352 pick352 6 t567 _ (by decide +kernel)
theorem cov352_7 : PA.Covered 7 (OZ.Valid 7 w352.low w352.t w352.y w352.r w352.cap) (P33.root 7) :=
  Night6836Tree.sound w352 pick352 7 t568 _ (by decide +kernel)
theorem window352 : P33.WindowCount w352 := by
  apply P33.window_count w352 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov352_1
  · exact cov352_2
  · exact cov352_3
  · exact cov352_4
  · exact cov352_5
  · exact cov352_6
  · exact cov352_7
def w353 : P33.Window := ⟨6,37,5636,4637,191503616054585750,39450,23000,5000000,81920000000⟩
def h353_0 : Height w353 := ⟨39450,23000,by decide +kernel⟩
def h353_1 : Height w353 := ⟨45982,19000,by decide +kernel⟩
def h353_2 : Height w353 := ⟨56724,15000,by decide +kernel⟩
def pick353 (cl : ℕ) : Height w353 := if cl<13 then (h353_0) else (if cl<192 then (h353_1) else (h353_2))
private theorem k353_1_0 : check w353 pick353 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k353_1_1 : check w353 pick353 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k353_1_2 : check w353 pick353 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w353 pick353 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k353_1_0 k353_1_1
private theorem k353_1_3 : check w353 pick353 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k353_1_4 : check w353 pick353 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k353_1_5 : check w353 pick353 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w353 pick353 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k353_1_3 k353_1_4
private theorem k353_1_6 : check w353 pick353 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w353 pick353 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k353_1_2 k353_1_5
private theorem k353_1_7 : check w353 pick353 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k353_1_8 : check w353 pick353 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k353_1_9 : check w353 pick353 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w353 pick353 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k353_1_7 k353_1_8
private theorem k353_1_10 : check w353 pick353 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k353_1_11 : check w353 pick353 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k353_1_12 : check w353 pick353 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w353 pick353 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k353_1_10 k353_1_11
private theorem k353_1_13 : check w353 pick353 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w353 pick353 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k353_1_9 k353_1_12
private theorem k353_1_14 : check w353 pick353 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w353 pick353 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k353_1_6 k353_1_13
theorem cov353_1 : PA.Covered 1 (OZ.Valid 1 w353.low w353.t w353.y w353.r w353.cap) (P33.root 1) :=
  Night6836Tree.sound w353 pick353 1 t9130 _ k353_1_14
theorem cov353_2 : PA.Covered 2 (OZ.Valid 2 w353.low w353.t w353.y w353.r w353.cap) (P33.root 2) :=
  Night6836Tree.sound w353 pick353 2 t9132 _ (by decide +kernel)
theorem cov353_3 : PA.Covered 3 (OZ.Valid 3 w353.low w353.t w353.y w353.r w353.cap) (P33.root 3) :=
  Night6836Tree.sound w353 pick353 3 t564 _ (by decide +kernel)
theorem cov353_4 : PA.Covered 4 (OZ.Valid 4 w353.low w353.t w353.y w353.r w353.cap) (P33.root 4) :=
  Night6836Tree.sound w353 pick353 4 t565 _ (by decide +kernel)
theorem cov353_5 : PA.Covered 5 (OZ.Valid 5 w353.low w353.t w353.y w353.r w353.cap) (P33.root 5) :=
  Night6836Tree.sound w353 pick353 5 t566 _ (by decide +kernel)
theorem cov353_6 : PA.Covered 6 (OZ.Valid 6 w353.low w353.t w353.y w353.r w353.cap) (P33.root 6) :=
  Night6836Tree.sound w353 pick353 6 t567 _ (by decide +kernel)
theorem cov353_7 : PA.Covered 7 (OZ.Valid 7 w353.low w353.t w353.y w353.r w353.cap) (P33.root 7) :=
  Night6836Tree.sound w353 pick353 7 t2134 _ (by decide +kernel)
theorem window353 : P33.WindowCount w353 := by
  apply P33.window_count w353 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov353_1
  · exact cov353_2
  · exact cov353_3
  · exact cov353_4
  · exact cov353_5
  · exact cov353_6
  · exact cov353_7
def w354 : P33.Window := ⟨6,37,7736,7698,240985822498560409,22318,15000,5000000,81920000000⟩
def h354_0 : Height w354 := ⟨22318,15000,by decide +kernel⟩
def h354_1 : Height w354 := ⟨26672,12000,by decide +kernel⟩
def h354_2 : Height w354 := ⟨34360,9000,by decide +kernel⟩
def pick354 (cl : ℕ) : Height w354 := if cl<5 then (h354_0) else (if cl<152 then (h354_1) else (h354_2))
private theorem k354_1_0 : check w354 pick354 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k354_1_1 : check w354 pick354 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k354_1_2 : check w354 pick354 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w354 pick354 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k354_1_0 k354_1_1
private theorem k354_1_3 : check w354 pick354 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k354_1_4 : check w354 pick354 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k354_1_5 : check w354 pick354 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w354 pick354 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k354_1_3 k354_1_4
private theorem k354_1_6 : check w354 pick354 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w354 pick354 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k354_1_2 k354_1_5
private theorem k354_1_7 : check w354 pick354 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k354_1_8 : check w354 pick354 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k354_1_9 : check w354 pick354 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w354 pick354 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k354_1_7 k354_1_8
private theorem k354_1_10 : check w354 pick354 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k354_1_11 : check w354 pick354 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k354_1_12 : check w354 pick354 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w354 pick354 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k354_1_10 k354_1_11
private theorem k354_1_13 : check w354 pick354 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w354 pick354 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k354_1_9 k354_1_12
private theorem k354_1_14 : check w354 pick354 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w354 pick354 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k354_1_6 k354_1_13
theorem cov354_1 : PA.Covered 1 (OZ.Valid 1 w354.low w354.t w354.y w354.r w354.cap) (P33.root 1) :=
  Night6836Tree.sound w354 pick354 1 t9130 _ k354_1_14
private theorem k354_2_0 : check w354 pick354 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k354_2_1 : check w354 pick354 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k354_2_2 : check w354 pick354 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w354 pick354 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k354_2_0 k354_2_1
theorem cov354_2 : PA.Covered 2 (OZ.Valid 2 w354.low w354.t w354.y w354.r w354.cap) (P33.root 2) :=
  Night6836Tree.sound w354 pick354 2 t9134 _ k354_2_2
theorem cov354_3 : PA.Covered 3 (OZ.Valid 3 w354.low w354.t w354.y w354.r w354.cap) (P33.root 3) :=
  Night6836Tree.sound w354 pick354 3 t564 _ (by decide +kernel)
theorem cov354_4 : PA.Covered 4 (OZ.Valid 4 w354.low w354.t w354.y w354.r w354.cap) (P33.root 4) :=
  Night6836Tree.sound w354 pick354 4 t565 _ (by decide +kernel)
theorem cov354_5 : PA.Covered 5 (OZ.Valid 5 w354.low w354.t w354.y w354.r w354.cap) (P33.root 5) :=
  Night6836Tree.sound w354 pick354 5 t566 _ (by decide +kernel)
theorem cov354_6 : PA.Covered 6 (OZ.Valid 6 w354.low w354.t w354.y w354.r w354.cap) (P33.root 6) :=
  Night6836Tree.sound w354 pick354 6 t567 _ (by decide +kernel)
theorem cov354_7 : PA.Covered 7 (OZ.Valid 7 w354.low w354.t w354.y w354.r w354.cap) (P33.root 7) :=
  Night6836Tree.sound w354 pick354 7 t568 _ (by decide +kernel)
theorem window354 : P33.WindowCount w354 := by
  apply P33.window_count w354 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov354_1
  · exact cov354_2
  · exact cov354_3
  · exact cov354_4
  · exact cov354_5
  · exact cov354_6
  · exact cov354_7
def w355 : P33.Window := ⟨6,38,7697,7659,243739155536872730,23406,15000,5000000,81920000000⟩
def h355_0 : Height w355 := ⟨23406,15000,by decide +kernel⟩
def h355_1 : Height w355 := ⟨27884,12000,by decide +kernel⟩
def h355_2 : Height w355 := ⟨35858,9000,by decide +kernel⟩
def pick355 (cl : ℕ) : Height w355 := if cl<5 then (h355_0) else (if cl<177 then (h355_1) else (h355_2))
private theorem k355_1_0 : check w355 pick355 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k355_1_1 : check w355 pick355 1 t5141 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k355_1_2 : check w355 pick355 1 t9137 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w355 pick355 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t5141 k355_1_0 k355_1_1
private theorem k355_1_3 : check w355 pick355 1 t6095 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k355_1_4 : check w355 pick355 1 t9139 ⟨1,7,2,16,1,52,111,145⟩ = true := by decide +kernel
private theorem k355_1_5 : check w355 pick355 1 t9140 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w355 pick355 1 ⟨1,7,2,16,1,52,84,145⟩ 3 110 t6095 t9139 k355_1_3 k355_1_4
private theorem k355_1_6 : check w355 pick355 1 t9141 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w355 pick355 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t9137 t9140 k355_1_2 k355_1_5
private theorem k355_1_7 : check w355 pick355 1 t2373 ⟨1,7,2,16,1,52,146,179⟩ = true := by decide +kernel
private theorem k355_1_8 : check w355 pick355 1 t9142 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k355_1_9 : check w355 pick355 1 t9143 ⟨1,7,2,16,1,52,146,206⟩ = true := glue w355 pick355 1 ⟨1,7,2,16,1,52,146,206⟩ 3 179 t2373 t9142 k355_1_7 k355_1_8
private theorem k355_1_10 : check w355 pick355 1 t9148 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k355_1_11 : check w355 pick355 1 t9150 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k355_1_12 : check w355 pick355 1 t9151 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w355 pick355 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t9148 t9150 k355_1_10 k355_1_11
private theorem k355_1_13 : check w355 pick355 1 t9152 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w355 pick355 1 ⟨1,7,2,16,1,52,146,450⟩ 3 206 t9143 t9151 k355_1_9 k355_1_12
private theorem k355_1_14 : check w355 pick355 1 t9153 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w355 pick355 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t9141 t9152 k355_1_6 k355_1_13
theorem cov355_1 : PA.Covered 1 (OZ.Valid 1 w355.low w355.t w355.y w355.r w355.cap) (P33.root 1) :=
  Night6836Tree.sound w355 pick355 1 t9153 _ k355_1_14
private theorem k355_2_0 : check w355 pick355 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k355_2_1 : check w355 pick355 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k355_2_2 : check w355 pick355 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w355 pick355 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k355_2_0 k355_2_1
theorem cov355_2 : PA.Covered 2 (OZ.Valid 2 w355.low w355.t w355.y w355.r w355.cap) (P33.root 2) :=
  Night6836Tree.sound w355 pick355 2 t9134 _ k355_2_2
theorem cov355_3 : PA.Covered 3 (OZ.Valid 3 w355.low w355.t w355.y w355.r w355.cap) (P33.root 3) :=
  Night6836Tree.sound w355 pick355 3 t564 _ (by decide +kernel)
theorem cov355_4 : PA.Covered 4 (OZ.Valid 4 w355.low w355.t w355.y w355.r w355.cap) (P33.root 4) :=
  Night6836Tree.sound w355 pick355 4 t565 _ (by decide +kernel)
theorem cov355_5 : PA.Covered 5 (OZ.Valid 5 w355.low w355.t w355.y w355.r w355.cap) (P33.root 5) :=
  Night6836Tree.sound w355 pick355 5 t566 _ (by decide +kernel)
theorem cov355_6 : PA.Covered 6 (OZ.Valid 6 w355.low w355.t w355.y w355.r w355.cap) (P33.root 6) :=
  Night6836Tree.sound w355 pick355 6 t567 _ (by decide +kernel)
theorem cov355_7 : PA.Covered 7 (OZ.Valid 7 w355.low w355.t w355.y w355.r w355.cap) (P33.root 7) :=
  Night6836Tree.sound w355 pick355 7 t568 _ (by decide +kernel)
theorem window355 : P33.WindowCount w355 := by
  apply P33.window_count w355 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov355_1
  · exact cov355_2
  · exact cov355_3
  · exact cov355_4
  · exact cov355_5
  · exact cov355_6
  · exact cov355_7
def w356 : P33.Window := ⟨6,39,5338,4339,187993943422495958,42203,27000,5000000,81920000000⟩
def h356_0 : Height w356 := ⟨42203,27000,by decide +kernel⟩
def h356_1 : Height w356 := ⟨47718,23000,by decide +kernel⟩
def h356_2 : Height w356 := ⟨55540,19000,by decide +kernel⟩
def h356_3 : Height w356 := ⟨69049,15000,by decide +kernel⟩
def pick356 (cl : ℕ) : Height w356 := if cl<36 then (if cl<3 then (h356_0) else (h356_1)) else (if cl<549 then (h356_2) else (h356_3))
private theorem k356_1_0 : check w356 pick356 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k356_1_1 : check w356 pick356 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k356_1_2 : check w356 pick356 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w356 pick356 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k356_1_0 k356_1_1
private theorem k356_1_3 : check w356 pick356 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k356_1_4 : check w356 pick356 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k356_1_5 : check w356 pick356 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w356 pick356 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k356_1_3 k356_1_4
private theorem k356_1_6 : check w356 pick356 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w356 pick356 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k356_1_2 k356_1_5
private theorem k356_1_7 : check w356 pick356 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k356_1_8 : check w356 pick356 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k356_1_9 : check w356 pick356 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w356 pick356 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k356_1_7 k356_1_8
private theorem k356_1_10 : check w356 pick356 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k356_1_11 : check w356 pick356 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k356_1_12 : check w356 pick356 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w356 pick356 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k356_1_10 k356_1_11
private theorem k356_1_13 : check w356 pick356 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w356 pick356 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k356_1_9 k356_1_12
private theorem k356_1_14 : check w356 pick356 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w356 pick356 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k356_1_6 k356_1_13
theorem cov356_1 : PA.Covered 1 (OZ.Valid 1 w356.low w356.t w356.y w356.r w356.cap) (P33.root 1) :=
  Night6836Tree.sound w356 pick356 1 t9130 _ k356_1_14
theorem cov356_2 : PA.Covered 2 (OZ.Valid 2 w356.low w356.t w356.y w356.r w356.cap) (P33.root 2) :=
  Night6836Tree.sound w356 pick356 2 t9132 _ (by decide +kernel)
theorem cov356_3 : PA.Covered 3 (OZ.Valid 3 w356.low w356.t w356.y w356.r w356.cap) (P33.root 3) :=
  Night6836Tree.sound w356 pick356 3 t564 _ (by decide +kernel)
theorem cov356_4 : PA.Covered 4 (OZ.Valid 4 w356.low w356.t w356.y w356.r w356.cap) (P33.root 4) :=
  Night6836Tree.sound w356 pick356 4 t565 _ (by decide +kernel)
theorem cov356_5 : PA.Covered 5 (OZ.Valid 5 w356.low w356.t w356.y w356.r w356.cap) (P33.root 5) :=
  Night6836Tree.sound w356 pick356 5 t566 _ (by decide +kernel)
theorem cov356_6 : PA.Covered 6 (OZ.Valid 6 w356.low w356.t w356.y w356.r w356.cap) (P33.root 6) :=
  Night6836Tree.sound w356 pick356 6 t567 _ (by decide +kernel)
theorem cov356_7 : PA.Covered 7 (OZ.Valid 7 w356.low w356.t w356.y w356.r w356.cap) (P33.root 7) :=
  Night6836Tree.sound w356 pick356 7 t2134 _ (by decide +kernel)
theorem window356 : P33.WindowCount w356 := by
  apply P33.window_count w356 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov356_1
  · exact cov356_2
  · exact cov356_3
  · exact cov356_4
  · exact cov356_5
  · exact cov356_6
  · exact cov356_7
def w357 : P33.Window := ⟨6,39,7658,7398,243970819795304129,25822,15000,5000000,81920000000⟩
def h357_0 : Height w357 := ⟨25822,15000,by decide +kernel⟩
def h357_1 : Height w357 := ⟨30702,12000,by decide +kernel⟩
def h357_2 : Height w357 := ⟨39656,9000,by decide +kernel⟩
def pick357 (cl : ℕ) : Height w357 := if cl<13 then (h357_0) else (if cl<278 then (h357_1) else (h357_2))
private theorem k357_1_0 : check w357 pick357 1 t9154 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k357_1_1 : check w357 pick357 1 t5141 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k357_1_2 : check w357 pick357 1 t9155 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w357 pick357 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t9154 t5141 k357_1_0 k357_1_1
private theorem k357_1_3 : check w357 pick357 1 t9162 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k357_1_4 : check w357 pick357 1 t9180 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k357_1_5 : check w357 pick357 1 t9181 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w357 pick357 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t9162 t9180 k357_1_3 k357_1_4
private theorem k357_1_6 : check w357 pick357 1 t9182 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w357 pick357 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t9155 t9181 k357_1_2 k357_1_5
private theorem k357_1_7 : check w357 pick357 1 t5178 ⟨1,7,2,16,1,52,146,179⟩ = true := by decide +kernel
private theorem k357_1_8 : check w357 pick357 1 t2374 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k357_1_9 : check w357 pick357 1 t5179 ⟨1,7,2,16,1,52,146,206⟩ = true := glue w357 pick357 1 ⟨1,7,2,16,1,52,146,206⟩ 3 179 t5178 t2374 k357_1_7 k357_1_8
private theorem k357_1_10 : check w357 pick357 1 t2385 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k357_1_11 : check w357 pick357 1 t9150 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k357_1_12 : check w357 pick357 1 t9183 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w357 pick357 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t2385 t9150 k357_1_10 k357_1_11
private theorem k357_1_13 : check w357 pick357 1 t9184 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w357 pick357 1 ⟨1,7,2,16,1,52,146,450⟩ 3 206 t5179 t9183 k357_1_9 k357_1_12
private theorem k357_1_14 : check w357 pick357 1 t9185 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w357 pick357 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t9182 t9184 k357_1_6 k357_1_13
theorem cov357_1 : PA.Covered 1 (OZ.Valid 1 w357.low w357.t w357.y w357.r w357.cap) (P33.root 1) :=
  Night6836Tree.sound w357 pick357 1 t9185 _ k357_1_14
private theorem k357_2_0 : check w357 pick357 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k357_2_1 : check w357 pick357 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k357_2_2 : check w357 pick357 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w357 pick357 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k357_2_0 k357_2_1
theorem cov357_2 : PA.Covered 2 (OZ.Valid 2 w357.low w357.t w357.y w357.r w357.cap) (P33.root 2) :=
  Night6836Tree.sound w357 pick357 2 t9134 _ k357_2_2
theorem cov357_3 : PA.Covered 3 (OZ.Valid 3 w357.low w357.t w357.y w357.r w357.cap) (P33.root 3) :=
  Night6836Tree.sound w357 pick357 3 t564 _ (by decide +kernel)
theorem cov357_4 : PA.Covered 4 (OZ.Valid 4 w357.low w357.t w357.y w357.r w357.cap) (P33.root 4) :=
  Night6836Tree.sound w357 pick357 4 t565 _ (by decide +kernel)
theorem cov357_5 : PA.Covered 5 (OZ.Valid 5 w357.low w357.t w357.y w357.r w357.cap) (P33.root 5) :=
  Night6836Tree.sound w357 pick357 5 t566 _ (by decide +kernel)
theorem cov357_6 : PA.Covered 6 (OZ.Valid 6 w357.low w357.t w357.y w357.r w357.cap) (P33.root 6) :=
  Night6836Tree.sound w357 pick357 6 t567 _ (by decide +kernel)
theorem cov357_7 : PA.Covered 7 (OZ.Valid 7 w357.low w357.t w357.y w357.r w357.cap) (P33.root 7) :=
  Night6836Tree.sound w357 pick357 7 t568 _ (by decide +kernel)
theorem window357 : P33.WindowCount w357 := by
  apply P33.window_count w357 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov357_1
  · exact cov357_2
  · exact cov357_3
  · exact cov357_4
  · exact cov357_5
  · exact cov357_6
  · exact cov357_7
def w358 : P33.Window := ⟨6,40,5339,4340,191347478353622848,43730,27000,5000000,81920000000⟩
def h358_0 : Height w358 := ⟨43730,27000,by decide +kernel⟩
def h358_1 : Height w358 := ⟨49339,23000,by decide +kernel⟩
def h358_2 : Height w358 := ⟨57316,19000,by decide +kernel⟩
def h358_3 : Height w358 := ⟨71128,15000,by decide +kernel⟩
def pick358 (cl : ℕ) : Height w358 := if cl<37 then (if cl<4 then (h358_0) else (h358_1)) else (if cl<644 then (h358_2) else (h358_3))
private theorem k358_1_0 : check w358 pick358 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k358_1_1 : check w358 pick358 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k358_1_2 : check w358 pick358 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w358 pick358 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k358_1_0 k358_1_1
private theorem k358_1_3 : check w358 pick358 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k358_1_4 : check w358 pick358 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k358_1_5 : check w358 pick358 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w358 pick358 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k358_1_3 k358_1_4
private theorem k358_1_6 : check w358 pick358 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w358 pick358 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k358_1_2 k358_1_5
private theorem k358_1_7 : check w358 pick358 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k358_1_8 : check w358 pick358 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k358_1_9 : check w358 pick358 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w358 pick358 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k358_1_7 k358_1_8
private theorem k358_1_10 : check w358 pick358 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k358_1_11 : check w358 pick358 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k358_1_12 : check w358 pick358 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w358 pick358 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k358_1_10 k358_1_11
private theorem k358_1_13 : check w358 pick358 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w358 pick358 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k358_1_9 k358_1_12
private theorem k358_1_14 : check w358 pick358 1 t9129 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w358 pick358 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t3549 k358_1_6 k358_1_13
theorem cov358_1 : PA.Covered 1 (OZ.Valid 1 w358.low w358.t w358.y w358.r w358.cap) (P33.root 1) :=
  Night6836Tree.sound w358 pick358 1 t9129 _ k358_1_14
theorem cov358_2 : PA.Covered 2 (OZ.Valid 2 w358.low w358.t w358.y w358.r w358.cap) (P33.root 2) :=
  Night6836Tree.sound w358 pick358 2 t9132 _ (by decide +kernel)
theorem cov358_3 : PA.Covered 3 (OZ.Valid 3 w358.low w358.t w358.y w358.r w358.cap) (P33.root 3) :=
  Night6836Tree.sound w358 pick358 3 t564 _ (by decide +kernel)
theorem cov358_4 : PA.Covered 4 (OZ.Valid 4 w358.low w358.t w358.y w358.r w358.cap) (P33.root 4) :=
  Night6836Tree.sound w358 pick358 4 t565 _ (by decide +kernel)
theorem cov358_5 : PA.Covered 5 (OZ.Valid 5 w358.low w358.t w358.y w358.r w358.cap) (P33.root 5) :=
  Night6836Tree.sound w358 pick358 5 t566 _ (by decide +kernel)
theorem cov358_6 : PA.Covered 6 (OZ.Valid 6 w358.low w358.t w358.y w358.r w358.cap) (P33.root 6) :=
  Night6836Tree.sound w358 pick358 6 t567 _ (by decide +kernel)
theorem cov358_7 : PA.Covered 7 (OZ.Valid 7 w358.low w358.t w358.y w358.r w358.cap) (P33.root 7) :=
  Night6836Tree.sound w358 pick358 7 t2134 _ (by decide +kernel)
theorem window358 : P33.WindowCount w358 := by
  apply P33.window_count w358 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov358_1
  · exact cov358_2
  · exact cov358_3
  · exact cov358_4
  · exact cov358_5
  · exact cov358_6
  · exact cov358_7
def w359 : P33.Window := ⟨6,40,7617,7578,234899622955860268,25643,15000,5000000,81920000000⟩
def h359_0 : Height w359 := ⟨25643,15000,by decide +kernel⟩
def h359_1 : Height w359 := ⟨30387,12000,by decide +kernel⟩
def h359_2 : Height w359 := ⟨38966,9000,by decide +kernel⟩
def pick359 (cl : ℕ) : Height w359 := if cl<10 then (h359_0) else (if cl<257 then (h359_1) else (h359_2))
private theorem k359_1_0 : check w359 pick359 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k359_1_1 : check w359 pick359 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k359_1_2 : check w359 pick359 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w359 pick359 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k359_1_0 k359_1_1
private theorem k359_1_3 : check w359 pick359 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k359_1_4 : check w359 pick359 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k359_1_5 : check w359 pick359 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w359 pick359 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k359_1_3 k359_1_4
private theorem k359_1_6 : check w359 pick359 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w359 pick359 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k359_1_2 k359_1_5
private theorem k359_1_7 : check w359 pick359 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k359_1_8 : check w359 pick359 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k359_1_9 : check w359 pick359 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w359 pick359 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k359_1_7 k359_1_8
private theorem k359_1_10 : check w359 pick359 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k359_1_11 : check w359 pick359 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k359_1_12 : check w359 pick359 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w359 pick359 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k359_1_10 k359_1_11
private theorem k359_1_13 : check w359 pick359 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w359 pick359 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k359_1_9 k359_1_12
private theorem k359_1_14 : check w359 pick359 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w359 pick359 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k359_1_6 k359_1_13
theorem cov359_1 : PA.Covered 1 (OZ.Valid 1 w359.low w359.t w359.y w359.r w359.cap) (P33.root 1) :=
  Night6836Tree.sound w359 pick359 1 t9213 _ k359_1_14
private theorem k359_2_0 : check w359 pick359 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k359_2_1 : check w359 pick359 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k359_2_2 : check w359 pick359 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w359 pick359 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k359_2_0 k359_2_1
theorem cov359_2 : PA.Covered 2 (OZ.Valid 2 w359.low w359.t w359.y w359.r w359.cap) (P33.root 2) :=
  Night6836Tree.sound w359 pick359 2 t9134 _ k359_2_2
theorem cov359_3 : PA.Covered 3 (OZ.Valid 3 w359.low w359.t w359.y w359.r w359.cap) (P33.root 3) :=
  Night6836Tree.sound w359 pick359 3 t564 _ (by decide +kernel)
theorem cov359_4 : PA.Covered 4 (OZ.Valid 4 w359.low w359.t w359.y w359.r w359.cap) (P33.root 4) :=
  Night6836Tree.sound w359 pick359 4 t565 _ (by decide +kernel)
theorem cov359_5 : PA.Covered 5 (OZ.Valid 5 w359.low w359.t w359.y w359.r w359.cap) (P33.root 5) :=
  Night6836Tree.sound w359 pick359 5 t566 _ (by decide +kernel)
theorem cov359_6 : PA.Covered 6 (OZ.Valid 6 w359.low w359.t w359.y w359.r w359.cap) (P33.root 6) :=
  Night6836Tree.sound w359 pick359 6 t567 _ (by decide +kernel)
theorem cov359_7 : PA.Covered 7 (OZ.Valid 7 w359.low w359.t w359.y w359.r w359.cap) (P33.root 7) :=
  Night6836Tree.sound w359 pick359 7 t568 _ (by decide +kernel)
theorem window359 : P33.WindowCount w359 := by
  apply P33.window_count w359 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov359_1
  · exact cov359_2
  · exact cov359_3
  · exact cov359_4
  · exact cov359_5
  · exact cov359_6
  · exact cov359_7
end ProximityPrize.SubmissionLower.Night6836Bank
