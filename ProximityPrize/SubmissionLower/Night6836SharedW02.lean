/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w60 : P33.Window := ⟨10,34,5233,4234,203322326216979011,34127,35000,5000000,81920000000⟩
def h60_0 : Height w60 := ⟨34127,35000,by decide +kernel⟩
def h60_1 : Height w60 := ⟨39724,31000,by decide +kernel⟩
def h60_2 : Height w60 := ⟨47197,27000,by decide +kernel⟩
def h60_3 : Height w60 := ⟨58525,23000,by decide +kernel⟩
def pick60 (cl : ℕ) : Height w60 := if cl<32 then (if cl<4 then (h60_0) else (h60_1)) else (if cl<260 then (h60_2) else (h60_3))
private theorem k60_1_0 : check w60 pick60 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k60_1_1 : check w60 pick60 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k60_1_2 : check w60 pick60 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w60 pick60 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k60_1_0 k60_1_1
private theorem k60_1_3 : check w60 pick60 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k60_1_4 : check w60 pick60 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k60_1_5 : check w60 pick60 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w60 pick60 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k60_1_3 k60_1_4
private theorem k60_1_6 : check w60 pick60 1 t2814 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w60 pick60 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2813 k60_1_2 k60_1_5
private theorem k60_1_7 : check w60 pick60 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k60_1_8 : check w60 pick60 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k60_1_9 : check w60 pick60 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w60 pick60 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k60_1_7 k60_1_8
private theorem k60_1_10 : check w60 pick60 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k60_1_11 : check w60 pick60 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k60_1_12 : check w60 pick60 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w60 pick60 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k60_1_10 k60_1_11
private theorem k60_1_13 : check w60 pick60 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w60 pick60 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k60_1_9 k60_1_12
private theorem k60_1_14 : check w60 pick60 1 t2815 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w60 pick60 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2814 t2461 k60_1_6 k60_1_13
theorem cov60_1 : PA.Covered 1 (OZ.Valid 1 w60.low w60.t w60.y w60.r w60.cap) (P33.root 1) :=
  Night6836Tree.sound w60 pick60 1 t2815 _ k60_1_14
private theorem k60_2_0 : check w60 pick60 2 t3223 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k60_2_1 : check w60 pick60 2 t3235 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k60_2_2 : check w60 pick60 2 t3236 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w60 pick60 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t3223 t3235 k60_2_0 k60_2_1
theorem cov60_2 : PA.Covered 2 (OZ.Valid 2 w60.low w60.t w60.y w60.r w60.cap) (P33.root 2) :=
  Night6836Tree.sound w60 pick60 2 t3236 _ k60_2_2
theorem cov60_3 : PA.Covered 3 (OZ.Valid 3 w60.low w60.t w60.y w60.r w60.cap) (P33.root 3) :=
  Night6836Tree.sound w60 pick60 3 t564 _ (by decide +kernel)
theorem cov60_4 : PA.Covered 4 (OZ.Valid 4 w60.low w60.t w60.y w60.r w60.cap) (P33.root 4) :=
  Night6836Tree.sound w60 pick60 4 t565 _ (by decide +kernel)
theorem cov60_5 : PA.Covered 5 (OZ.Valid 5 w60.low w60.t w60.y w60.r w60.cap) (P33.root 5) :=
  Night6836Tree.sound w60 pick60 5 t566 _ (by decide +kernel)
theorem cov60_6 : PA.Covered 6 (OZ.Valid 6 w60.low w60.t w60.y w60.r w60.cap) (P33.root 6) :=
  Night6836Tree.sound w60 pick60 6 t567 _ (by decide +kernel)
theorem cov60_7 : PA.Covered 7 (OZ.Valid 7 w60.low w60.t w60.y w60.r w60.cap) (P33.root 7) :=
  Night6836Tree.sound w60 pick60 7 t2134 _ (by decide +kernel)
theorem window60 : P33.WindowCount w60 := by
  apply P33.window_count w60 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov60_1
  · exact cov60_2
  · exact cov60_3
  · exact cov60_4
  · exact cov60_5
  · exact cov60_6
  · exact cov60_7
def w61 : P33.Window := ⟨10,34,7282,7239,245819482376095537,19330,21000,5000000,81920000000⟩
def h61_0 : Height w61 := ⟨19330,21000,by decide +kernel⟩
def h61_1 : Height w61 := ⟨23469,18000,by decide +kernel⟩
def h61_2 : Height w61 := ⟨29552,15000,by decide +kernel⟩
def h61_3 : Height w61 := ⟨40969,12000,by decide +kernel⟩
def pick61 (cl : ℕ) : Height w61 := if cl<41 then (if cl<3 then (h61_0) else (h61_1)) else (if cl<853 then (h61_2) else (h61_3))
private theorem k61_1_0 : check w61 pick61 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k61_1_1 : check w61 pick61 1 t3253 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k61_1_2 : check w61 pick61 1 t3254 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w61 pick61 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t3253 k61_1_0 k61_1_1
private theorem k61_1_3 : check w61 pick61 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k61_1_4 : check w61 pick61 1 t3195 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k61_1_5 : check w61 pick61 1 t3264 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w61 pick61 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t3195 k61_1_3 k61_1_4
private theorem k61_1_6 : check w61 pick61 1 t3265 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w61 pick61 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3254 t3264 k61_1_2 k61_1_5
private theorem k61_1_7 : check w61 pick61 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k61_1_8 : check w61 pick61 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k61_1_9 : check w61 pick61 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w61 pick61 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k61_1_7 k61_1_8
private theorem k61_1_10 : check w61 pick61 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k61_1_11 : check w61 pick61 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k61_1_12 : check w61 pick61 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w61 pick61 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k61_1_10 k61_1_11
private theorem k61_1_13 : check w61 pick61 1 t3201 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w61 pick61 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t1079 k61_1_9 k61_1_12
private theorem k61_1_14 : check w61 pick61 1 t3266 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w61 pick61 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3265 t3201 k61_1_6 k61_1_13
theorem cov61_1 : PA.Covered 1 (OZ.Valid 1 w61.low w61.t w61.y w61.r w61.cap) (P33.root 1) :=
  Night6836Tree.sound w61 pick61 1 t3266 _ k61_1_14
private theorem k61_2_0 : check w61 pick61 2 t3206 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k61_2_1 : check w61 pick61 2 t3280 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k61_2_2 : check w61 pick61 2 t3281 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w61 pick61 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t3206 t3280 k61_2_0 k61_2_1
theorem cov61_2 : PA.Covered 2 (OZ.Valid 2 w61.low w61.t w61.y w61.r w61.cap) (P33.root 2) :=
  Night6836Tree.sound w61 pick61 2 t3281 _ k61_2_2
theorem cov61_3 : PA.Covered 3 (OZ.Valid 3 w61.low w61.t w61.y w61.r w61.cap) (P33.root 3) :=
  Night6836Tree.sound w61 pick61 3 t564 _ (by decide +kernel)
theorem cov61_4 : PA.Covered 4 (OZ.Valid 4 w61.low w61.t w61.y w61.r w61.cap) (P33.root 4) :=
  Night6836Tree.sound w61 pick61 4 t565 _ (by decide +kernel)
theorem cov61_5 : PA.Covered 5 (OZ.Valid 5 w61.low w61.t w61.y w61.r w61.cap) (P33.root 5) :=
  Night6836Tree.sound w61 pick61 5 t566 _ (by decide +kernel)
theorem cov61_6 : PA.Covered 6 (OZ.Valid 6 w61.low w61.t w61.y w61.r w61.cap) (P33.root 6) :=
  Night6836Tree.sound w61 pick61 6 t567 _ (by decide +kernel)
theorem cov61_7 : PA.Covered 7 (OZ.Valid 7 w61.low w61.t w61.y w61.r w61.cap) (P33.root 7) :=
  Night6836Tree.sound w61 pick61 7 t568 _ (by decide +kernel)
theorem window61 : P33.WindowCount w61 := by
  apply P33.window_count w61 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov61_1
  · exact cov61_2
  · exact cov61_3
  · exact cov61_4
  · exact cov61_5
  · exact cov61_6
  · exact cov61_7
def w62 : P33.Window := ⟨10,35,4634,3635,197738144615062164,44144,39000,5000000,81920000000⟩
def h62_0 : Height w62 := ⟨44144,39000,by decide +kernel⟩
def h62_1 : Height w62 := ⟨50320,35000,by decide +kernel⟩
def h62_2 : Height w62 := ⟨58409,31000,by decide +kernel⟩
def h62_3 : Height w62 := ⟨70111,27000,by decide +kernel⟩
def pick62 (cl : ℕ) : Height w62 := if cl<40 then (if cl<6 then (h62_0) else (h62_1)) else (if cl<264 then (h62_2) else (h62_3))
private theorem k62_1_0 : check w62 pick62 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k62_1_1 : check w62 pick62 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k62_1_2 : check w62 pick62 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w62 pick62 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k62_1_0 k62_1_1
private theorem k62_1_3 : check w62 pick62 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k62_1_4 : check w62 pick62 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k62_1_5 : check w62 pick62 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w62 pick62 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k62_1_3 k62_1_4
private theorem k62_1_6 : check w62 pick62 1 t2814 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w62 pick62 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2813 k62_1_2 k62_1_5
private theorem k62_1_7 : check w62 pick62 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k62_1_8 : check w62 pick62 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k62_1_9 : check w62 pick62 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w62 pick62 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k62_1_7 k62_1_8
private theorem k62_1_10 : check w62 pick62 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k62_1_11 : check w62 pick62 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k62_1_12 : check w62 pick62 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w62 pick62 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k62_1_10 k62_1_11
private theorem k62_1_13 : check w62 pick62 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w62 pick62 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k62_1_9 k62_1_12
private theorem k62_1_14 : check w62 pick62 1 t2815 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w62 pick62 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2814 t2461 k62_1_6 k62_1_13
theorem cov62_1 : PA.Covered 1 (OZ.Valid 1 w62.low w62.t w62.y w62.r w62.cap) (P33.root 1) :=
  Night6836Tree.sound w62 pick62 1 t2815 _ k62_1_14
theorem cov62_2 : PA.Covered 2 (OZ.Valid 2 w62.low w62.t w62.y w62.r w62.cap) (P33.root 2) :=
  Night6836Tree.sound w62 pick62 2 t2745 _ (by decide +kernel)
theorem cov62_3 : PA.Covered 3 (OZ.Valid 3 w62.low w62.t w62.y w62.r w62.cap) (P33.root 3) :=
  Night6836Tree.sound w62 pick62 3 t564 _ (by decide +kernel)
theorem cov62_4 : PA.Covered 4 (OZ.Valid 4 w62.low w62.t w62.y w62.r w62.cap) (P33.root 4) :=
  Night6836Tree.sound w62 pick62 4 t565 _ (by decide +kernel)
theorem cov62_5 : PA.Covered 5 (OZ.Valid 5 w62.low w62.t w62.y w62.r w62.cap) (P33.root 5) :=
  Night6836Tree.sound w62 pick62 5 t566 _ (by decide +kernel)
theorem cov62_6 : PA.Covered 6 (OZ.Valid 6 w62.low w62.t w62.y w62.r w62.cap) (P33.root 6) :=
  Night6836Tree.sound w62 pick62 6 t567 _ (by decide +kernel)
theorem cov62_7 : PA.Covered 7 (OZ.Valid 7 w62.low w62.t w62.y w62.r w62.cap) (P33.root 7) :=
  Night6836Tree.sound w62 pick62 7 t2134 _ (by decide +kernel)
theorem window62 : P33.WindowCount w62 := by
  apply P33.window_count w62 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov62_1
  · exact cov62_2
  · exact cov62_3
  · exact cov62_4
  · exact cov62_5
  · exact cov62_6
  · exact cov62_7
def w63 : P33.Window := ⟨10,35,5834,4835,203858752054438947,31006,31000,5000000,81920000000⟩
def h63_0 : Height w63 := ⟨31006,31000,by decide +kernel⟩
def h63_1 : Height w63 := ⟨36700,27000,by decide +kernel⟩
def h63_2 : Height w63 := ⟨44705,23000,by decide +kernel⟩
def h63_3 : Height w63 := ⟨58173,19000,by decide +kernel⟩
def pick63 (cl : ℕ) : Height w63 := if cl<40 then (if cl<4 then (h63_0) else (h63_1)) else (if cl<531 then (h63_2) else (h63_3))
private theorem k63_1_0 : check w63 pick63 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k63_1_1 : check w63 pick63 1 t3253 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k63_1_2 : check w63 pick63 1 t3254 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w63 pick63 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t3253 k63_1_0 k63_1_1
private theorem k63_1_3 : check w63 pick63 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k63_1_4 : check w63 pick63 1 t3195 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k63_1_5 : check w63 pick63 1 t3264 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w63 pick63 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t3195 k63_1_3 k63_1_4
private theorem k63_1_6 : check w63 pick63 1 t3265 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w63 pick63 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3254 t3264 k63_1_2 k63_1_5
private theorem k63_1_7 : check w63 pick63 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k63_1_8 : check w63 pick63 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k63_1_9 : check w63 pick63 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w63 pick63 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k63_1_7 k63_1_8
private theorem k63_1_10 : check w63 pick63 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k63_1_11 : check w63 pick63 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k63_1_12 : check w63 pick63 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w63 pick63 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k63_1_10 k63_1_11
private theorem k63_1_13 : check w63 pick63 1 t3201 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w63 pick63 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t1079 k63_1_9 k63_1_12
private theorem k63_1_14 : check w63 pick63 1 t3266 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w63 pick63 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3265 t3201 k63_1_6 k63_1_13
theorem cov63_1 : PA.Covered 1 (OZ.Valid 1 w63.low w63.t w63.y w63.r w63.cap) (P33.root 1) :=
  Night6836Tree.sound w63 pick63 1 t3266 _ k63_1_14
private theorem k63_2_0 : check w63 pick63 2 t3291 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k63_2_1 : check w63 pick63 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k63_2_2 : check w63 pick63 2 t3304 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w63 pick63 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t3291 t3303 k63_2_0 k63_2_1
theorem cov63_2 : PA.Covered 2 (OZ.Valid 2 w63.low w63.t w63.y w63.r w63.cap) (P33.root 2) :=
  Night6836Tree.sound w63 pick63 2 t3304 _ k63_2_2
theorem cov63_3 : PA.Covered 3 (OZ.Valid 3 w63.low w63.t w63.y w63.r w63.cap) (P33.root 3) :=
  Night6836Tree.sound w63 pick63 3 t564 _ (by decide +kernel)
theorem cov63_4 : PA.Covered 4 (OZ.Valid 4 w63.low w63.t w63.y w63.r w63.cap) (P33.root 4) :=
  Night6836Tree.sound w63 pick63 4 t565 _ (by decide +kernel)
theorem cov63_5 : PA.Covered 5 (OZ.Valid 5 w63.low w63.t w63.y w63.r w63.cap) (P33.root 5) :=
  Night6836Tree.sound w63 pick63 5 t566 _ (by decide +kernel)
theorem cov63_6 : PA.Covered 6 (OZ.Valid 6 w63.low w63.t w63.y w63.r w63.cap) (P33.root 6) :=
  Night6836Tree.sound w63 pick63 6 t567 _ (by decide +kernel)
theorem cov63_7 : PA.Covered 7 (OZ.Valid 7 w63.low w63.t w63.y w63.r w63.cap) (P33.root 7) :=
  Night6836Tree.sound w63 pick63 7 t2134 _ (by decide +kernel)
theorem window63 : P33.WindowCount w63 := by
  apply P33.window_count w63 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov63_1
  · exact cov63_2
  · exact cov63_3
  · exact cov63_4
  · exact cov63_5
  · exact cov63_6
  · exact cov63_7
def w64 : P33.Window := ⟨10,35,7238,7194,245621871001650061,20645,21000,5000000,81920000000⟩
def h64_0 : Height w64 := ⟨20645,21000,by decide +kernel⟩
def h64_1 : Height w64 := ⟨24927,18000,by decide +kernel⟩
def h64_2 : Height w64 := ⟨31270,15000,by decide +kernel⟩
def h64_3 : Height w64 := ⟨43292,12000,by decide +kernel⟩
def pick64 (cl : ℕ) : Height w64 := if cl<49 then (if cl<4 then (h64_0) else (h64_1)) else (if cl<922 then (h64_2) else (h64_3))
private theorem k64_1_0 : check w64 pick64 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k64_1_1 : check w64 pick64 1 t3253 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k64_1_2 : check w64 pick64 1 t3254 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w64 pick64 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t3253 k64_1_0 k64_1_1
private theorem k64_1_3 : check w64 pick64 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k64_1_4 : check w64 pick64 1 t3195 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k64_1_5 : check w64 pick64 1 t3264 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w64 pick64 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t3195 k64_1_3 k64_1_4
private theorem k64_1_6 : check w64 pick64 1 t3265 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w64 pick64 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3254 t3264 k64_1_2 k64_1_5
private theorem k64_1_7 : check w64 pick64 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k64_1_8 : check w64 pick64 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k64_1_9 : check w64 pick64 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w64 pick64 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k64_1_7 k64_1_8
private theorem k64_1_10 : check w64 pick64 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k64_1_11 : check w64 pick64 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k64_1_12 : check w64 pick64 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w64 pick64 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k64_1_10 k64_1_11
private theorem k64_1_13 : check w64 pick64 1 t3201 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w64 pick64 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t1079 k64_1_9 k64_1_12
private theorem k64_1_14 : check w64 pick64 1 t3266 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w64 pick64 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3265 t3201 k64_1_6 k64_1_13
theorem cov64_1 : PA.Covered 1 (OZ.Valid 1 w64.low w64.t w64.y w64.r w64.cap) (P33.root 1) :=
  Night6836Tree.sound w64 pick64 1 t3266 _ k64_1_14
private theorem k64_2_0 : check w64 pick64 2 t3321 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k64_2_1 : check w64 pick64 2 t3323 ⟨2,7,4,16,2,52,85,166⟩ = true := by decide +kernel
private theorem k64_2_2 : check w64 pick64 2 t3324 ⟨2,7,4,16,2,52,2,166⟩ = true := glue w64 pick64 2 ⟨2,7,4,16,2,52,2,166⟩ 3 84 t3321 t3323 k64_2_0 k64_2_1
private theorem k64_2_3 : check w64 pick64 2 t3356 ⟨2,7,4,16,2,52,167,450⟩ = true := by decide +kernel
private theorem k64_2_4 : check w64 pick64 2 t3357 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w64 pick64 2 ⟨2,7,4,16,0,52,0,450⟩ 3 166 t3324 t3356 k64_2_2 k64_2_3
theorem cov64_2 : PA.Covered 2 (OZ.Valid 2 w64.low w64.t w64.y w64.r w64.cap) (P33.root 2) :=
  Night6836Tree.sound w64 pick64 2 t3357 _ k64_2_4
theorem cov64_3 : PA.Covered 3 (OZ.Valid 3 w64.low w64.t w64.y w64.r w64.cap) (P33.root 3) :=
  Night6836Tree.sound w64 pick64 3 t564 _ (by decide +kernel)
theorem cov64_4 : PA.Covered 4 (OZ.Valid 4 w64.low w64.t w64.y w64.r w64.cap) (P33.root 4) :=
  Night6836Tree.sound w64 pick64 4 t565 _ (by decide +kernel)
theorem cov64_5 : PA.Covered 5 (OZ.Valid 5 w64.low w64.t w64.y w64.r w64.cap) (P33.root 5) :=
  Night6836Tree.sound w64 pick64 5 t566 _ (by decide +kernel)
theorem cov64_6 : PA.Covered 6 (OZ.Valid 6 w64.low w64.t w64.y w64.r w64.cap) (P33.root 6) :=
  Night6836Tree.sound w64 pick64 6 t567 _ (by decide +kernel)
theorem cov64_7 : PA.Covered 7 (OZ.Valid 7 w64.low w64.t w64.y w64.r w64.cap) (P33.root 7) :=
  Night6836Tree.sound w64 pick64 7 t568 _ (by decide +kernel)
theorem window64 : P33.WindowCount w64 := by
  apply P33.window_count w64 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov64_1
  · exact cov64_2
  · exact cov64_3
  · exact cov64_4
  · exact cov64_5
  · exact cov64_6
  · exact cov64_7
def w65 : P33.Window := ⟨10,36,4635,3636,201229765474532011,46231,39000,5000000,81920000000⟩
def h65_0 : Height w65 := ⟨46231,39000,by decide +kernel⟩
def h65_1 : Height w65 := ⟨52539,35000,by decide +kernel⟩
def h65_2 : Height w65 := ⟨60821,31000,by decide +kernel⟩
def h65_3 : Height w65 := ⟨72826,27000,by decide +kernel⟩
def pick65 (cl : ℕ) : Height w65 := if cl<44 then (if cl<10 then (h65_0) else (h65_1)) else (if cl<281 then (h65_2) else (h65_3))
private theorem k65_1_0 : check w65 pick65 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k65_1_1 : check w65 pick65 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k65_1_2 : check w65 pick65 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w65 pick65 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k65_1_0 k65_1_1
private theorem k65_1_3 : check w65 pick65 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k65_1_4 : check w65 pick65 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k65_1_5 : check w65 pick65 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w65 pick65 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k65_1_3 k65_1_4
private theorem k65_1_6 : check w65 pick65 1 t2814 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w65 pick65 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t2813 k65_1_2 k65_1_5
private theorem k65_1_7 : check w65 pick65 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k65_1_8 : check w65 pick65 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k65_1_9 : check w65 pick65 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w65 pick65 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k65_1_7 k65_1_8
private theorem k65_1_10 : check w65 pick65 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k65_1_11 : check w65 pick65 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k65_1_12 : check w65 pick65 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w65 pick65 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k65_1_10 k65_1_11
private theorem k65_1_13 : check w65 pick65 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w65 pick65 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k65_1_9 k65_1_12
private theorem k65_1_14 : check w65 pick65 1 t2815 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w65 pick65 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2814 t2461 k65_1_6 k65_1_13
theorem cov65_1 : PA.Covered 1 (OZ.Valid 1 w65.low w65.t w65.y w65.r w65.cap) (P33.root 1) :=
  Night6836Tree.sound w65 pick65 1 t2815 _ k65_1_14
theorem cov65_2 : PA.Covered 2 (OZ.Valid 2 w65.low w65.t w65.y w65.r w65.cap) (P33.root 2) :=
  Night6836Tree.sound w65 pick65 2 t2745 _ (by decide +kernel)
theorem cov65_3 : PA.Covered 3 (OZ.Valid 3 w65.low w65.t w65.y w65.r w65.cap) (P33.root 3) :=
  Night6836Tree.sound w65 pick65 3 t564 _ (by decide +kernel)
theorem cov65_4 : PA.Covered 4 (OZ.Valid 4 w65.low w65.t w65.y w65.r w65.cap) (P33.root 4) :=
  Night6836Tree.sound w65 pick65 4 t565 _ (by decide +kernel)
theorem cov65_5 : PA.Covered 5 (OZ.Valid 5 w65.low w65.t w65.y w65.r w65.cap) (P33.root 5) :=
  Night6836Tree.sound w65 pick65 5 t566 _ (by decide +kernel)
theorem cov65_6 : PA.Covered 6 (OZ.Valid 6 w65.low w65.t w65.y w65.r w65.cap) (P33.root 6) :=
  Night6836Tree.sound w65 pick65 6 t567 _ (by decide +kernel)
theorem cov65_7 : PA.Covered 7 (OZ.Valid 7 w65.low w65.t w65.y w65.r w65.cap) (P33.root 7) :=
  Night6836Tree.sound w65 pick65 7 t2134 _ (by decide +kernel)
theorem window65 : P33.WindowCount w65 := by
  apply P33.window_count w65 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov65_1
  · exact cov65_2
  · exact cov65_3
  · exact cov65_4
  · exact cov65_5
  · exact cov65_6
  · exact cov65_7
def w66 : P33.Window := ⟨10,36,7193,7148,245789768717442864,21992,21000,5000000,81920000000⟩
def h66_0 : Height w66 := ⟨21992,21000,by decide +kernel⟩
def h66_1 : Height w66 := ⟨26424,18000,by decide +kernel⟩
def h66_2 : Height w66 := ⟨33038,15000,by decide +kernel⟩
def h66_3 : Height w66 := ⟨45699,12000,by decide +kernel⟩
def pick66 (cl : ℕ) : Height w66 := if cl<64 then (if cl<5 then (h66_0) else (h66_1)) else (if cl<961 then (h66_2) else (h66_3))
private theorem k66_1_0 : check w66 pick66 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k66_1_1 : check w66 pick66 1 t3253 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k66_1_2 : check w66 pick66 1 t3254 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w66 pick66 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t3253 k66_1_0 k66_1_1
private theorem k66_1_3 : check w66 pick66 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k66_1_4 : check w66 pick66 1 t3195 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k66_1_5 : check w66 pick66 1 t3264 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w66 pick66 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t3195 k66_1_3 k66_1_4
private theorem k66_1_6 : check w66 pick66 1 t3265 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w66 pick66 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3254 t3264 k66_1_2 k66_1_5
private theorem k66_1_7 : check w66 pick66 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k66_1_8 : check w66 pick66 1 t3371 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k66_1_9 : check w66 pick66 1 t3372 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w66 pick66 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t3199 t3371 k66_1_7 k66_1_8
private theorem k66_1_10 : check w66 pick66 1 t3382 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k66_1_11 : check w66 pick66 1 t3405 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k66_1_12 : check w66 pick66 1 t3406 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w66 pick66 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t3382 t3405 k66_1_10 k66_1_11
private theorem k66_1_13 : check w66 pick66 1 t3407 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w66 pick66 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t3372 t3406 k66_1_9 k66_1_12
private theorem k66_1_14 : check w66 pick66 1 t3408 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w66 pick66 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3265 t3407 k66_1_6 k66_1_13
theorem cov66_1 : PA.Covered 1 (OZ.Valid 1 w66.low w66.t w66.y w66.r w66.cap) (P33.root 1) :=
  Night6836Tree.sound w66 pick66 1 t3408 _ k66_1_14
private theorem k66_2_0 : check w66 pick66 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k66_2_1 : check w66 pick66 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k66_2_2 : check w66 pick66 2 t3491 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w66 pick66 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3490 k66_2_0 k66_2_1
private theorem k66_2_3 : check w66 pick66 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k66_2_4 : check w66 pick66 2 t3530 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k66_2_5 : check w66 pick66 2 t3531 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w66 pick66 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t3530 k66_2_3 k66_2_4
private theorem k66_2_6 : check w66 pick66 2 t3532 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w66 pick66 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3491 t3531 k66_2_2 k66_2_5
theorem cov66_2 : PA.Covered 2 (OZ.Valid 2 w66.low w66.t w66.y w66.r w66.cap) (P33.root 2) :=
  Night6836Tree.sound w66 pick66 2 t3532 _ k66_2_6
theorem cov66_3 : PA.Covered 3 (OZ.Valid 3 w66.low w66.t w66.y w66.r w66.cap) (P33.root 3) :=
  Night6836Tree.sound w66 pick66 3 t564 _ (by decide +kernel)
theorem cov66_4 : PA.Covered 4 (OZ.Valid 4 w66.low w66.t w66.y w66.r w66.cap) (P33.root 4) :=
  Night6836Tree.sound w66 pick66 4 t565 _ (by decide +kernel)
theorem cov66_5 : PA.Covered 5 (OZ.Valid 5 w66.low w66.t w66.y w66.r w66.cap) (P33.root 5) :=
  Night6836Tree.sound w66 pick66 5 t566 _ (by decide +kernel)
theorem cov66_6 : PA.Covered 6 (OZ.Valid 6 w66.low w66.t w66.y w66.r w66.cap) (P33.root 6) :=
  Night6836Tree.sound w66 pick66 6 t567 _ (by decide +kernel)
theorem cov66_7 : PA.Covered 7 (OZ.Valid 7 w66.low w66.t w66.y w66.r w66.cap) (P33.root 7) :=
  Night6836Tree.sound w66 pick66 7 t568 _ (by decide +kernel)
theorem window66 : P33.WindowCount w66 := by
  apply P33.window_count w66 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov66_1
  · exact cov66_2
  · exact cov66_3
  · exact cov66_4
  · exact cov66_5
  · exact cov66_6
  · exact cov66_7
def w67 : P33.Window := ⟨10,37,4636,3637,203648407253629935,43081,43000,5000000,81920000000⟩
def h67_0 : Height w67 := ⟨43081,43000,by decide +kernel⟩
def h67_1 : Height w67 := ⟨48316,39000,by decide +kernel⟩
def h67_2 : Height w67 := ⟨54756,35000,by decide +kernel⟩
def h67_3 : Height w67 := ⟨63230,31000,by decide +kernel⟩
def h67_4 : Height w67 := ⟨75537,27000,by decide +kernel⟩
def pick67 (cl : ℕ) : Height w67 := if cl<10 then (if cl<2 then (h67_0) else (h67_1)) else (if cl<49 then (h67_2) else (if cl<302 then (h67_3) else (h67_4)))
private theorem k67_1_0 : check w67 pick67 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k67_1_1 : check w67 pick67 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k67_1_2 : check w67 pick67 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w67 pick67 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k67_1_0 k67_1_1
private theorem k67_1_3 : check w67 pick67 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k67_1_4 : check w67 pick67 1 t3538 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k67_1_5 : check w67 pick67 1 t3539 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w67 pick67 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t3538 k67_1_3 k67_1_4
private theorem k67_1_6 : check w67 pick67 1 t3540 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w67 pick67 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t3539 k67_1_2 k67_1_5
private theorem k67_1_7 : check w67 pick67 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k67_1_8 : check w67 pick67 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k67_1_9 : check w67 pick67 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w67 pick67 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k67_1_7 k67_1_8
private theorem k67_1_10 : check w67 pick67 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k67_1_11 : check w67 pick67 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k67_1_12 : check w67 pick67 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w67 pick67 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k67_1_10 k67_1_11
private theorem k67_1_13 : check w67 pick67 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w67 pick67 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k67_1_9 k67_1_12
private theorem k67_1_14 : check w67 pick67 1 t3550 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w67 pick67 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3540 t3549 k67_1_6 k67_1_13
theorem cov67_1 : PA.Covered 1 (OZ.Valid 1 w67.low w67.t w67.y w67.r w67.cap) (P33.root 1) :=
  Night6836Tree.sound w67 pick67 1 t3550 _ k67_1_14
theorem cov67_2 : PA.Covered 2 (OZ.Valid 2 w67.low w67.t w67.y w67.r w67.cap) (P33.root 2) :=
  Night6836Tree.sound w67 pick67 2 t2745 _ (by decide +kernel)
theorem cov67_3 : PA.Covered 3 (OZ.Valid 3 w67.low w67.t w67.y w67.r w67.cap) (P33.root 3) :=
  Night6836Tree.sound w67 pick67 3 t564 _ (by decide +kernel)
theorem cov67_4 : PA.Covered 4 (OZ.Valid 4 w67.low w67.t w67.y w67.r w67.cap) (P33.root 4) :=
  Night6836Tree.sound w67 pick67 4 t565 _ (by decide +kernel)
theorem cov67_5 : PA.Covered 5 (OZ.Valid 5 w67.low w67.t w67.y w67.r w67.cap) (P33.root 5) :=
  Night6836Tree.sound w67 pick67 5 t566 _ (by decide +kernel)
theorem cov67_6 : PA.Covered 6 (OZ.Valid 6 w67.low w67.t w67.y w67.r w67.cap) (P33.root 6) :=
  Night6836Tree.sound w67 pick67 6 t567 _ (by decide +kernel)
theorem cov67_7 : PA.Covered 7 (OZ.Valid 7 w67.low w67.t w67.y w67.r w67.cap) (P33.root 7) :=
  Night6836Tree.sound w67 pick67 7 t2134 _ (by decide +kernel)
theorem window67 : P33.WindowCount w67 := by
  apply P33.window_count w67 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov67_1
  · exact cov67_2
  · exact cov67_3
  · exact cov67_4
  · exact cov67_5
  · exact cov67_6
  · exact cov67_7
def w68 : P33.Window := ⟨10,37,7147,6298,245469400137523389,25930,24000,5000000,81920000000⟩
def h68_0 : Height w68 := ⟨25930,24000,by decide +kernel⟩
def h68_1 : Height w68 := ⟨30292,21000,by decide +kernel⟩
def h68_2 : Height w68 := ⟨36348,18000,by decide +kernel⟩
def h68_3 : Height w68 := ⟨46230,15000,by decide +kernel⟩
def pick68 (cl : ℕ) : Height w68 := if cl<40 then (if cl<5 then (h68_0) else (h68_1)) else (if cl<431 then (h68_2) else (h68_3))
private theorem k68_1_0 : check w68 pick68 1 t3562 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k68_1_1 : check w68 pick68 1 t3253 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k68_1_2 : check w68 pick68 1 t3563 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w68 pick68 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3562 t3253 k68_1_0 k68_1_1
private theorem k68_1_3 : check w68 pick68 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k68_1_4 : check w68 pick68 1 t3571 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k68_1_5 : check w68 pick68 1 t3572 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w68 pick68 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t3571 k68_1_3 k68_1_4
private theorem k68_1_6 : check w68 pick68 1 t3573 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w68 pick68 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3563 t3572 k68_1_2 k68_1_5
private theorem k68_1_7 : check w68 pick68 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k68_1_8 : check w68 pick68 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k68_1_9 : check w68 pick68 1 t3616 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w68 pick68 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t3615 k68_1_7 k68_1_8
private theorem k68_1_10 : check w68 pick68 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k68_1_11 : check w68 pick68 1 t3405 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k68_1_12 : check w68 pick68 1 t3656 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w68 pick68 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t3405 k68_1_10 k68_1_11
private theorem k68_1_13 : check w68 pick68 1 t3657 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w68 pick68 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3616 t3656 k68_1_9 k68_1_12
private theorem k68_1_14 : check w68 pick68 1 t3658 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w68 pick68 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3573 t3657 k68_1_6 k68_1_13
theorem cov68_1 : PA.Covered 1 (OZ.Valid 1 w68.low w68.t w68.y w68.r w68.cap) (P33.root 1) :=
  Night6836Tree.sound w68 pick68 1 t3658 _ k68_1_14
private theorem k68_2_0 : check w68 pick68 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k68_2_1 : check w68 pick68 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k68_2_2 : check w68 pick68 2 t3491 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w68 pick68 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3490 k68_2_0 k68_2_1
private theorem k68_2_3 : check w68 pick68 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k68_2_4 : check w68 pick68 2 t3530 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k68_2_5 : check w68 pick68 2 t3531 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w68 pick68 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t3530 k68_2_3 k68_2_4
private theorem k68_2_6 : check w68 pick68 2 t3532 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w68 pick68 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3491 t3531 k68_2_2 k68_2_5
theorem cov68_2 : PA.Covered 2 (OZ.Valid 2 w68.low w68.t w68.y w68.r w68.cap) (P33.root 2) :=
  Night6836Tree.sound w68 pick68 2 t3532 _ k68_2_6
theorem cov68_3 : PA.Covered 3 (OZ.Valid 3 w68.low w68.t w68.y w68.r w68.cap) (P33.root 3) :=
  Night6836Tree.sound w68 pick68 3 t564 _ (by decide +kernel)
theorem cov68_4 : PA.Covered 4 (OZ.Valid 4 w68.low w68.t w68.y w68.r w68.cap) (P33.root 4) :=
  Night6836Tree.sound w68 pick68 4 t565 _ (by decide +kernel)
theorem cov68_5 : PA.Covered 5 (OZ.Valid 5 w68.low w68.t w68.y w68.r w68.cap) (P33.root 5) :=
  Night6836Tree.sound w68 pick68 5 t566 _ (by decide +kernel)
theorem cov68_6 : PA.Covered 6 (OZ.Valid 6 w68.low w68.t w68.y w68.r w68.cap) (P33.root 6) :=
  Night6836Tree.sound w68 pick68 6 t567 _ (by decide +kernel)
theorem cov68_7 : PA.Covered 7 (OZ.Valid 7 w68.low w68.t w68.y w68.r w68.cap) (P33.root 7) :=
  Night6836Tree.sound w68 pick68 7 t568 _ (by decide +kernel)
theorem window68 : P33.WindowCount w68 := by
  apply P33.window_count w68 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov68_1
  · exact cov68_2
  · exact cov68_3
  · exact cov68_4
  · exact cov68_5
  · exact cov68_6
  · exact cov68_7
def w69 : P33.Window := ⟨10,38,5437,4438,203656351141569620,37262,35000,5000000,81920000000⟩
def h69_0 : Height w69 := ⟨37262,35000,by decide +kernel⟩
def h69_1 : Height w69 := ⟨42801,31000,by decide +kernel⟩
def h69_2 : Height w69 := ⟨50122,27000,by decide +kernel⟩
def h69_3 : Height w69 := ⟨61020,23000,by decide +kernel⟩
def h69_4 : Height w69 := ⟨80889,19000,by decide +kernel⟩
def pick69 (cl : ℕ) : Height w69 := if cl<32 then (if cl<4 then (h69_0) else (h69_1)) else (if cl<203 then (h69_2) else (if cl<1002 then (h69_3) else (h69_4)))
private theorem k69_1_0 : check w69 pick69 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k69_1_1 : check w69 pick69 1 t3668 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k69_1_2 : check w69 pick69 1 t3669 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w69 pick69 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t3666 t3668 k69_1_0 k69_1_1
private theorem k69_1_3 : check w69 pick69 1 t3682 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k69_1_4 : check w69 pick69 1 t3704 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k69_1_5 : check w69 pick69 1 t3705 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w69 pick69 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t3682 t3704 k69_1_3 k69_1_4
private theorem k69_1_6 : check w69 pick69 1 t3706 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w69 pick69 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t3669 t3705 k69_1_2 k69_1_5
private theorem k69_1_7 : check w69 pick69 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k69_1_8 : check w69 pick69 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k69_1_9 : check w69 pick69 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w69 pick69 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k69_1_7 k69_1_8
private theorem k69_1_10 : check w69 pick69 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k69_1_11 : check w69 pick69 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k69_1_12 : check w69 pick69 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w69 pick69 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k69_1_10 k69_1_11
private theorem k69_1_13 : check w69 pick69 1 t3710 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w69 pick69 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t3709 k69_1_9 k69_1_12
private theorem k69_1_14 : check w69 pick69 1 t3711 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w69 pick69 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3706 t3710 k69_1_6 k69_1_13
theorem cov69_1 : PA.Covered 1 (OZ.Valid 1 w69.low w69.t w69.y w69.r w69.cap) (P33.root 1) :=
  Night6836Tree.sound w69 pick69 1 t3711 _ k69_1_14
private theorem k69_2_0 : check w69 pick69 2 t3291 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k69_2_1 : check w69 pick69 2 t3714 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k69_2_2 : check w69 pick69 2 t3715 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w69 pick69 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t3291 t3714 k69_2_0 k69_2_1
theorem cov69_2 : PA.Covered 2 (OZ.Valid 2 w69.low w69.t w69.y w69.r w69.cap) (P33.root 2) :=
  Night6836Tree.sound w69 pick69 2 t3715 _ k69_2_2
theorem cov69_3 : PA.Covered 3 (OZ.Valid 3 w69.low w69.t w69.y w69.r w69.cap) (P33.root 3) :=
  Night6836Tree.sound w69 pick69 3 t564 _ (by decide +kernel)
theorem cov69_4 : PA.Covered 4 (OZ.Valid 4 w69.low w69.t w69.y w69.r w69.cap) (P33.root 4) :=
  Night6836Tree.sound w69 pick69 4 t565 _ (by decide +kernel)
theorem cov69_5 : PA.Covered 5 (OZ.Valid 5 w69.low w69.t w69.y w69.r w69.cap) (P33.root 5) :=
  Night6836Tree.sound w69 pick69 5 t566 _ (by decide +kernel)
theorem cov69_6 : PA.Covered 6 (OZ.Valid 6 w69.low w69.t w69.y w69.r w69.cap) (P33.root 6) :=
  Night6836Tree.sound w69 pick69 6 t567 _ (by decide +kernel)
theorem cov69_7 : PA.Covered 7 (OZ.Valid 7 w69.low w69.t w69.y w69.r w69.cap) (P33.root 7) :=
  Night6836Tree.sound w69 pick69 7 t2134 _ (by decide +kernel)
theorem window69 : P33.WindowCount w69 := by
  apply P33.window_count w69 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov69_1
  · exact cov69_2
  · exact cov69_3
  · exact cov69_4
  · exact cov69_5
  · exact cov69_6
  · exact cov69_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w70 : P33.Window := ⟨10,38,7100,7054,246373170049359754,24778,21000,5000000,81920000000⟩
def h70_0 : Height w70 := ⟨24778,21000,by decide +kernel⟩
def h70_1 : Height w70 := ⟨29530,18000,by decide +kernel⟩
def h70_2 : Height w70 := ⟨36727,15000,by decide +kernel⟩
def h70_3 : Height w70 := ⟨50775,12000,by decide +kernel⟩
def pick70 (cl : ℕ) : Height w70 := if cl<105 then (if cl<10 then (h70_0) else (h70_1)) else (if cl<981 then (h70_2) else (h70_3))
private theorem k70_1_0 : check w70 pick70 1 t3716 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k70_1_1 : check w70 pick70 1 t3725 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k70_1_2 : check w70 pick70 1 t3726 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w70 pick70 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t3716 t3725 k70_1_0 k70_1_1
private theorem k70_1_3 : check w70 pick70 1 t3747 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k70_1_4 : check w70 pick70 1 t3766 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k70_1_5 : check w70 pick70 1 t3767 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w70 pick70 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t3747 t3766 k70_1_3 k70_1_4
private theorem k70_1_6 : check w70 pick70 1 t3768 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w70 pick70 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t3726 t3767 k70_1_2 k70_1_5
private theorem k70_1_7 : check w70 pick70 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k70_1_8 : check w70 pick70 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k70_1_9 : check w70 pick70 1 t3616 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w70 pick70 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t3615 k70_1_7 k70_1_8
private theorem k70_1_10 : check w70 pick70 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k70_1_11 : check w70 pick70 1 t3405 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k70_1_12 : check w70 pick70 1 t3656 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w70 pick70 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t3405 k70_1_10 k70_1_11
private theorem k70_1_13 : check w70 pick70 1 t3657 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w70 pick70 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3616 t3656 k70_1_9 k70_1_12
private theorem k70_1_14 : check w70 pick70 1 t3769 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w70 pick70 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3768 t3657 k70_1_6 k70_1_13
theorem cov70_1 : PA.Covered 1 (OZ.Valid 1 w70.low w70.t w70.y w70.r w70.cap) (P33.root 1) :=
  Night6836Tree.sound w70 pick70 1 t3769 _ k70_1_14
private theorem k70_2_0 : check w70 pick70 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k70_2_1 : check w70 pick70 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k70_2_2 : check w70 pick70 2 t3778 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w70 pick70 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3777 k70_2_0 k70_2_1
private theorem k70_2_3 : check w70 pick70 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k70_2_4 : check w70 pick70 2 t3530 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k70_2_5 : check w70 pick70 2 t3531 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w70 pick70 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t3530 k70_2_3 k70_2_4
private theorem k70_2_6 : check w70 pick70 2 t3779 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w70 pick70 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3778 t3531 k70_2_2 k70_2_5
theorem cov70_2 : PA.Covered 2 (OZ.Valid 2 w70.low w70.t w70.y w70.r w70.cap) (P33.root 2) :=
  Night6836Tree.sound w70 pick70 2 t3779 _ k70_2_6
theorem cov70_3 : PA.Covered 3 (OZ.Valid 3 w70.low w70.t w70.y w70.r w70.cap) (P33.root 3) :=
  Night6836Tree.sound w70 pick70 3 t564 _ (by decide +kernel)
theorem cov70_4 : PA.Covered 4 (OZ.Valid 4 w70.low w70.t w70.y w70.r w70.cap) (P33.root 4) :=
  Night6836Tree.sound w70 pick70 4 t565 _ (by decide +kernel)
theorem cov70_5 : PA.Covered 5 (OZ.Valid 5 w70.low w70.t w70.y w70.r w70.cap) (P33.root 5) :=
  Night6836Tree.sound w70 pick70 5 t566 _ (by decide +kernel)
theorem cov70_6 : PA.Covered 6 (OZ.Valid 6 w70.low w70.t w70.y w70.r w70.cap) (P33.root 6) :=
  Night6836Tree.sound w70 pick70 6 t567 _ (by decide +kernel)
theorem cov70_7 : PA.Covered 7 (OZ.Valid 7 w70.low w70.t w70.y w70.r w70.cap) (P33.root 7) :=
  Night6836Tree.sound w70 pick70 7 t568 _ (by decide +kernel)
theorem window70 : P33.WindowCount w70 := by
  apply P33.window_count w70 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov70_1
  · exact cov70_2
  · exact cov70_3
  · exact cov70_4
  · exact cov70_5
  · exact cov70_6
  · exact cov70_7
def w71 : P33.Window := ⟨10,39,5438,4439,203819765871467876,38899,35000,5000000,81920000000⟩
def h71_0 : Height w71 := ⟨38899,35000,by decide +kernel⟩
def h71_1 : Height w71 := ⟨44541,31000,by decide +kernel⟩
def h71_2 : Height w71 := ⟨52016,27000,by decide +kernel⟩
def h71_3 : Height w71 := ⟨63170,23000,by decide +kernel⟩
def h71_4 : Height w71 := ⟨83541,19000,by decide +kernel⟩
def pick71 (cl : ℕ) : Height w71 := if cl<27 then (if cl<4 then (h71_0) else (h71_1)) else (if cl<223 then (h71_2) else (if cl<1008 then (h71_3) else (h71_4)))
private theorem k71_1_0 : check w71 pick71 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k71_1_1 : check w71 pick71 1 t3795 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k71_1_2 : check w71 pick71 1 t3796 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w71 pick71 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t3666 t3795 k71_1_0 k71_1_1
private theorem k71_1_3 : check w71 pick71 1 t3808 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k71_1_4 : check w71 pick71 1 t3828 ⟨1,7,2,16,1,52,111,131⟩ = true := by decide +kernel
private theorem k71_1_5 : check w71 pick71 1 t3829 ⟨1,7,2,16,1,52,84,131⟩ = true := glue w71 pick71 1 ⟨1,7,2,16,1,52,84,131⟩ 3 110 t3808 t3828 k71_1_3 k71_1_4
private theorem k71_1_6 : check w71 pick71 1 t3830 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w71 pick71 1 ⟨1,7,2,16,1,52,1,131⟩ 3 83 t3796 t3829 k71_1_2 k71_1_5
private theorem k71_1_7 : check w71 pick71 1 t3836 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k71_1_8 : check w71 pick71 1 t3840 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k71_1_9 : check w71 pick71 1 t3841 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w71 pick71 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t3836 t3840 k71_1_7 k71_1_8
private theorem k71_1_10 : check w71 pick71 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k71_1_11 : check w71 pick71 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k71_1_12 : check w71 pick71 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w71 pick71 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k71_1_10 k71_1_11
private theorem k71_1_13 : check w71 pick71 1 t3842 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w71 pick71 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t3841 t3709 k71_1_9 k71_1_12
private theorem k71_1_14 : check w71 pick71 1 t3843 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w71 pick71 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t3830 t3842 k71_1_6 k71_1_13
theorem cov71_1 : PA.Covered 1 (OZ.Valid 1 w71.low w71.t w71.y w71.r w71.cap) (P33.root 1) :=
  Night6836Tree.sound w71 pick71 1 t3843 _ k71_1_14
private theorem k71_2_0 : check w71 pick71 2 t3845 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k71_2_1 : check w71 pick71 2 t3847 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k71_2_2 : check w71 pick71 2 t3848 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w71 pick71 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t3845 t3847 k71_2_0 k71_2_1
private theorem k71_2_3 : check w71 pick71 2 t3858 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k71_2_4 : check w71 pick71 2 t3859 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w71 pick71 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3848 t3858 k71_2_2 k71_2_3
theorem cov71_2 : PA.Covered 2 (OZ.Valid 2 w71.low w71.t w71.y w71.r w71.cap) (P33.root 2) :=
  Night6836Tree.sound w71 pick71 2 t3859 _ k71_2_4
theorem cov71_3 : PA.Covered 3 (OZ.Valid 3 w71.low w71.t w71.y w71.r w71.cap) (P33.root 3) :=
  Night6836Tree.sound w71 pick71 3 t564 _ (by decide +kernel)
theorem cov71_4 : PA.Covered 4 (OZ.Valid 4 w71.low w71.t w71.y w71.r w71.cap) (P33.root 4) :=
  Night6836Tree.sound w71 pick71 4 t565 _ (by decide +kernel)
theorem cov71_5 : PA.Covered 5 (OZ.Valid 5 w71.low w71.t w71.y w71.r w71.cap) (P33.root 5) :=
  Night6836Tree.sound w71 pick71 5 t566 _ (by decide +kernel)
theorem cov71_6 : PA.Covered 6 (OZ.Valid 6 w71.low w71.t w71.y w71.r w71.cap) (P33.root 6) :=
  Night6836Tree.sound w71 pick71 6 t567 _ (by decide +kernel)
theorem cov71_7 : PA.Covered 7 (OZ.Valid 7 w71.low w71.t w71.y w71.r w71.cap) (P33.root 7) :=
  Night6836Tree.sound w71 pick71 7 t2134 _ (by decide +kernel)
theorem window71 : P33.WindowCount w71 := by
  apply P33.window_count w71 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov71_1
  · exact cov71_2
  · exact cov71_3
  · exact cov71_4
  · exact cov71_5
  · exact cov71_6
  · exact cov71_7
def w72 : P33.Window := ⟨10,39,7053,6948,246363516488613969,26687,21000,5000000,81920000000⟩
def h72_0 : Height w72 := ⟨26687,21000,by decide +kernel⟩
def h72_1 : Height w72 := ⟨31699,18000,by decide +kernel⟩
def h72_2 : Height w72 := ⟨39388,15000,by decide +kernel⟩
def h72_3 : Height w72 := ⟨54675,12000,by decide +kernel⟩
def pick72 (cl : ℕ) : Height w72 := if cl<152 then (if cl<14 then (h72_0) else (h72_1)) else (if cl<1008 then (h72_2) else (h72_3))
private theorem k72_1_0 : check w72 pick72 1 t3870 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k72_1_1 : check w72 pick72 1 t3910 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k72_1_2 : check w72 pick72 1 t3911 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w72 pick72 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3870 t3910 k72_1_0 k72_1_1
private theorem k72_1_3 : check w72 pick72 1 t3944 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k72_1_4 : check w72 pick72 1 t3766 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k72_1_5 : check w72 pick72 1 t3945 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w72 pick72 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3944 t3766 k72_1_3 k72_1_4
private theorem k72_1_6 : check w72 pick72 1 t3946 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w72 pick72 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3911 t3945 k72_1_2 k72_1_5
private theorem k72_1_7 : check w72 pick72 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k72_1_8 : check w72 pick72 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k72_1_9 : check w72 pick72 1 t3616 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w72 pick72 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t3615 k72_1_7 k72_1_8
private theorem k72_1_10 : check w72 pick72 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k72_1_11 : check w72 pick72 1 t3949 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k72_1_12 : check w72 pick72 1 t3950 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w72 pick72 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t3949 k72_1_10 k72_1_11
private theorem k72_1_13 : check w72 pick72 1 t3951 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w72 pick72 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3616 t3950 k72_1_9 k72_1_12
private theorem k72_1_14 : check w72 pick72 1 t3952 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w72 pick72 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3946 t3951 k72_1_6 k72_1_13
theorem cov72_1 : PA.Covered 1 (OZ.Valid 1 w72.low w72.t w72.y w72.r w72.cap) (P33.root 1) :=
  Night6836Tree.sound w72 pick72 1 t3952 _ k72_1_14
private theorem k72_2_0 : check w72 pick72 2 t3985 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k72_2_1 : check w72 pick72 2 t4008 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k72_2_2 : check w72 pick72 2 t4009 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w72 pick72 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3985 t4008 k72_2_0 k72_2_1
private theorem k72_2_3 : check w72 pick72 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k72_2_4 : check w72 pick72 2 t3530 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k72_2_5 : check w72 pick72 2 t3531 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w72 pick72 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t3530 k72_2_3 k72_2_4
private theorem k72_2_6 : check w72 pick72 2 t4010 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w72 pick72 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4009 t3531 k72_2_2 k72_2_5
theorem cov72_2 : PA.Covered 2 (OZ.Valid 2 w72.low w72.t w72.y w72.r w72.cap) (P33.root 2) :=
  Night6836Tree.sound w72 pick72 2 t4010 _ k72_2_6
theorem cov72_3 : PA.Covered 3 (OZ.Valid 3 w72.low w72.t w72.y w72.r w72.cap) (P33.root 3) :=
  Night6836Tree.sound w72 pick72 3 t564 _ (by decide +kernel)
theorem cov72_4 : PA.Covered 4 (OZ.Valid 4 w72.low w72.t w72.y w72.r w72.cap) (P33.root 4) :=
  Night6836Tree.sound w72 pick72 4 t565 _ (by decide +kernel)
theorem cov72_5 : PA.Covered 5 (OZ.Valid 5 w72.low w72.t w72.y w72.r w72.cap) (P33.root 5) :=
  Night6836Tree.sound w72 pick72 5 t566 _ (by decide +kernel)
theorem cov72_6 : PA.Covered 6 (OZ.Valid 6 w72.low w72.t w72.y w72.r w72.cap) (P33.root 6) :=
  Night6836Tree.sound w72 pick72 6 t567 _ (by decide +kernel)
theorem cov72_7 : PA.Covered 7 (OZ.Valid 7 w72.low w72.t w72.y w72.r w72.cap) (P33.root 7) :=
  Night6836Tree.sound w72 pick72 7 t568 _ (by decide +kernel)
theorem window72 : P33.WindowCount w72 := by
  apply P33.window_count w72 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov72_1
  · exact cov72_2
  · exact cov72_3
  · exact cov72_4
  · exact cov72_5
  · exact cov72_6
  · exact cov72_7
def w73 : P33.Window := ⟨10,40,5839,4890,244113859091799667,35299,33000,5000000,81920000000⟩
def h73_0 : Height w73 := ⟨35299,33000,by decide +kernel⟩
def h73_1 : Height w73 := ⟨39213,30000,by decide +kernel⟩
def h73_2 : Height w73 := ⟨43984,27000,by decide +kernel⟩
def h73_3 : Height w73 := ⟨50166,24000,by decide +kernel⟩
def h73_4 : Height w73 := ⟨58919,21000,by decide +kernel⟩
def h73_5 : Height w73 := ⟨73148,18000,by decide +kernel⟩
def pick73 (cl : ℕ) : Height w73 := if cl<43 then (if cl<2 then (h73_0) else (if cl<10 then (h73_1) else (h73_2))) else (if cl<262 then (h73_3) else (if cl<1021 then (h73_4) else (h73_5)))
private theorem k73_1_0 : check w73 pick73 1 t2748 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k73_1_1 : check w73 pick73 1 t2764 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k73_1_2 : check w73 pick73 1 t2765 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w73 pick73 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t2748 t2764 k73_1_0 k73_1_1
private theorem k73_1_3 : check w73 pick73 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k73_1_4 : check w73 pick73 1 t2687 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k73_1_5 : check w73 pick73 1 t2813 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w73 pick73 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t2687 k73_1_3 k73_1_4
private theorem k73_1_6 : check w73 pick73 1 t2816 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w73 pick73 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2765 t2813 k73_1_2 k73_1_5
private theorem k73_1_7 : check w73 pick73 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k73_1_8 : check w73 pick73 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k73_1_9 : check w73 pick73 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w73 pick73 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k73_1_7 k73_1_8
private theorem k73_1_10 : check w73 pick73 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k73_1_11 : check w73 pick73 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k73_1_12 : check w73 pick73 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w73 pick73 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k73_1_10 k73_1_11
private theorem k73_1_13 : check w73 pick73 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w73 pick73 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k73_1_9 k73_1_12
private theorem k73_1_14 : check w73 pick73 1 t4011 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w73 pick73 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2816 t3549 k73_1_6 k73_1_13
theorem cov73_1 : PA.Covered 1 (OZ.Valid 1 w73.low w73.t w73.y w73.r w73.cap) (P33.root 1) :=
  Night6836Tree.sound w73 pick73 1 t4011 _ k73_1_14
private theorem k73_2_0 : check w73 pick73 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k73_2_1 : check w73 pick73 2 t4017 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k73_2_2 : check w73 pick73 2 t4018 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w73 pick73 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t4017 k73_2_0 k73_2_1
theorem cov73_2 : PA.Covered 2 (OZ.Valid 2 w73.low w73.t w73.y w73.r w73.cap) (P33.root 2) :=
  Night6836Tree.sound w73 pick73 2 t4018 _ k73_2_2
theorem cov73_3 : PA.Covered 3 (OZ.Valid 3 w73.low w73.t w73.y w73.r w73.cap) (P33.root 3) :=
  Night6836Tree.sound w73 pick73 3 t564 _ (by decide +kernel)
theorem cov73_4 : PA.Covered 4 (OZ.Valid 4 w73.low w73.t w73.y w73.r w73.cap) (P33.root 4) :=
  Night6836Tree.sound w73 pick73 4 t565 _ (by decide +kernel)
theorem cov73_5 : PA.Covered 5 (OZ.Valid 5 w73.low w73.t w73.y w73.r w73.cap) (P33.root 5) :=
  Night6836Tree.sound w73 pick73 5 t566 _ (by decide +kernel)
theorem cov73_6 : PA.Covered 6 (OZ.Valid 6 w73.low w73.t w73.y w73.r w73.cap) (P33.root 6) :=
  Night6836Tree.sound w73 pick73 6 t567 _ (by decide +kernel)
theorem cov73_7 : PA.Covered 7 (OZ.Valid 7 w73.low w73.t w73.y w73.r w73.cap) (P33.root 7) :=
  Night6836Tree.sound w73 pick73 7 t2134 _ (by decide +kernel)
theorem window73 : P33.WindowCount w73 := by
  apply P33.window_count w73 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov73_1
  · exact cov73_2
  · exact cov73_3
  · exact cov73_4
  · exact cov73_5
  · exact cov73_6
  · exact cov73_7
def w74 : P33.Window := ⟨10,40,7002,6948,246902424620869776,27779,21000,5000000,81920000000⟩
def h74_0 : Height w74 := ⟨27779,21000,by decide +kernel⟩
def h74_1 : Height w74 := ⟨32893,18000,by decide +kernel⟩
def h74_2 : Height w74 := ⟨40762,15000,by decide +kernel⟩
def h74_3 : Height w74 := ⟨56443,12000,by decide +kernel⟩
def pick74 (cl : ℕ) : Height w74 := if cl<170 then (if cl<18 then (h74_0) else (h74_1)) else (if cl<1017 then (h74_2) else (h74_3))
private theorem k74_1_0 : check w74 pick74 1 t3870 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k74_1_1 : check w74 pick74 1 t3910 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k74_1_2 : check w74 pick74 1 t3911 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w74 pick74 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3870 t3910 k74_1_0 k74_1_1
private theorem k74_1_3 : check w74 pick74 1 t3944 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k74_1_4 : check w74 pick74 1 t3766 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k74_1_5 : check w74 pick74 1 t3945 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w74 pick74 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3944 t3766 k74_1_3 k74_1_4
private theorem k74_1_6 : check w74 pick74 1 t3946 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w74 pick74 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3911 t3945 k74_1_2 k74_1_5
private theorem k74_1_7 : check w74 pick74 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k74_1_8 : check w74 pick74 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k74_1_9 : check w74 pick74 1 t3616 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w74 pick74 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t3615 k74_1_7 k74_1_8
private theorem k74_1_10 : check w74 pick74 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k74_1_11 : check w74 pick74 1 t4021 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k74_1_12 : check w74 pick74 1 t4022 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w74 pick74 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t4021 k74_1_10 k74_1_11
private theorem k74_1_13 : check w74 pick74 1 t4023 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w74 pick74 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3616 t4022 k74_1_9 k74_1_12
private theorem k74_1_14 : check w74 pick74 1 t4024 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w74 pick74 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3946 t4023 k74_1_6 k74_1_13
theorem cov74_1 : PA.Covered 1 (OZ.Valid 1 w74.low w74.t w74.y w74.r w74.cap) (P33.root 1) :=
  Night6836Tree.sound w74 pick74 1 t4024 _ k74_1_14
private theorem k74_2_0 : check w74 pick74 2 t3985 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k74_2_1 : check w74 pick74 2 t4008 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k74_2_2 : check w74 pick74 2 t4009 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w74 pick74 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3985 t4008 k74_2_0 k74_2_1
private theorem k74_2_3 : check w74 pick74 2 t4029 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k74_2_4 : check w74 pick74 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k74_2_5 : check w74 pick74 2 t4034 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w74 pick74 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4029 t4033 k74_2_3 k74_2_4
private theorem k74_2_6 : check w74 pick74 2 t4035 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w74 pick74 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4009 t4034 k74_2_2 k74_2_5
theorem cov74_2 : PA.Covered 2 (OZ.Valid 2 w74.low w74.t w74.y w74.r w74.cap) (P33.root 2) :=
  Night6836Tree.sound w74 pick74 2 t4035 _ k74_2_6
theorem cov74_3 : PA.Covered 3 (OZ.Valid 3 w74.low w74.t w74.y w74.r w74.cap) (P33.root 3) :=
  Night6836Tree.sound w74 pick74 3 t564 _ (by decide +kernel)
theorem cov74_4 : PA.Covered 4 (OZ.Valid 4 w74.low w74.t w74.y w74.r w74.cap) (P33.root 4) :=
  Night6836Tree.sound w74 pick74 4 t565 _ (by decide +kernel)
theorem cov74_5 : PA.Covered 5 (OZ.Valid 5 w74.low w74.t w74.y w74.r w74.cap) (P33.root 5) :=
  Night6836Tree.sound w74 pick74 5 t566 _ (by decide +kernel)
theorem cov74_6 : PA.Covered 6 (OZ.Valid 6 w74.low w74.t w74.y w74.r w74.cap) (P33.root 6) :=
  Night6836Tree.sound w74 pick74 6 t567 _ (by decide +kernel)
theorem cov74_7 : PA.Covered 7 (OZ.Valid 7 w74.low w74.t w74.y w74.r w74.cap) (P33.root 7) :=
  Night6836Tree.sound w74 pick74 7 t568 _ (by decide +kernel)
theorem window74 : P33.WindowCount w74 := by
  apply P33.window_count w74 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov74_1
  · exact cov74_2
  · exact cov74_3
  · exact cov74_4
  · exact cov74_5
  · exact cov74_6
  · exact cov74_7
def w75 : P33.Window := ⟨10,41,6947,6400,243922577270127567,29657,24000,5000000,81920000000⟩
def h75_0 : Height w75 := ⟨29657,24000,by decide +kernel⟩
def h75_1 : Height w75 := ⟨34218,21000,by decide +kernel⟩
def h75_2 : Height w75 := ⟨40568,18000,by decide +kernel⟩
def h75_3 : Height w75 := ⟨50915,15000,by decide +kernel⟩
def pick75 (cl : ℕ) : Height w75 := if cl<49 then (if cl<6 then (h75_0) else (h75_1)) else (if cl<644 then (h75_2) else (h75_3))
private theorem k75_1_0 : check w75 pick75 1 t4037 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k75_1_1 : check w75 pick75 1 t3910 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k75_1_2 : check w75 pick75 1 t4038 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w75 pick75 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t4037 t3910 k75_1_0 k75_1_1
private theorem k75_1_3 : check w75 pick75 1 t4043 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k75_1_4 : check w75 pick75 1 t4046 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k75_1_5 : check w75 pick75 1 t4047 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w75 pick75 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4043 t4046 k75_1_3 k75_1_4
private theorem k75_1_6 : check w75 pick75 1 t4062 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k75_1_7 : check w75 pick75 1 t4063 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w75 pick75 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4047 t4062 k75_1_5 k75_1_6
private theorem k75_1_8 : check w75 pick75 1 t4064 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w75 pick75 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4038 t4063 k75_1_2 k75_1_7
private theorem k75_1_9 : check w75 pick75 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k75_1_10 : check w75 pick75 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k75_1_11 : check w75 pick75 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w75 pick75 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k75_1_9 k75_1_10
private theorem k75_1_12 : check w75 pick75 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k75_1_13 : check w75 pick75 1 t4100 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k75_1_14 : check w75 pick75 1 t4101 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w75 pick75 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4100 k75_1_12 k75_1_13
private theorem k75_1_15 : check w75 pick75 1 t4102 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w75 pick75 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4101 k75_1_11 k75_1_14
private theorem k75_1_16 : check w75 pick75 1 t4103 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w75 pick75 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4064 t4102 k75_1_8 k75_1_15
theorem cov75_1 : PA.Covered 1 (OZ.Valid 1 w75.low w75.t w75.y w75.r w75.cap) (P33.root 1) :=
  Night6836Tree.sound w75 pick75 1 t4103 _ k75_1_16
private theorem k75_2_0 : check w75 pick75 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k75_2_1 : check w75 pick75 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k75_2_2 : check w75 pick75 2 t4132 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w75 pick75 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t4131 k75_2_0 k75_2_1
private theorem k75_2_3 : check w75 pick75 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k75_2_4 : check w75 pick75 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k75_2_5 : check w75 pick75 2 t4141 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w75 pick75 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t4033 k75_2_3 k75_2_4
private theorem k75_2_6 : check w75 pick75 2 t4142 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w75 pick75 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4132 t4141 k75_2_2 k75_2_5
theorem cov75_2 : PA.Covered 2 (OZ.Valid 2 w75.low w75.t w75.y w75.r w75.cap) (P33.root 2) :=
  Night6836Tree.sound w75 pick75 2 t4142 _ k75_2_6
theorem cov75_3 : PA.Covered 3 (OZ.Valid 3 w75.low w75.t w75.y w75.r w75.cap) (P33.root 3) :=
  Night6836Tree.sound w75 pick75 3 t4151 _ (by decide +kernel)
theorem cov75_4 : PA.Covered 4 (OZ.Valid 4 w75.low w75.t w75.y w75.r w75.cap) (P33.root 4) :=
  Night6836Tree.sound w75 pick75 4 t565 _ (by decide +kernel)
theorem cov75_5 : PA.Covered 5 (OZ.Valid 5 w75.low w75.t w75.y w75.r w75.cap) (P33.root 5) :=
  Night6836Tree.sound w75 pick75 5 t566 _ (by decide +kernel)
theorem cov75_6 : PA.Covered 6 (OZ.Valid 6 w75.low w75.t w75.y w75.r w75.cap) (P33.root 6) :=
  Night6836Tree.sound w75 pick75 6 t567 _ (by decide +kernel)
theorem cov75_7 : PA.Covered 7 (OZ.Valid 7 w75.low w75.t w75.y w75.r w75.cap) (P33.root 7) :=
  Night6836Tree.sound w75 pick75 7 t568 _ (by decide +kernel)
theorem window75 : P33.WindowCount w75 := by
  apply P33.window_count w75 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov75_1
  · exact cov75_2
  · exact cov75_3
  · exact cov75_4
  · exact cov75_5
  · exact cov75_6
  · exact cov75_7
def w76 : P33.Window := ⟨10,42,6297,5348,245301687316370789,35198,30000,5000000,81920000000⟩
def h76_0 : Height w76 := ⟨35198,30000,by decide +kernel⟩
def h76_1 : Height w76 := ⟨39334,27000,by decide +kernel⟩
def h76_2 : Height w76 := ⟨44542,24000,by decide +kernel⟩
def h76_3 : Height w76 := ⟨51638,21000,by decide +kernel⟩
def h76_4 : Height w76 := ⟨62556,18000,by decide +kernel⟩
def pick76 (cl : ℕ) : Height w76 := if cl<25 then (if cl<3 then (h76_0) else (h76_1)) else (if cl<97 then (h76_2) else (if cl<853 then (h76_3) else (h76_4)))
private theorem k76_1_0 : check w76 pick76 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k76_1_1 : check w76 pick76 1 t3253 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k76_1_2 : check w76 pick76 1 t3254 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w76 pick76 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t3253 k76_1_0 k76_1_1
private theorem k76_1_3 : check w76 pick76 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k76_1_4 : check w76 pick76 1 t3195 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k76_1_5 : check w76 pick76 1 t3264 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w76 pick76 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t3195 k76_1_3 k76_1_4
private theorem k76_1_6 : check w76 pick76 1 t3265 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w76 pick76 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t3254 t3264 k76_1_2 k76_1_5
private theorem k76_1_7 : check w76 pick76 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k76_1_8 : check w76 pick76 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k76_1_9 : check w76 pick76 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w76 pick76 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k76_1_7 k76_1_8
private theorem k76_1_10 : check w76 pick76 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k76_1_11 : check w76 pick76 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k76_1_12 : check w76 pick76 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w76 pick76 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k76_1_10 k76_1_11
private theorem k76_1_13 : check w76 pick76 1 t3201 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w76 pick76 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t1079 k76_1_9 k76_1_12
private theorem k76_1_14 : check w76 pick76 1 t3266 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w76 pick76 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t3265 t3201 k76_1_6 k76_1_13
theorem cov76_1 : PA.Covered 1 (OZ.Valid 1 w76.low w76.t w76.y w76.r w76.cap) (P33.root 1) :=
  Night6836Tree.sound w76 pick76 1 t3266 _ k76_1_14
private theorem k76_2_0 : check w76 pick76 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k76_2_1 : check w76 pick76 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k76_2_2 : check w76 pick76 2 t3491 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w76 pick76 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3490 k76_2_0 k76_2_1
private theorem k76_2_3 : check w76 pick76 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k76_2_4 : check w76 pick76 2 t4155 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k76_2_5 : check w76 pick76 2 t4156 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w76 pick76 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4155 k76_2_3 k76_2_4
private theorem k76_2_6 : check w76 pick76 2 t4157 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w76 pick76 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3491 t4156 k76_2_2 k76_2_5
theorem cov76_2 : PA.Covered 2 (OZ.Valid 2 w76.low w76.t w76.y w76.r w76.cap) (P33.root 2) :=
  Night6836Tree.sound w76 pick76 2 t4157 _ k76_2_6
theorem cov76_3 : PA.Covered 3 (OZ.Valid 3 w76.low w76.t w76.y w76.r w76.cap) (P33.root 3) :=
  Night6836Tree.sound w76 pick76 3 t564 _ (by decide +kernel)
theorem cov76_4 : PA.Covered 4 (OZ.Valid 4 w76.low w76.t w76.y w76.r w76.cap) (P33.root 4) :=
  Night6836Tree.sound w76 pick76 4 t565 _ (by decide +kernel)
theorem cov76_5 : PA.Covered 5 (OZ.Valid 5 w76.low w76.t w76.y w76.r w76.cap) (P33.root 5) :=
  Night6836Tree.sound w76 pick76 5 t566 _ (by decide +kernel)
theorem cov76_6 : PA.Covered 6 (OZ.Valid 6 w76.low w76.t w76.y w76.r w76.cap) (P33.root 6) :=
  Night6836Tree.sound w76 pick76 6 t567 _ (by decide +kernel)
theorem cov76_7 : PA.Covered 7 (OZ.Valid 7 w76.low w76.t w76.y w76.r w76.cap) (P33.root 7) :=
  Night6836Tree.sound w76 pick76 7 t2134 _ (by decide +kernel)
theorem window76 : P33.WindowCount w76 := by
  apply P33.window_count w76 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov76_1
  · exact cov76_2
  · exact cov76_3
  · exact cov76_4
  · exact cov76_5
  · exact cov76_6
  · exact cov76_7
def w77 : P33.Window := ⟨10,42,6891,6557,246618597510796910,29314,24000,5000000,81920000000⟩
def h77_0 : Height w77 := ⟨29314,24000,by decide +kernel⟩
def h77_1 : Height w77 := ⟨33736,21000,by decide +kernel⟩
def h77_2 : Height w77 := ⟨39836,18000,by decide +kernel⟩
def h77_3 : Height w77 := ⟨49634,15000,by decide +kernel⟩
def pick77 (cl : ℕ) : Height w77 := if cl<42 then (if cl<5 then (h77_0) else (h77_1)) else (if cl<395 then (h77_2) else (h77_3))
private theorem k77_1_0 : check w77 pick77 1 t4037 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k77_1_1 : check w77 pick77 1 t4166 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k77_1_2 : check w77 pick77 1 t4167 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w77 pick77 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t4037 t4166 k77_1_0 k77_1_1
private theorem k77_1_3 : check w77 pick77 1 t4171 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k77_1_4 : check w77 pick77 1 t4174 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k77_1_5 : check w77 pick77 1 t4175 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w77 pick77 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4171 t4174 k77_1_3 k77_1_4
private theorem k77_1_6 : check w77 pick77 1 t4062 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k77_1_7 : check w77 pick77 1 t4176 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w77 pick77 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4175 t4062 k77_1_5 k77_1_6
private theorem k77_1_8 : check w77 pick77 1 t4177 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w77 pick77 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4167 t4176 k77_1_2 k77_1_7
private theorem k77_1_9 : check w77 pick77 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k77_1_10 : check w77 pick77 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k77_1_11 : check w77 pick77 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w77 pick77 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k77_1_9 k77_1_10
private theorem k77_1_12 : check w77 pick77 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k77_1_13 : check w77 pick77 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k77_1_14 : check w77 pick77 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w77 pick77 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k77_1_12 k77_1_13
private theorem k77_1_15 : check w77 pick77 1 t4180 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w77 pick77 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4179 k77_1_11 k77_1_14
private theorem k77_1_16 : check w77 pick77 1 t4181 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w77 pick77 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4177 t4180 k77_1_8 k77_1_15
theorem cov77_1 : PA.Covered 1 (OZ.Valid 1 w77.low w77.t w77.y w77.r w77.cap) (P33.root 1) :=
  Night6836Tree.sound w77 pick77 1 t4181 _ k77_1_16
private theorem k77_2_0 : check w77 pick77 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k77_2_1 : check w77 pick77 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k77_2_2 : check w77 pick77 2 t4132 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w77 pick77 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t4131 k77_2_0 k77_2_1
private theorem k77_2_3 : check w77 pick77 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k77_2_4 : check w77 pick77 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k77_2_5 : check w77 pick77 2 t4141 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w77 pick77 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t4033 k77_2_3 k77_2_4
private theorem k77_2_6 : check w77 pick77 2 t4142 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w77 pick77 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4132 t4141 k77_2_2 k77_2_5
theorem cov77_2 : PA.Covered 2 (OZ.Valid 2 w77.low w77.t w77.y w77.r w77.cap) (P33.root 2) :=
  Night6836Tree.sound w77 pick77 2 t4142 _ k77_2_6
theorem cov77_3 : PA.Covered 3 (OZ.Valid 3 w77.low w77.t w77.y w77.r w77.cap) (P33.root 3) :=
  Night6836Tree.sound w77 pick77 3 t4151 _ (by decide +kernel)
theorem cov77_4 : PA.Covered 4 (OZ.Valid 4 w77.low w77.t w77.y w77.r w77.cap) (P33.root 4) :=
  Night6836Tree.sound w77 pick77 4 t565 _ (by decide +kernel)
theorem cov77_5 : PA.Covered 5 (OZ.Valid 5 w77.low w77.t w77.y w77.r w77.cap) (P33.root 5) :=
  Night6836Tree.sound w77 pick77 5 t566 _ (by decide +kernel)
theorem cov77_6 : PA.Covered 6 (OZ.Valid 6 w77.low w77.t w77.y w77.r w77.cap) (P33.root 6) :=
  Night6836Tree.sound w77 pick77 6 t567 _ (by decide +kernel)
theorem cov77_7 : PA.Covered 7 (OZ.Valid 7 w77.low w77.t w77.y w77.r w77.cap) (P33.root 7) :=
  Night6836Tree.sound w77 pick77 7 t568 _ (by decide +kernel)
theorem window77 : P33.WindowCount w77 := by
  apply P33.window_count w77 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov77_1
  · exact cov77_2
  · exact cov77_3
  · exact cov77_4
  · exact cov77_5
  · exact cov77_6
  · exact cov77_7
def w78 : P33.Window := ⟨10,43,6834,6606,244110522773536197,29970,24000,5000000,81920000000⟩
def h78_0 : Height w78 := ⟨29970,24000,by decide +kernel⟩
def h78_1 : Height w78 := ⟨34404,21000,by decide +kernel⟩
def h78_2 : Height w78 := ⟨40513,18000,by decide +kernel⟩
def h78_3 : Height w78 := ⟨50300,15000,by decide +kernel⟩
def pick78 (cl : ℕ) : Height w78 := if cl<42 then (if cl<5 then (h78_0) else (h78_1)) else (if cl<395 then (h78_2) else (h78_3))
private theorem k78_1_0 : check w78 pick78 1 t4189 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k78_1_1 : check w78 pick78 1 t4197 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k78_1_2 : check w78 pick78 1 t4198 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w78 pick78 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t4189 t4197 k78_1_0 k78_1_1
private theorem k78_1_3 : check w78 pick78 1 t4171 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k78_1_4 : check w78 pick78 1 t4174 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k78_1_5 : check w78 pick78 1 t4175 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w78 pick78 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4171 t4174 k78_1_3 k78_1_4
private theorem k78_1_6 : check w78 pick78 1 t4062 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k78_1_7 : check w78 pick78 1 t4176 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w78 pick78 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4175 t4062 k78_1_5 k78_1_6
private theorem k78_1_8 : check w78 pick78 1 t4199 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w78 pick78 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4198 t4176 k78_1_2 k78_1_7
private theorem k78_1_9 : check w78 pick78 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k78_1_10 : check w78 pick78 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k78_1_11 : check w78 pick78 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w78 pick78 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k78_1_9 k78_1_10
private theorem k78_1_12 : check w78 pick78 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k78_1_13 : check w78 pick78 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k78_1_14 : check w78 pick78 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w78 pick78 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k78_1_12 k78_1_13
private theorem k78_1_15 : check w78 pick78 1 t4180 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w78 pick78 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4179 k78_1_11 k78_1_14
private theorem k78_1_16 : check w78 pick78 1 t4200 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w78 pick78 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4199 t4180 k78_1_8 k78_1_15
theorem cov78_1 : PA.Covered 1 (OZ.Valid 1 w78.low w78.t w78.y w78.r w78.cap) (P33.root 1) :=
  Night6836Tree.sound w78 pick78 1 t4200 _ k78_1_16
private theorem k78_2_0 : check w78 pick78 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k78_2_1 : check w78 pick78 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k78_2_2 : check w78 pick78 2 t4132 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w78 pick78 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t4131 k78_2_0 k78_2_1
private theorem k78_2_3 : check w78 pick78 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k78_2_4 : check w78 pick78 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k78_2_5 : check w78 pick78 2 t4141 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w78 pick78 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t4033 k78_2_3 k78_2_4
private theorem k78_2_6 : check w78 pick78 2 t4142 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w78 pick78 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4132 t4141 k78_2_2 k78_2_5
theorem cov78_2 : PA.Covered 2 (OZ.Valid 2 w78.low w78.t w78.y w78.r w78.cap) (P33.root 2) :=
  Night6836Tree.sound w78 pick78 2 t4142 _ k78_2_6
theorem cov78_3 : PA.Covered 3 (OZ.Valid 3 w78.low w78.t w78.y w78.r w78.cap) (P33.root 3) :=
  Night6836Tree.sound w78 pick78 3 t4151 _ (by decide +kernel)
theorem cov78_4 : PA.Covered 4 (OZ.Valid 4 w78.low w78.t w78.y w78.r w78.cap) (P33.root 4) :=
  Night6836Tree.sound w78 pick78 4 t565 _ (by decide +kernel)
theorem cov78_5 : PA.Covered 5 (OZ.Valid 5 w78.low w78.t w78.y w78.r w78.cap) (P33.root 5) :=
  Night6836Tree.sound w78 pick78 5 t566 _ (by decide +kernel)
theorem cov78_6 : PA.Covered 6 (OZ.Valid 6 w78.low w78.t w78.y w78.r w78.cap) (P33.root 6) :=
  Night6836Tree.sound w78 pick78 6 t567 _ (by decide +kernel)
theorem cov78_7 : PA.Covered 7 (OZ.Valid 7 w78.low w78.t w78.y w78.r w78.cap) (P33.root 7) :=
  Night6836Tree.sound w78 pick78 7 t568 _ (by decide +kernel)
theorem window78 : P33.WindowCount w78 := by
  apply P33.window_count w78 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov78_1
  · exact cov78_2
  · exact cov78_3
  · exact cov78_4
  · exact cov78_5
  · exact cov78_6
  · exact cov78_7
def w79 : P33.Window := ⟨10,44,6776,6716,247108163784963121,30053,24000,5000000,81920000000⟩
def h79_0 : Height w79 := ⟨30053,24000,by decide +kernel⟩
def h79_1 : Height w79 := ⟨34418,21000,by decide +kernel⟩
def h79_2 : Height w79 := ⟨40400,18000,by decide +kernel⟩
def h79_3 : Height w79 := ⟨49902,15000,by decide +kernel⟩
def h79_4 : Height w79 := ⟨69698,12000,by decide +kernel⟩
def pick79 (cl : ℕ) : Height w79 := if cl<37 then (if cl<5 then (h79_0) else (h79_1)) else (if cl<317 then (h79_2) else (if cl<1026 then (h79_3) else (h79_4)))
private theorem k79_1_0 : check w79 pick79 1 t4189 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k79_1_1 : check w79 pick79 1 t4208 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k79_1_2 : check w79 pick79 1 t4209 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w79 pick79 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t4189 t4208 k79_1_0 k79_1_1
private theorem k79_1_3 : check w79 pick79 1 t4171 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k79_1_4 : check w79 pick79 1 t4174 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k79_1_5 : check w79 pick79 1 t4175 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w79 pick79 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4171 t4174 k79_1_3 k79_1_4
private theorem k79_1_6 : check w79 pick79 1 t4062 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k79_1_7 : check w79 pick79 1 t4176 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w79 pick79 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4175 t4062 k79_1_5 k79_1_6
private theorem k79_1_8 : check w79 pick79 1 t4210 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w79 pick79 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4209 t4176 k79_1_2 k79_1_7
private theorem k79_1_9 : check w79 pick79 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k79_1_10 : check w79 pick79 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k79_1_11 : check w79 pick79 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w79 pick79 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k79_1_9 k79_1_10
private theorem k79_1_12 : check w79 pick79 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k79_1_13 : check w79 pick79 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k79_1_14 : check w79 pick79 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w79 pick79 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k79_1_12 k79_1_13
private theorem k79_1_15 : check w79 pick79 1 t4180 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w79 pick79 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4179 k79_1_11 k79_1_14
private theorem k79_1_16 : check w79 pick79 1 t4211 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w79 pick79 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4210 t4180 k79_1_8 k79_1_15
theorem cov79_1 : PA.Covered 1 (OZ.Valid 1 w79.low w79.t w79.y w79.r w79.cap) (P33.root 1) :=
  Night6836Tree.sound w79 pick79 1 t4211 _ k79_1_16
private theorem k79_2_0 : check w79 pick79 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k79_2_1 : check w79 pick79 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k79_2_2 : check w79 pick79 2 t4132 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w79 pick79 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t4131 k79_2_0 k79_2_1
private theorem k79_2_3 : check w79 pick79 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k79_2_4 : check w79 pick79 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k79_2_5 : check w79 pick79 2 t4141 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w79 pick79 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t4033 k79_2_3 k79_2_4
private theorem k79_2_6 : check w79 pick79 2 t4142 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w79 pick79 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4132 t4141 k79_2_2 k79_2_5
theorem cov79_2 : PA.Covered 2 (OZ.Valid 2 w79.low w79.t w79.y w79.r w79.cap) (P33.root 2) :=
  Night6836Tree.sound w79 pick79 2 t4142 _ k79_2_6
theorem cov79_3 : PA.Covered 3 (OZ.Valid 3 w79.low w79.t w79.y w79.r w79.cap) (P33.root 3) :=
  Night6836Tree.sound w79 pick79 3 t4151 _ (by decide +kernel)
theorem cov79_4 : PA.Covered 4 (OZ.Valid 4 w79.low w79.t w79.y w79.r w79.cap) (P33.root 4) :=
  Night6836Tree.sound w79 pick79 4 t565 _ (by decide +kernel)
theorem cov79_5 : PA.Covered 5 (OZ.Valid 5 w79.low w79.t w79.y w79.r w79.cap) (P33.root 5) :=
  Night6836Tree.sound w79 pick79 5 t566 _ (by decide +kernel)
theorem cov79_6 : PA.Covered 6 (OZ.Valid 6 w79.low w79.t w79.y w79.r w79.cap) (P33.root 6) :=
  Night6836Tree.sound w79 pick79 6 t567 _ (by decide +kernel)
theorem cov79_7 : PA.Covered 7 (OZ.Valid 7 w79.low w79.t w79.y w79.r w79.cap) (P33.root 7) :=
  Night6836Tree.sound w79 pick79 7 t568 _ (by decide +kernel)
theorem window79 : P33.WindowCount w79 := by
  apply P33.window_count w79 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov79_1
  · exact cov79_2
  · exact cov79_3
  · exact cov79_4
  · exact cov79_5
  · exact cov79_6
  · exact cov79_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w80 : P33.Window := ⟨10,45,6715,6647,247375926791161974,31779,24000,5000000,81920000000⟩
def h80_0 : Height w80 := ⟨31779,24000,by decide +kernel⟩
def h80_1 : Height w80 := ⟨36309,21000,by decide +kernel⟩
def h80_2 : Height w80 := ⟨42561,18000,by decide +kernel⟩
def h80_3 : Height w80 := ⟨52579,15000,by decide +kernel⟩
def pick80 (cl : ℕ) : Height w80 := if cl<45 then (if cl<6 then (h80_0) else (h80_1)) else (if cl<493 then (h80_2) else (h80_3))
private theorem k80_1_0 : check w80 pick80 1 t4189 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k80_1_1 : check w80 pick80 1 t4197 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k80_1_2 : check w80 pick80 1 t4198 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w80 pick80 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t4189 t4197 k80_1_0 k80_1_1
private theorem k80_1_3 : check w80 pick80 1 t4171 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k80_1_4 : check w80 pick80 1 t4174 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k80_1_5 : check w80 pick80 1 t4175 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w80 pick80 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4171 t4174 k80_1_3 k80_1_4
private theorem k80_1_6 : check w80 pick80 1 t4215 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k80_1_7 : check w80 pick80 1 t4216 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w80 pick80 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4175 t4215 k80_1_5 k80_1_6
private theorem k80_1_8 : check w80 pick80 1 t4217 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w80 pick80 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4198 t4216 k80_1_2 k80_1_7
private theorem k80_1_9 : check w80 pick80 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k80_1_10 : check w80 pick80 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k80_1_11 : check w80 pick80 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w80 pick80 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k80_1_9 k80_1_10
private theorem k80_1_12 : check w80 pick80 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k80_1_13 : check w80 pick80 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k80_1_14 : check w80 pick80 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w80 pick80 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k80_1_12 k80_1_13
private theorem k80_1_15 : check w80 pick80 1 t4180 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w80 pick80 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4179 k80_1_11 k80_1_14
private theorem k80_1_16 : check w80 pick80 1 t4218 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w80 pick80 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4217 t4180 k80_1_8 k80_1_15
theorem cov80_1 : PA.Covered 1 (OZ.Valid 1 w80.low w80.t w80.y w80.r w80.cap) (P33.root 1) :=
  Night6836Tree.sound w80 pick80 1 t4218 _ k80_1_16
private theorem k80_2_0 : check w80 pick80 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k80_2_1 : check w80 pick80 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k80_2_2 : check w80 pick80 2 t4132 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w80 pick80 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t4131 k80_2_0 k80_2_1
private theorem k80_2_3 : check w80 pick80 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k80_2_4 : check w80 pick80 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k80_2_5 : check w80 pick80 2 t4225 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w80 pick80 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t4033 k80_2_3 k80_2_4
private theorem k80_2_6 : check w80 pick80 2 t4226 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w80 pick80 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4132 t4225 k80_2_2 k80_2_5
theorem cov80_2 : PA.Covered 2 (OZ.Valid 2 w80.low w80.t w80.y w80.r w80.cap) (P33.root 2) :=
  Night6836Tree.sound w80 pick80 2 t4226 _ k80_2_6
theorem cov80_3 : PA.Covered 3 (OZ.Valid 3 w80.low w80.t w80.y w80.r w80.cap) (P33.root 3) :=
  Night6836Tree.sound w80 pick80 3 t4231 _ (by decide +kernel)
theorem cov80_4 : PA.Covered 4 (OZ.Valid 4 w80.low w80.t w80.y w80.r w80.cap) (P33.root 4) :=
  Night6836Tree.sound w80 pick80 4 t565 _ (by decide +kernel)
theorem cov80_5 : PA.Covered 5 (OZ.Valid 5 w80.low w80.t w80.y w80.r w80.cap) (P33.root 5) :=
  Night6836Tree.sound w80 pick80 5 t566 _ (by decide +kernel)
theorem cov80_6 : PA.Covered 6 (OZ.Valid 6 w80.low w80.t w80.y w80.r w80.cap) (P33.root 6) :=
  Night6836Tree.sound w80 pick80 6 t567 _ (by decide +kernel)
theorem cov80_7 : PA.Covered 7 (OZ.Valid 7 w80.low w80.t w80.y w80.r w80.cap) (P33.root 7) :=
  Night6836Tree.sound w80 pick80 7 t568 _ (by decide +kernel)
theorem window80 : P33.WindowCount w80 := by
  apply P33.window_count w80 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov80_1
  · exact cov80_2
  · exact cov80_3
  · exact cov80_4
  · exact cov80_5
  · exact cov80_6
  · exact cov80_7
def w81 : P33.Window := ⟨10,46,6646,6576,247378984294054626,33578,24000,5000000,81920000000⟩
def h81_0 : Height w81 := ⟨33578,24000,by decide +kernel⟩
def h81_1 : Height w81 := ⟨38285,21000,by decide +kernel⟩
def h81_2 : Height w81 := ⟨44827,18000,by decide +kernel⟩
def h81_3 : Height w81 := ⟨55405,15000,by decide +kernel⟩
def pick81 (cl : ℕ) : Height w81 := if cl<60 then (if cl<10 then (h81_0) else (h81_1)) else (if cl<728 then (h81_2) else (h81_3))
private theorem k81_1_0 : check w81 pick81 1 t4189 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k81_1_1 : check w81 pick81 1 t4197 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k81_1_2 : check w81 pick81 1 t4198 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w81 pick81 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t4189 t4197 k81_1_0 k81_1_1
private theorem k81_1_3 : check w81 pick81 1 t4171 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k81_1_4 : check w81 pick81 1 t4174 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k81_1_5 : check w81 pick81 1 t4175 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w81 pick81 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4171 t4174 k81_1_3 k81_1_4
private theorem k81_1_6 : check w81 pick81 1 t4215 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k81_1_7 : check w81 pick81 1 t4216 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w81 pick81 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4175 t4215 k81_1_5 k81_1_6
private theorem k81_1_8 : check w81 pick81 1 t4217 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w81 pick81 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4198 t4216 k81_1_2 k81_1_7
private theorem k81_1_9 : check w81 pick81 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k81_1_10 : check w81 pick81 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k81_1_11 : check w81 pick81 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w81 pick81 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k81_1_9 k81_1_10
private theorem k81_1_12 : check w81 pick81 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k81_1_13 : check w81 pick81 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k81_1_14 : check w81 pick81 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w81 pick81 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k81_1_12 k81_1_13
private theorem k81_1_15 : check w81 pick81 1 t4180 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w81 pick81 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4179 k81_1_11 k81_1_14
private theorem k81_1_16 : check w81 pick81 1 t4218 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w81 pick81 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4217 t4180 k81_1_8 k81_1_15
theorem cov81_1 : PA.Covered 1 (OZ.Valid 1 w81.low w81.t w81.y w81.r w81.cap) (P33.root 1) :=
  Night6836Tree.sound w81 pick81 1 t4218 _ k81_1_16
private theorem k81_2_0 : check w81 pick81 2 t4241 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k81_2_1 : check w81 pick81 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k81_2_2 : check w81 pick81 2 t4242 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w81 pick81 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4241 t4131 k81_2_0 k81_2_1
private theorem k81_2_3 : check w81 pick81 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k81_2_4 : check w81 pick81 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k81_2_5 : check w81 pick81 2 t4225 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w81 pick81 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t4033 k81_2_3 k81_2_4
private theorem k81_2_6 : check w81 pick81 2 t4243 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w81 pick81 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4242 t4225 k81_2_2 k81_2_5
theorem cov81_2 : PA.Covered 2 (OZ.Valid 2 w81.low w81.t w81.y w81.r w81.cap) (P33.root 2) :=
  Night6836Tree.sound w81 pick81 2 t4243 _ k81_2_6
theorem cov81_3 : PA.Covered 3 (OZ.Valid 3 w81.low w81.t w81.y w81.r w81.cap) (P33.root 3) :=
  Night6836Tree.sound w81 pick81 3 t4231 _ (by decide +kernel)
theorem cov81_4 : PA.Covered 4 (OZ.Valid 4 w81.low w81.t w81.y w81.r w81.cap) (P33.root 4) :=
  Night6836Tree.sound w81 pick81 4 t565 _ (by decide +kernel)
theorem cov81_5 : PA.Covered 5 (OZ.Valid 5 w81.low w81.t w81.y w81.r w81.cap) (P33.root 5) :=
  Night6836Tree.sound w81 pick81 5 t566 _ (by decide +kernel)
theorem cov81_6 : PA.Covered 6 (OZ.Valid 6 w81.low w81.t w81.y w81.r w81.cap) (P33.root 6) :=
  Night6836Tree.sound w81 pick81 6 t567 _ (by decide +kernel)
theorem cov81_7 : PA.Covered 7 (OZ.Valid 7 w81.low w81.t w81.y w81.r w81.cap) (P33.root 7) :=
  Night6836Tree.sound w81 pick81 7 t568 _ (by decide +kernel)
theorem window81 : P33.WindowCount w81 := by
  apply P33.window_count w81 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov81_1
  · exact cov81_2
  · exact cov81_3
  · exact cov81_4
  · exact cov81_5
  · exact cov81_6
  · exact cov81_7
def w82 : P33.Window := ⟨10,47,4052,3103,234444124124142361,69256,54000,5000000,81920000000⟩
def h82_0 : Height w82 := ⟨69256,54000,by decide +kernel⟩
def h82_1 : Height w82 := ⟨73188,51000,by decide +kernel⟩
def h82_2 : Height w82 := ⟨77572,48000,by decide +kernel⟩
def h82_3 : Height w82 := ⟨82548,45000,by decide +kernel⟩
def h82_4 : Height w82 := ⟨88318,42000,by decide +kernel⟩
def h82_5 : Height w82 := ⟨95187,39000,by decide +kernel⟩
def h82_6 : Height w82 := ⟨103643,36000,by decide +kernel⟩
def pick82 (cl : ℕ) : Height w82 := if cl<13 then (if cl<2 then (h82_0) else (if cl<5 then (h82_1) else (h82_2))) else (if cl<83 then (if cl<32 then (h82_3) else (h82_4)) else (if cl<236 then (h82_5) else (h82_6)))
private theorem k82_1_0 : check w82 pick82 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k82_1_1 : check w82 pick82 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k82_1_2 : check w82 pick82 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w82 pick82 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k82_1_0 k82_1_1
private theorem k82_1_3 : check w82 pick82 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k82_1_4 : check w82 pick82 1 t4252 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k82_1_5 : check w82 pick82 1 t4253 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w82 pick82 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t4252 k82_1_3 k82_1_4
private theorem k82_1_6 : check w82 pick82 1 t4254 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w82 pick82 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t4253 k82_1_2 k82_1_5
private theorem k82_1_7 : check w82 pick82 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k82_1_8 : check w82 pick82 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k82_1_9 : check w82 pick82 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w82 pick82 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k82_1_7 k82_1_8
private theorem k82_1_10 : check w82 pick82 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k82_1_11 : check w82 pick82 1 t4260 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k82_1_12 : check w82 pick82 1 t4261 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w82 pick82 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t4260 k82_1_10 k82_1_11
private theorem k82_1_13 : check w82 pick82 1 t4262 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w82 pick82 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t4261 k82_1_9 k82_1_12
private theorem k82_1_14 : check w82 pick82 1 t4263 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w82 pick82 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4254 t4262 k82_1_6 k82_1_13
theorem cov82_1 : PA.Covered 1 (OZ.Valid 1 w82.low w82.t w82.y w82.r w82.cap) (P33.root 1) :=
  Night6836Tree.sound w82 pick82 1 t4263 _ k82_1_14
theorem cov82_2 : PA.Covered 2 (OZ.Valid 2 w82.low w82.t w82.y w82.r w82.cap) (P33.root 2) :=
  Night6836Tree.sound w82 pick82 2 t4274 _ (by decide +kernel)
theorem cov82_3 : PA.Covered 3 (OZ.Valid 3 w82.low w82.t w82.y w82.r w82.cap) (P33.root 3) :=
  Night6836Tree.sound w82 pick82 3 t564 _ (by decide +kernel)
theorem cov82_4 : PA.Covered 4 (OZ.Valid 4 w82.low w82.t w82.y w82.r w82.cap) (P33.root 4) :=
  Night6836Tree.sound w82 pick82 4 t565 _ (by decide +kernel)
theorem cov82_5 : PA.Covered 5 (OZ.Valid 5 w82.low w82.t w82.y w82.r w82.cap) (P33.root 5) :=
  Night6836Tree.sound w82 pick82 5 t566 _ (by decide +kernel)
theorem cov82_6 : PA.Covered 6 (OZ.Valid 6 w82.low w82.t w82.y w82.r w82.cap) (P33.root 6) :=
  Night6836Tree.sound w82 pick82 6 t567 _ (by decide +kernel)
theorem cov82_7 : PA.Covered 7 (OZ.Valid 7 w82.low w82.t w82.y w82.r w82.cap) (P33.root 7) :=
  Night6836Tree.sound w82 pick82 7 t2134 _ (by decide +kernel)
theorem window82 : P33.WindowCount w82 := by
  apply P33.window_count w82 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov82_1
  · exact cov82_2
  · exact cov82_3
  · exact cov82_4
  · exact cov82_5
  · exact cov82_6
  · exact cov82_7
def w83 : P33.Window := ⟨10,47,6556,5607,246118218771218426,38234,30000,5000000,81920000000⟩
def h83_0 : Height w83 := ⟨38234,30000,by decide +kernel⟩
def h83_1 : Height w83 := ⟨42336,27000,by decide +kernel⟩
def h83_2 : Height w83 := ⟨47465,24000,by decide +kernel⟩
def h83_3 : Height w83 := ⟨54378,21000,by decide +kernel⟩
def h83_4 : Height w83 := ⟨64814,18000,by decide +kernel⟩
def h83_5 : Height w83 := ⟨83832,15000,by decide +kernel⟩
def pick83 (cl : ℕ) : Height w83 := if cl<90 then (if cl<2 then (h83_0) else (if cl<17 then (h83_1) else (h83_2))) else (if cl<728 then (h83_3) else (if cl<1026 then (h83_4) else (h83_5)))
private theorem k83_1_0 : check w83 pick83 1 t4290 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k83_1_1 : check w83 pick83 1 t4325 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k83_1_2 : check w83 pick83 1 t4326 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w83 pick83 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t4290 t4325 k83_1_0 k83_1_1
private theorem k83_1_3 : check w83 pick83 1 t4358 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k83_1_4 : check w83 pick83 1 t4380 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k83_1_5 : check w83 pick83 1 t4381 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w83 pick83 1 ⟨1,7,2,16,1,52,70,131⟩ 3 104 t4358 t4380 k83_1_3 k83_1_4
private theorem k83_1_6 : check w83 pick83 1 t4382 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w83 pick83 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t4326 t4381 k83_1_2 k83_1_5
private theorem k83_1_7 : check w83 pick83 1 t4407 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k83_1_8 : check w83 pick83 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k83_1_9 : check w83 pick83 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k83_1_10 : check w83 pick83 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w83 pick83 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k83_1_8 k83_1_9
private theorem k83_1_11 : check w83 pick83 1 t4433 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w83 pick83 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t4407 t4432 k83_1_7 k83_1_10
private theorem k83_1_12 : check w83 pick83 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k83_1_13 : check w83 pick83 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k83_1_14 : check w83 pick83 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w83 pick83 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k83_1_12 k83_1_13
private theorem k83_1_15 : check w83 pick83 1 t4434 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w83 pick83 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4433 t4179 k83_1_11 k83_1_14
private theorem k83_1_16 : check w83 pick83 1 t4435 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w83 pick83 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t4382 t4434 k83_1_6 k83_1_15
theorem cov83_1 : PA.Covered 1 (OZ.Valid 1 w83.low w83.t w83.y w83.r w83.cap) (P33.root 1) :=
  Night6836Tree.sound w83 pick83 1 t4435 _ k83_1_16
private theorem k83_2_0 : check w83 pick83 2 t4443 ⟨2,7,4,16,2,52,2,56⟩ = true := by decide +kernel
private theorem k83_2_1 : check w83 pick83 2 t4463 ⟨2,7,4,16,2,52,57,84⟩ = true := by decide +kernel
private theorem k83_2_2 : check w83 pick83 2 t4464 ⟨2,7,4,16,2,52,2,84⟩ = true := glue w83 pick83 2 ⟨2,7,4,16,2,52,2,84⟩ 3 56 t4443 t4463 k83_2_0 k83_2_1
private theorem k83_2_3 : check w83 pick83 2 t4479 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k83_2_4 : check w83 pick83 2 t4480 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w83 pick83 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4464 t4479 k83_2_2 k83_2_3
private theorem k83_2_5 : check w83 pick83 2 t4503 ⟨2,7,4,16,2,52,140,248⟩ = true := by decide +kernel
private theorem k83_2_6 : check w83 pick83 2 t4531 ⟨2,7,4,16,2,52,249,450⟩ = true := by decide +kernel
private theorem k83_2_7 : check w83 pick83 2 t4532 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w83 pick83 2 ⟨2,7,4,16,2,52,140,450⟩ 3 248 t4503 t4531 k83_2_5 k83_2_6
private theorem k83_2_8 : check w83 pick83 2 t4533 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w83 pick83 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4480 t4532 k83_2_4 k83_2_7
theorem cov83_2 : PA.Covered 2 (OZ.Valid 2 w83.low w83.t w83.y w83.r w83.cap) (P33.root 2) :=
  Night6836Tree.sound w83 pick83 2 t4533 _ k83_2_8
theorem cov83_3 : PA.Covered 3 (OZ.Valid 3 w83.low w83.t w83.y w83.r w83.cap) (P33.root 3) :=
  Night6836Tree.sound w83 pick83 3 t4231 _ (by decide +kernel)
theorem cov83_4 : PA.Covered 4 (OZ.Valid 4 w83.low w83.t w83.y w83.r w83.cap) (P33.root 4) :=
  Night6836Tree.sound w83 pick83 4 t565 _ (by decide +kernel)
theorem cov83_5 : PA.Covered 5 (OZ.Valid 5 w83.low w83.t w83.y w83.r w83.cap) (P33.root 5) :=
  Night6836Tree.sound w83 pick83 5 t566 _ (by decide +kernel)
theorem cov83_6 : PA.Covered 6 (OZ.Valid 6 w83.low w83.t w83.y w83.r w83.cap) (P33.root 6) :=
  Night6836Tree.sound w83 pick83 6 t567 _ (by decide +kernel)
theorem cov83_7 : PA.Covered 7 (OZ.Valid 7 w83.low w83.t w83.y w83.r w83.cap) (P33.root 7) :=
  Night6836Tree.sound w83 pick83 7 t568 _ (by decide +kernel)
theorem window83 : P33.WindowCount w83 := by
  apply P33.window_count w83 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov83_1
  · exact cov83_2
  · exact cov83_3
  · exact cov83_4
  · exact cov83_5
  · exact cov83_6
  · exact cov83_7
def w84 : P33.Window := ⟨10,47,6575,6496,247368604123164362,35531,24000,5000000,81920000000⟩
def h84_0 : Height w84 := ⟨35531,24000,by decide +kernel⟩
def h84_1 : Height w84 := ⟨40438,21000,by decide +kernel⟩
def h84_2 : Height w84 := ⟨47312,18000,by decide +kernel⟩
def h84_3 : Height w84 := ⟨58539,15000,by decide +kernel⟩
def pick84 (cl : ℕ) : Height w84 := if cl<82 then (if cl<13 then (h84_0) else (h84_1)) else (if cl<830 then (h84_2) else (h84_3))
private theorem k84_1_0 : check w84 pick84 1 t4544 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k84_1_1 : check w84 pick84 1 t4555 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k84_1_2 : check w84 pick84 1 t4556 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w84 pick84 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t4544 t4555 k84_1_0 k84_1_1
private theorem k84_1_3 : check w84 pick84 1 t4569 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k84_1_4 : check w84 pick84 1 t4601 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k84_1_5 : check w84 pick84 1 t4602 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w84 pick84 1 ⟨1,7,2,16,1,52,70,131⟩ 3 104 t4569 t4601 k84_1_3 k84_1_4
private theorem k84_1_6 : check w84 pick84 1 t4603 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w84 pick84 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t4556 t4602 k84_1_2 k84_1_5
private theorem k84_1_7 : check w84 pick84 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k84_1_8 : check w84 pick84 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k84_1_9 : check w84 pick84 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w84 pick84 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k84_1_7 k84_1_8
private theorem k84_1_10 : check w84 pick84 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k84_1_11 : check w84 pick84 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w84 pick84 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k84_1_9 k84_1_10
private theorem k84_1_12 : check w84 pick84 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k84_1_13 : check w84 pick84 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k84_1_14 : check w84 pick84 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w84 pick84 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k84_1_12 k84_1_13
private theorem k84_1_15 : check w84 pick84 1 t4636 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w84 pick84 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t4179 k84_1_11 k84_1_14
private theorem k84_1_16 : check w84 pick84 1 t4637 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w84 pick84 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t4603 t4636 k84_1_6 k84_1_15
theorem cov84_1 : PA.Covered 1 (OZ.Valid 1 w84.low w84.t w84.y w84.r w84.cap) (P33.root 1) :=
  Night6836Tree.sound w84 pick84 1 t4637 _ k84_1_16
private theorem k84_2_0 : check w84 pick84 2 t4443 ⟨2,7,4,16,2,52,2,56⟩ = true := by decide +kernel
private theorem k84_2_1 : check w84 pick84 2 t4463 ⟨2,7,4,16,2,52,57,84⟩ = true := by decide +kernel
private theorem k84_2_2 : check w84 pick84 2 t4464 ⟨2,7,4,16,2,52,2,84⟩ = true := glue w84 pick84 2 ⟨2,7,4,16,2,52,2,84⟩ 3 56 t4443 t4463 k84_2_0 k84_2_1
private theorem k84_2_3 : check w84 pick84 2 t4479 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k84_2_4 : check w84 pick84 2 t4480 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w84 pick84 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4464 t4479 k84_2_2 k84_2_3
private theorem k84_2_5 : check w84 pick84 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k84_2_6 : check w84 pick84 2 t4648 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k84_2_7 : check w84 pick84 2 t4649 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w84 pick84 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t4648 k84_2_5 k84_2_6
private theorem k84_2_8 : check w84 pick84 2 t4650 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w84 pick84 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4480 t4649 k84_2_4 k84_2_7
theorem cov84_2 : PA.Covered 2 (OZ.Valid 2 w84.low w84.t w84.y w84.r w84.cap) (P33.root 2) :=
  Night6836Tree.sound w84 pick84 2 t4650 _ k84_2_8
theorem cov84_3 : PA.Covered 3 (OZ.Valid 3 w84.low w84.t w84.y w84.r w84.cap) (P33.root 3) :=
  Night6836Tree.sound w84 pick84 3 t4231 _ (by decide +kernel)
theorem cov84_4 : PA.Covered 4 (OZ.Valid 4 w84.low w84.t w84.y w84.r w84.cap) (P33.root 4) :=
  Night6836Tree.sound w84 pick84 4 t565 _ (by decide +kernel)
theorem cov84_5 : PA.Covered 5 (OZ.Valid 5 w84.low w84.t w84.y w84.r w84.cap) (P33.root 5) :=
  Night6836Tree.sound w84 pick84 5 t566 _ (by decide +kernel)
theorem cov84_6 : PA.Covered 6 (OZ.Valid 6 w84.low w84.t w84.y w84.r w84.cap) (P33.root 6) :=
  Night6836Tree.sound w84 pick84 6 t567 _ (by decide +kernel)
theorem cov84_7 : PA.Covered 7 (OZ.Valid 7 w84.low w84.t w84.y w84.r w84.cap) (P33.root 7) :=
  Night6836Tree.sound w84 pick84 7 t568 _ (by decide +kernel)
theorem window84 : P33.WindowCount w84 := by
  apply P33.window_count w84 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov84_1
  · exact cov84_2
  · exact cov84_3
  · exact cov84_4
  · exact cov84_5
  · exact cov84_6
  · exact cov84_7
def w85 : P33.Window := ⟨10,48,4455,3506,239477282090504241,63077,48000,5000000,81920000000⟩
def h85_0 : Height w85 := ⟨63077,48000,by decide +kernel⟩
def h85_1 : Height w85 := ⟨67066,45000,by decide +kernel⟩
def h85_2 : Height w85 := ⟨71589,42000,by decide +kernel⟩
def h85_3 : Height w85 := ⟨76835,39000,by decide +kernel⟩
def h85_4 : Height w85 := ⟨83101,36000,by decide +kernel⟩
def h85_5 : Height w85 := ⟨90866,33000,by decide +kernel⟩
def h85_6 : Height w85 := ⟨100967,30000,by decide +kernel⟩
def pick85 (cl : ℕ) : Height w85 := if cl<32 then (if cl<2 then (h85_0) else (if cl<6 then (h85_1) else (h85_2))) else (if cl<172 then (if cl<46 then (h85_3) else (h85_4)) else (if cl<531 then (h85_5) else (h85_6)))
private theorem k85_1_0 : check w85 pick85 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k85_1_1 : check w85 pick85 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k85_1_2 : check w85 pick85 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w85 pick85 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k85_1_0 k85_1_1
private theorem k85_1_3 : check w85 pick85 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k85_1_4 : check w85 pick85 1 t4252 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k85_1_5 : check w85 pick85 1 t4253 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w85 pick85 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t4252 k85_1_3 k85_1_4
private theorem k85_1_6 : check w85 pick85 1 t4254 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w85 pick85 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t4253 k85_1_2 k85_1_5
private theorem k85_1_7 : check w85 pick85 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k85_1_8 : check w85 pick85 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k85_1_9 : check w85 pick85 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w85 pick85 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k85_1_7 k85_1_8
private theorem k85_1_10 : check w85 pick85 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k85_1_11 : check w85 pick85 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k85_1_12 : check w85 pick85 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w85 pick85 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k85_1_10 k85_1_11
private theorem k85_1_13 : check w85 pick85 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w85 pick85 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k85_1_9 k85_1_12
private theorem k85_1_14 : check w85 pick85 1 t4651 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w85 pick85 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4254 t3549 k85_1_6 k85_1_13
theorem cov85_1 : PA.Covered 1 (OZ.Valid 1 w85.low w85.t w85.y w85.r w85.cap) (P33.root 1) :=
  Night6836Tree.sound w85 pick85 1 t4651 _ k85_1_14
theorem cov85_2 : PA.Covered 2 (OZ.Valid 2 w85.low w85.t w85.y w85.r w85.cap) (P33.root 2) :=
  Night6836Tree.sound w85 pick85 2 t4654 _ (by decide +kernel)
theorem cov85_3 : PA.Covered 3 (OZ.Valid 3 w85.low w85.t w85.y w85.r w85.cap) (P33.root 3) :=
  Night6836Tree.sound w85 pick85 3 t564 _ (by decide +kernel)
theorem cov85_4 : PA.Covered 4 (OZ.Valid 4 w85.low w85.t w85.y w85.r w85.cap) (P33.root 4) :=
  Night6836Tree.sound w85 pick85 4 t565 _ (by decide +kernel)
theorem cov85_5 : PA.Covered 5 (OZ.Valid 5 w85.low w85.t w85.y w85.r w85.cap) (P33.root 5) :=
  Night6836Tree.sound w85 pick85 5 t566 _ (by decide +kernel)
theorem cov85_6 : PA.Covered 6 (OZ.Valid 6 w85.low w85.t w85.y w85.r w85.cap) (P33.root 6) :=
  Night6836Tree.sound w85 pick85 6 t567 _ (by decide +kernel)
theorem cov85_7 : PA.Covered 7 (OZ.Valid 7 w85.low w85.t w85.y w85.r w85.cap) (P33.root 7) :=
  Night6836Tree.sound w85 pick85 7 t2134 _ (by decide +kernel)
theorem window85 : P33.WindowCount w85 := by
  apply P33.window_count w85 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov85_1
  · exact cov85_2
  · exact cov85_3
  · exact cov85_4
  · exact cov85_5
  · exact cov85_6
  · exact cov85_7
def w86 : P33.Window := ⟨10,48,6495,6406,247790981133889941,33664,27000,5000000,81920000000⟩
def h86_0 : Height w86 := ⟨33664,27000,by decide +kernel⟩
def h86_1 : Height w86 := ⟨37670,24000,by decide +kernel⟩
def h86_2 : Height w86 := ⟨42808,21000,by decide +kernel⟩
def h86_3 : Height w86 := ⟨50067,18000,by decide +kernel⟩
def h86_4 : Height w86 := ⟨62055,15000,by decide +kernel⟩
def pick86 (cl : ℕ) : Height w86 := if cl<17 then (if cl<2 then (h86_0) else (h86_1)) else (if cl<107 then (h86_2) else (if cl<922 then (h86_3) else (h86_4)))
private theorem k86_1_0 : check w86 pick86 1 t4544 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k86_1_1 : check w86 pick86 1 t4555 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k86_1_2 : check w86 pick86 1 t4556 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w86 pick86 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t4544 t4555 k86_1_0 k86_1_1
private theorem k86_1_3 : check w86 pick86 1 t4569 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k86_1_4 : check w86 pick86 1 t4659 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k86_1_5 : check w86 pick86 1 t4660 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w86 pick86 1 ⟨1,7,2,16,1,52,70,131⟩ 3 104 t4569 t4659 k86_1_3 k86_1_4
private theorem k86_1_6 : check w86 pick86 1 t4661 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w86 pick86 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t4556 t4660 k86_1_2 k86_1_5
private theorem k86_1_7 : check w86 pick86 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k86_1_8 : check w86 pick86 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k86_1_9 : check w86 pick86 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w86 pick86 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k86_1_7 k86_1_8
private theorem k86_1_10 : check w86 pick86 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k86_1_11 : check w86 pick86 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w86 pick86 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k86_1_9 k86_1_10
private theorem k86_1_12 : check w86 pick86 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k86_1_13 : check w86 pick86 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k86_1_14 : check w86 pick86 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w86 pick86 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k86_1_12 k86_1_13
private theorem k86_1_15 : check w86 pick86 1 t4636 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w86 pick86 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t4179 k86_1_11 k86_1_14
private theorem k86_1_16 : check w86 pick86 1 t4662 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w86 pick86 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t4661 t4636 k86_1_6 k86_1_15
theorem cov86_1 : PA.Covered 1 (OZ.Valid 1 w86.low w86.t w86.y w86.r w86.cap) (P33.root 1) :=
  Night6836Tree.sound w86 pick86 1 t4662 _ k86_1_16
private theorem k86_2_0 : check w86 pick86 2 t4688 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k86_2_1 : check w86 pick86 2 t4716 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k86_2_2 : check w86 pick86 2 t4717 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w86 pick86 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t4688 t4716 k86_2_0 k86_2_1
private theorem k86_2_3 : check w86 pick86 2 t4726 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k86_2_4 : check w86 pick86 2 t4729 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k86_2_5 : check w86 pick86 2 t4730 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w86 pick86 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4726 t4729 k86_2_3 k86_2_4
private theorem k86_2_6 : check w86 pick86 2 t4731 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w86 pick86 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4717 t4730 k86_2_2 k86_2_5
theorem cov86_2 : PA.Covered 2 (OZ.Valid 2 w86.low w86.t w86.y w86.r w86.cap) (P33.root 2) :=
  Night6836Tree.sound w86 pick86 2 t4731 _ k86_2_6
theorem cov86_3 : PA.Covered 3 (OZ.Valid 3 w86.low w86.t w86.y w86.r w86.cap) (P33.root 3) :=
  Night6836Tree.sound w86 pick86 3 t4231 _ (by decide +kernel)
theorem cov86_4 : PA.Covered 4 (OZ.Valid 4 w86.low w86.t w86.y w86.r w86.cap) (P33.root 4) :=
  Night6836Tree.sound w86 pick86 4 t565 _ (by decide +kernel)
theorem cov86_5 : PA.Covered 5 (OZ.Valid 5 w86.low w86.t w86.y w86.r w86.cap) (P33.root 5) :=
  Night6836Tree.sound w86 pick86 5 t566 _ (by decide +kernel)
theorem cov86_6 : PA.Covered 6 (OZ.Valid 6 w86.low w86.t w86.y w86.r w86.cap) (P33.root 6) :=
  Night6836Tree.sound w86 pick86 6 t567 _ (by decide +kernel)
theorem cov86_7 : PA.Covered 7 (OZ.Valid 7 w86.low w86.t w86.y w86.r w86.cap) (P33.root 7) :=
  Night6836Tree.sound w86 pick86 7 t568 _ (by decide +kernel)
theorem window86 : P33.WindowCount w86 := by
  apply P33.window_count w86 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov86_1
  · exact cov86_2
  · exact cov86_3
  · exact cov86_4
  · exact cov86_5
  · exact cov86_6
  · exact cov86_7
def w87 : P33.Window := ⟨10,49,6405,6213,247651454017635001,36888,27000,5000000,81920000000⟩
def h87_0 : Height w87 := ⟨36888,27000,by decide +kernel⟩
def h87_1 : Height w87 := ⟨41188,24000,by decide +kernel⟩
def h87_2 : Height w87 := ⟨46775,21000,by decide +kernel⟩
def h87_3 : Height w87 := ⟨54800,18000,by decide +kernel⟩
def h87_4 : Height w87 := ⟨68358,15000,by decide +kernel⟩
def pick87 (cl : ℕ) : Height w87 := if cl<26 then (if cl<4 then (h87_0) else (h87_1)) else (if cl<186 then (h87_2) else (if cl<961 then (h87_3) else (h87_4)))
private theorem k87_1_0 : check w87 pick87 1 t4290 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k87_1_1 : check w87 pick87 1 t4737 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k87_1_2 : check w87 pick87 1 t4738 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w87 pick87 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t4290 t4737 k87_1_0 k87_1_1
private theorem k87_1_3 : check w87 pick87 1 t4569 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k87_1_4 : check w87 pick87 1 t4745 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k87_1_5 : check w87 pick87 1 t4746 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w87 pick87 1 ⟨1,7,2,16,1,52,70,131⟩ 3 104 t4569 t4745 k87_1_3 k87_1_4
private theorem k87_1_6 : check w87 pick87 1 t4747 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w87 pick87 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t4738 t4746 k87_1_2 k87_1_5
private theorem k87_1_7 : check w87 pick87 1 t4754 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k87_1_8 : check w87 pick87 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k87_1_9 : check w87 pick87 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k87_1_10 : check w87 pick87 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w87 pick87 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k87_1_8 k87_1_9
private theorem k87_1_11 : check w87 pick87 1 t4755 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w87 pick87 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t4754 t4432 k87_1_7 k87_1_10
private theorem k87_1_12 : check w87 pick87 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k87_1_13 : check w87 pick87 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k87_1_14 : check w87 pick87 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w87 pick87 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k87_1_12 k87_1_13
private theorem k87_1_15 : check w87 pick87 1 t4756 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w87 pick87 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4755 t4179 k87_1_11 k87_1_14
private theorem k87_1_16 : check w87 pick87 1 t4757 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w87 pick87 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t4747 t4756 k87_1_6 k87_1_15
theorem cov87_1 : PA.Covered 1 (OZ.Valid 1 w87.low w87.t w87.y w87.r w87.cap) (P33.root 1) :=
  Night6836Tree.sound w87 pick87 1 t4757 _ k87_1_16
private theorem k87_2_0 : check w87 pick87 2 t4688 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k87_2_1 : check w87 pick87 2 t4716 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k87_2_2 : check w87 pick87 2 t4717 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w87 pick87 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t4688 t4716 k87_2_0 k87_2_1
private theorem k87_2_3 : check w87 pick87 2 t4777 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k87_2_4 : check w87 pick87 2 t4793 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k87_2_5 : check w87 pick87 2 t4794 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w87 pick87 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4777 t4793 k87_2_3 k87_2_4
private theorem k87_2_6 : check w87 pick87 2 t4795 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w87 pick87 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4717 t4794 k87_2_2 k87_2_5
theorem cov87_2 : PA.Covered 2 (OZ.Valid 2 w87.low w87.t w87.y w87.r w87.cap) (P33.root 2) :=
  Night6836Tree.sound w87 pick87 2 t4795 _ k87_2_6
theorem cov87_3 : PA.Covered 3 (OZ.Valid 3 w87.low w87.t w87.y w87.r w87.cap) (P33.root 3) :=
  Night6836Tree.sound w87 pick87 3 t4800 _ (by decide +kernel)
theorem cov87_4 : PA.Covered 4 (OZ.Valid 4 w87.low w87.t w87.y w87.r w87.cap) (P33.root 4) :=
  Night6836Tree.sound w87 pick87 4 t565 _ (by decide +kernel)
theorem cov87_5 : PA.Covered 5 (OZ.Valid 5 w87.low w87.t w87.y w87.r w87.cap) (P33.root 5) :=
  Night6836Tree.sound w87 pick87 5 t566 _ (by decide +kernel)
theorem cov87_6 : PA.Covered 6 (OZ.Valid 6 w87.low w87.t w87.y w87.r w87.cap) (P33.root 6) :=
  Night6836Tree.sound w87 pick87 6 t567 _ (by decide +kernel)
theorem cov87_7 : PA.Covered 7 (OZ.Valid 7 w87.low w87.t w87.y w87.r w87.cap) (P33.root 7) :=
  Night6836Tree.sound w87 pick87 7 t2134 _ (by decide +kernel)
theorem window87 : P33.WindowCount w87 := by
  apply P33.window_count w87 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov87_1
  · exact cov87_2
  · exact cov87_3
  · exact cov87_4
  · exact cov87_5
  · exact cov87_6
  · exact cov87_7
def w88 : P33.Window := ⟨10,50,6212,5348,246998044448229934,46024,30000,5000000,81920000000⟩
def h88_0 : Height w88 := ⟨46024,30000,by decide +kernel⟩
def h88_1 : Height w88 := ⟨50721,27000,by decide +kernel⟩
def h88_2 : Height w88 := ⟨56715,24000,by decide +kernel⟩
def h88_3 : Height w88 := ⟨64995,21000,by decide +kernel⟩
def h88_4 : Height w88 := ⟨77886,18000,by decide +kernel⟩
def pick88 (cl : ℕ) : Height w88 := if cl<37 then (if cl<10 then (h88_0) else (h88_1)) else (if cl<210 then (h88_2) else (if cl<947 then (h88_3) else (h88_4)))
private theorem k88_1_0 : check w88 pick88 1 t4290 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k88_1_1 : check w88 pick88 1 t4810 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k88_1_2 : check w88 pick88 1 t4811 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w88 pick88 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t4290 t4810 k88_1_0 k88_1_1
private theorem k88_1_3 : check w88 pick88 1 t4829 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k88_1_4 : check w88 pick88 1 t4837 ⟨1,7,2,16,1,52,98,124⟩ = true := by decide +kernel
private theorem k88_1_5 : check w88 pick88 1 t4838 ⟨1,7,2,16,1,52,70,124⟩ = true := glue w88 pick88 1 ⟨1,7,2,16,1,52,70,124⟩ 3 97 t4829 t4837 k88_1_3 k88_1_4
private theorem k88_1_6 : check w88 pick88 1 t4839 ⟨1,7,2,16,1,52,1,124⟩ = true := glue w88 pick88 1 ⟨1,7,2,16,1,52,1,124⟩ 3 69 t4811 t4838 k88_1_2 k88_1_5
private theorem k88_1_7 : check w88 pick88 1 t4846 ⟨1,7,2,16,1,52,125,159⟩ = true := by decide +kernel
private theorem k88_1_8 : check w88 pick88 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k88_1_9 : check w88 pick88 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k88_1_10 : check w88 pick88 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w88 pick88 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k88_1_8 k88_1_9
private theorem k88_1_11 : check w88 pick88 1 t4847 ⟨1,7,2,16,1,52,125,192⟩ = true := glue w88 pick88 1 ⟨1,7,2,16,1,52,125,192⟩ 3 159 t4846 t4432 k88_1_7 k88_1_10
private theorem k88_1_12 : check w88 pick88 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k88_1_13 : check w88 pick88 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k88_1_14 : check w88 pick88 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w88 pick88 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k88_1_12 k88_1_13
private theorem k88_1_15 : check w88 pick88 1 t4848 ⟨1,7,2,16,1,52,125,450⟩ = true := glue w88 pick88 1 ⟨1,7,2,16,1,52,125,450⟩ 3 192 t4847 t4179 k88_1_11 k88_1_14
private theorem k88_1_16 : check w88 pick88 1 t4849 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w88 pick88 1 ⟨1,7,2,16,0,52,0,450⟩ 3 124 t4839 t4848 k88_1_6 k88_1_15
theorem cov88_1 : PA.Covered 1 (OZ.Valid 1 w88.low w88.t w88.y w88.r w88.cap) (P33.root 1) :=
  Night6836Tree.sound w88 pick88 1 t4849 _ k88_1_16
private theorem k88_2_0 : check w88 pick88 2 t4688 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k88_2_1 : check w88 pick88 2 t4716 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k88_2_2 : check w88 pick88 2 t4717 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w88 pick88 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t4688 t4716 k88_2_0 k88_2_1
private theorem k88_2_3 : check w88 pick88 2 t4857 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k88_2_4 : check w88 pick88 2 t4871 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k88_2_5 : check w88 pick88 2 t4872 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w88 pick88 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4857 t4871 k88_2_3 k88_2_4
private theorem k88_2_6 : check w88 pick88 2 t4873 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w88 pick88 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4717 t4872 k88_2_2 k88_2_5
theorem cov88_2 : PA.Covered 2 (OZ.Valid 2 w88.low w88.t w88.y w88.r w88.cap) (P33.root 2) :=
  Night6836Tree.sound w88 pick88 2 t4873 _ k88_2_6
theorem cov88_3 : PA.Covered 3 (OZ.Valid 3 w88.low w88.t w88.y w88.r w88.cap) (P33.root 3) :=
  Night6836Tree.sound w88 pick88 3 t4877 _ (by decide +kernel)
theorem cov88_4 : PA.Covered 4 (OZ.Valid 4 w88.low w88.t w88.y w88.r w88.cap) (P33.root 4) :=
  Night6836Tree.sound w88 pick88 4 t565 _ (by decide +kernel)
theorem cov88_5 : PA.Covered 5 (OZ.Valid 5 w88.low w88.t w88.y w88.r w88.cap) (P33.root 5) :=
  Night6836Tree.sound w88 pick88 5 t566 _ (by decide +kernel)
theorem cov88_6 : PA.Covered 6 (OZ.Valid 6 w88.low w88.t w88.y w88.r w88.cap) (P33.root 6) :=
  Night6836Tree.sound w88 pick88 6 t567 _ (by decide +kernel)
theorem cov88_7 : PA.Covered 7 (OZ.Valid 7 w88.low w88.t w88.y w88.r w88.cap) (P33.root 7) :=
  Night6836Tree.sound w88 pick88 7 t2134 _ (by decide +kernel)
theorem window88 : P33.WindowCount w88 := by
  apply P33.window_count w88 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov88_1
  · exact cov88_2
  · exact cov88_3
  · exact cov88_4
  · exact cov88_5
  · exact cov88_6
  · exact cov88_7
def w89 : P33.Window := ⟨10,51,5347,4398,245064641086902823,54194,39000,5000000,81920000000⟩
def h89_0 : Height w89 := ⟨54194,39000,by decide +kernel⟩
def h89_1 : Height w89 := ⟨58278,36000,by decide +kernel⟩
def h89_2 : Height w89 := ⟨63074,33000,by decide +kernel⟩
def h89_3 : Height w89 := ⟨68919,30000,by decide +kernel⟩
def h89_4 : Height w89 := ⟨76409,27000,by decide +kernel⟩
def h89_5 : Height w89 := ⟨86691,24000,by decide +kernel⟩
def h89_6 : Height w89 := ⟨102294,21000,by decide +kernel⟩
def pick89 (cl : ℕ) : Height w89 := if cl<34 then (if cl<2 then (h89_0) else (if cl<10 then (h89_1) else (h89_2))) else (if cl<615 then (if cl<135 then (h89_3) else (h89_4)) else (if cl<1016 then (h89_5) else (h89_6)))
private theorem k89_1_0 : check w89 pick89 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k89_1_1 : check w89 pick89 1 t4881 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k89_1_2 : check w89 pick89 1 t4882 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w89 pick89 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t3666 t4881 k89_1_0 k89_1_1
private theorem k89_1_3 : check w89 pick89 1 t3808 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k89_1_4 : check w89 pick89 1 t4890 ⟨1,7,2,16,1,52,111,131⟩ = true := by decide +kernel
private theorem k89_1_5 : check w89 pick89 1 t4891 ⟨1,7,2,16,1,52,84,131⟩ = true := glue w89 pick89 1 ⟨1,7,2,16,1,52,84,131⟩ 3 110 t3808 t4890 k89_1_3 k89_1_4
private theorem k89_1_6 : check w89 pick89 1 t4892 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w89 pick89 1 ⟨1,7,2,16,1,52,1,131⟩ 3 83 t4882 t4891 k89_1_2 k89_1_5
private theorem k89_1_7 : check w89 pick89 1 t3836 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k89_1_8 : check w89 pick89 1 t3840 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k89_1_9 : check w89 pick89 1 t3841 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w89 pick89 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t3836 t3840 k89_1_7 k89_1_8
private theorem k89_1_10 : check w89 pick89 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k89_1_11 : check w89 pick89 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k89_1_12 : check w89 pick89 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w89 pick89 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k89_1_10 k89_1_11
private theorem k89_1_13 : check w89 pick89 1 t3842 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w89 pick89 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t3841 t3709 k89_1_9 k89_1_12
private theorem k89_1_14 : check w89 pick89 1 t4893 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w89 pick89 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t4892 t3842 k89_1_6 k89_1_13
theorem cov89_1 : PA.Covered 1 (OZ.Valid 1 w89.low w89.t w89.y w89.r w89.cap) (P33.root 1) :=
  Night6836Tree.sound w89 pick89 1 t4893 _ k89_1_14
private theorem k89_2_0 : check w89 pick89 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k89_2_1 : check w89 pick89 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k89_2_2 : check w89 pick89 2 t3778 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w89 pick89 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3777 k89_2_0 k89_2_1
private theorem k89_2_3 : check w89 pick89 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k89_2_4 : check w89 pick89 2 t4902 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k89_2_5 : check w89 pick89 2 t4903 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w89 pick89 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4902 k89_2_3 k89_2_4
private theorem k89_2_6 : check w89 pick89 2 t4904 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w89 pick89 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3778 t4903 k89_2_2 k89_2_5
theorem cov89_2 : PA.Covered 2 (OZ.Valid 2 w89.low w89.t w89.y w89.r w89.cap) (P33.root 2) :=
  Night6836Tree.sound w89 pick89 2 t4904 _ k89_2_6
theorem cov89_3 : PA.Covered 3 (OZ.Valid 3 w89.low w89.t w89.y w89.r w89.cap) (P33.root 3) :=
  Night6836Tree.sound w89 pick89 3 t564 _ (by decide +kernel)
theorem cov89_4 : PA.Covered 4 (OZ.Valid 4 w89.low w89.t w89.y w89.r w89.cap) (P33.root 4) :=
  Night6836Tree.sound w89 pick89 4 t565 _ (by decide +kernel)
theorem cov89_5 : PA.Covered 5 (OZ.Valid 5 w89.low w89.t w89.y w89.r w89.cap) (P33.root 5) :=
  Night6836Tree.sound w89 pick89 5 t566 _ (by decide +kernel)
theorem cov89_6 : PA.Covered 6 (OZ.Valid 6 w89.low w89.t w89.y w89.r w89.cap) (P33.root 6) :=
  Night6836Tree.sound w89 pick89 6 t567 _ (by decide +kernel)
theorem cov89_7 : PA.Covered 7 (OZ.Valid 7 w89.low w89.t w89.y w89.r w89.cap) (P33.root 7) :=
  Night6836Tree.sound w89 pick89 7 t2134 _ (by decide +kernel)
theorem window89 : P33.WindowCount w89 := by
  apply P33.window_count w89 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov89_1
  · exact cov89_2
  · exact cov89_3
  · exact cov89_4
  · exact cov89_5
  · exact cov89_6
  · exact cov89_7
end ProximityPrize.SubmissionLower.Night6836Bank
