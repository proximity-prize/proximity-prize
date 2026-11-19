/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT03
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w540 : P33.Window := ⟨9,29,7641,7605,243731956700218453,14986,18000,5000000,81920000000⟩
def h540_0 : Height w540 := ⟨14986,18000,by decide +kernel⟩
def h540_1 : Height w540 := ⟨19079,15000,by decide +kernel⟩
def h540_2 : Height w540 := ⟨25714,12000,by decide +kernel⟩
def h540_3 : Height w540 := ⟨42185,9000,by decide +kernel⟩
def pick540 (cl : ℕ) : Height w540 := if cl<70 then (if cl<2 then (h540_0) else (h540_1)) else (if cl<1021 then (h540_2) else (h540_3))
private theorem k540_1_0 : check w540 pick540 1 t10158 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k540_1_1 : check w540 pick540 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k540_1_2 : check w540 pick540 1 t10159 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w540 pick540 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10158 t9991 k540_1_0 k540_1_1
private theorem k540_1_3 : check w540 pick540 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k540_1_4 : check w540 pick540 1 t10160 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w540 pick540 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10159 t10023 k540_1_2 k540_1_3
private theorem k540_1_5 : check w540 pick540 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k540_1_6 : check w540 pick540 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k540_1_7 : check w540 pick540 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w540 pick540 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k540_1_5 k540_1_6
private theorem k540_1_8 : check w540 pick540 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k540_1_9 : check w540 pick540 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k540_1_10 : check w540 pick540 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w540 pick540 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k540_1_8 k540_1_9
private theorem k540_1_11 : check w540 pick540 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w540 pick540 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k540_1_7 k540_1_10
private theorem k540_1_12 : check w540 pick540 1 t10161 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w540 pick540 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10160 t10007 k540_1_4 k540_1_11
theorem cov540_1 : PA.Covered 1 (OZ.Valid 1 w540.low w540.t w540.y w540.r w540.cap) (P33.root 1) :=
  Night6836Tree.sound w540 pick540 1 t10161 _ k540_1_12
private theorem k540_2_0 : check w540 pick540 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k540_2_1 : check w540 pick540 2 t2922 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k540_2_2 : check w540 pick540 2 t2923 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w540 pick540 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t2922 k540_2_0 k540_2_1
theorem cov540_2 : PA.Covered 2 (OZ.Valid 2 w540.low w540.t w540.y w540.r w540.cap) (P33.root 2) :=
  Night6836Tree.sound w540 pick540 2 t2923 _ k540_2_2
theorem cov540_3 : PA.Covered 3 (OZ.Valid 3 w540.low w540.t w540.y w540.r w540.cap) (P33.root 3) :=
  Night6836Tree.sound w540 pick540 3 t564 _ (by decide +kernel)
theorem cov540_4 : PA.Covered 4 (OZ.Valid 4 w540.low w540.t w540.y w540.r w540.cap) (P33.root 4) :=
  Night6836Tree.sound w540 pick540 4 t565 _ (by decide +kernel)
theorem cov540_5 : PA.Covered 5 (OZ.Valid 5 w540.low w540.t w540.y w540.r w540.cap) (P33.root 5) :=
  Night6836Tree.sound w540 pick540 5 t566 _ (by decide +kernel)
theorem cov540_6 : PA.Covered 6 (OZ.Valid 6 w540.low w540.t w540.y w540.r w540.cap) (P33.root 6) :=
  Night6836Tree.sound w540 pick540 6 t567 _ (by decide +kernel)
theorem cov540_7 : PA.Covered 7 (OZ.Valid 7 w540.low w540.t w540.y w540.r w540.cap) (P33.root 7) :=
  Night6836Tree.sound w540 pick540 7 t568 _ (by decide +kernel)
theorem window540 : P33.WindowCount w540 := by
  apply P33.window_count w540 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov540_1
  · exact cov540_2
  · exact cov540_3
  · exact cov540_4
  · exact cov540_5
  · exact cov540_6
  · exact cov540_7
def w541 : P33.Window := ⟨9,30,5729,4730,196094644631607000,28079,27000,5000000,81920000000⟩
def h541_0 : Height w541 := ⟨28079,27000,by decide +kernel⟩
def h541_1 : Height w541 := ⟨34388,23000,by decide +kernel⟩
def h541_2 : Height w541 := ⟨44293,19000,by decide +kernel⟩
def pick541 (cl : ℕ) : Height w541 := if cl<10 then (h541_0) else (if cl<132 then (h541_1) else (h541_2))
private theorem k541_1_0 : check w541 pick541 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k541_1_1 : check w541 pick541 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k541_1_2 : check w541 pick541 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w541 pick541 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k541_1_0 k541_1_1
private theorem k541_1_3 : check w541 pick541 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k541_1_4 : check w541 pick541 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w541 pick541 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k541_1_2 k541_1_3
private theorem k541_1_5 : check w541 pick541 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k541_1_6 : check w541 pick541 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k541_1_7 : check w541 pick541 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w541 pick541 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k541_1_5 k541_1_6
private theorem k541_1_8 : check w541 pick541 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k541_1_9 : check w541 pick541 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k541_1_10 : check w541 pick541 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w541 pick541 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k541_1_8 k541_1_9
private theorem k541_1_11 : check w541 pick541 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w541 pick541 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k541_1_7 k541_1_10
private theorem k541_1_12 : check w541 pick541 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w541 pick541 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k541_1_4 k541_1_11
theorem cov541_1 : PA.Covered 1 (OZ.Valid 1 w541.low w541.t w541.y w541.r w541.cap) (P33.root 1) :=
  Night6836Tree.sound w541 pick541 1 t10025 _ k541_1_12
theorem cov541_2 : PA.Covered 2 (OZ.Valid 2 w541.low w541.t w541.y w541.r w541.cap) (P33.root 2) :=
  Night6836Tree.sound w541 pick541 2 t2745 _ (by decide +kernel)
theorem cov541_3 : PA.Covered 3 (OZ.Valid 3 w541.low w541.t w541.y w541.r w541.cap) (P33.root 3) :=
  Night6836Tree.sound w541 pick541 3 t564 _ (by decide +kernel)
theorem cov541_4 : PA.Covered 4 (OZ.Valid 4 w541.low w541.t w541.y w541.r w541.cap) (P33.root 4) :=
  Night6836Tree.sound w541 pick541 4 t565 _ (by decide +kernel)
theorem cov541_5 : PA.Covered 5 (OZ.Valid 5 w541.low w541.t w541.y w541.r w541.cap) (P33.root 5) :=
  Night6836Tree.sound w541 pick541 5 t566 _ (by decide +kernel)
theorem cov541_6 : PA.Covered 6 (OZ.Valid 6 w541.low w541.t w541.y w541.r w541.cap) (P33.root 6) :=
  Night6836Tree.sound w541 pick541 6 t567 _ (by decide +kernel)
theorem cov541_7 : PA.Covered 7 (OZ.Valid 7 w541.low w541.t w541.y w541.r w541.cap) (P33.root 7) :=
  Night6836Tree.sound w541 pick541 7 t2134 _ (by decide +kernel)
theorem window541 : P33.WindowCount w541 := by
  apply P33.window_count w541 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov541_1
  · exact cov541_2
  · exact cov541_3
  · exact cov541_4
  · exact cov541_5
  · exact cov541_6
  · exact cov541_7
def w542 : P33.Window := ⟨9,30,7247,6298,240933679779786366,20165,21000,5000000,81920000000⟩
def h542_0 : Height w542 := ⟨20165,21000,by decide +kernel⟩
def h542_1 : Height w542 := ⟨24532,18000,by decide +kernel⟩
def h542_2 : Height w542 := ⟨31073,15000,by decide +kernel⟩
def pick542 (cl : ℕ) : Height w542 := if cl<5 then (h542_0) else (if cl<62 then (h542_1) else (h542_2))
private theorem k542_1_0 : check w542 pick542 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k542_1_1 : check w542 pick542 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k542_1_2 : check w542 pick542 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w542 pick542 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k542_1_0 k542_1_1
private theorem k542_1_3 : check w542 pick542 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k542_1_4 : check w542 pick542 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w542 pick542 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k542_1_2 k542_1_3
private theorem k542_1_5 : check w542 pick542 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k542_1_6 : check w542 pick542 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k542_1_7 : check w542 pick542 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w542 pick542 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k542_1_5 k542_1_6
private theorem k542_1_8 : check w542 pick542 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k542_1_9 : check w542 pick542 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k542_1_10 : check w542 pick542 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w542 pick542 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k542_1_8 k542_1_9
private theorem k542_1_11 : check w542 pick542 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w542 pick542 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k542_1_7 k542_1_10
private theorem k542_1_12 : check w542 pick542 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w542 pick542 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k542_1_4 k542_1_11
theorem cov542_1 : PA.Covered 1 (OZ.Valid 1 w542.low w542.t w542.y w542.r w542.cap) (P33.root 1) :=
  Night6836Tree.sound w542 pick542 1 t10025 _ k542_1_12
private theorem k542_2_0 : check w542 pick542 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k542_2_1 : check w542 pick542 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k542_2_2 : check w542 pick542 2 t9544 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w542 pick542 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9135 k542_2_0 k542_2_1
theorem cov542_2 : PA.Covered 2 (OZ.Valid 2 w542.low w542.t w542.y w542.r w542.cap) (P33.root 2) :=
  Night6836Tree.sound w542 pick542 2 t9544 _ k542_2_2
theorem cov542_3 : PA.Covered 3 (OZ.Valid 3 w542.low w542.t w542.y w542.r w542.cap) (P33.root 3) :=
  Night6836Tree.sound w542 pick542 3 t564 _ (by decide +kernel)
theorem cov542_4 : PA.Covered 4 (OZ.Valid 4 w542.low w542.t w542.y w542.r w542.cap) (P33.root 4) :=
  Night6836Tree.sound w542 pick542 4 t565 _ (by decide +kernel)
theorem cov542_5 : PA.Covered 5 (OZ.Valid 5 w542.low w542.t w542.y w542.r w542.cap) (P33.root 5) :=
  Night6836Tree.sound w542 pick542 5 t566 _ (by decide +kernel)
theorem cov542_6 : PA.Covered 6 (OZ.Valid 6 w542.low w542.t w542.y w542.r w542.cap) (P33.root 6) :=
  Night6836Tree.sound w542 pick542 6 t567 _ (by decide +kernel)
theorem cov542_7 : PA.Covered 7 (OZ.Valid 7 w542.low w542.t w542.y w542.r w542.cap) (P33.root 7) :=
  Night6836Tree.sound w542 pick542 7 t568 _ (by decide +kernel)
theorem window542 : P33.WindowCount w542 := by
  apply P33.window_count w542 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov542_1
  · exact cov542_2
  · exact cov542_3
  · exact cov542_4
  · exact cov542_5
  · exact cov542_6
  · exact cov542_7
def w543 : P33.Window := ⟨9,30,7604,7567,244324762236322925,16151,18000,5000000,81920000000⟩
def h543_0 : Height w543 := ⟨16151,18000,by decide +kernel⟩
def h543_1 : Height w543 := ⟨20391,15000,by decide +kernel⟩
def h543_2 : Height w543 := ⟨27331,12000,by decide +kernel⟩
def pick543 (cl : ℕ) : Height w543 := if cl<4 then (h543_0) else (if cl<92 then (h543_1) else (h543_2))
private theorem k543_1_0 : check w543 pick543 1 t10158 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k543_1_1 : check w543 pick543 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k543_1_2 : check w543 pick543 1 t10159 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w543 pick543 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10158 t9991 k543_1_0 k543_1_1
private theorem k543_1_3 : check w543 pick543 1 t10963 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k543_1_4 : check w543 pick543 1 t10965 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k543_1_5 : check w543 pick543 1 t10966 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w543 pick543 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10963 t10965 k543_1_3 k543_1_4
private theorem k543_1_6 : check w543 pick543 1 t10967 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w543 pick543 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10159 t10966 k543_1_2 k543_1_5
private theorem k543_1_7 : check w543 pick543 1 t2839 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k543_1_8 : check w543 pick543 1 t2846 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k543_1_9 : check w543 pick543 1 t2847 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w543 pick543 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t2839 t2846 k543_1_7 k543_1_8
private theorem k543_1_10 : check w543 pick543 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k543_1_11 : check w543 pick543 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k543_1_12 : check w543 pick543 1 t10968 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w543 pick543 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t10005 k543_1_10 k543_1_11
private theorem k543_1_13 : check w543 pick543 1 t10969 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w543 pick543 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t2847 t10968 k543_1_9 k543_1_12
private theorem k543_1_14 : check w543 pick543 1 t10970 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w543 pick543 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10967 t10969 k543_1_6 k543_1_13
theorem cov543_1 : PA.Covered 1 (OZ.Valid 1 w543.low w543.t w543.y w543.r w543.cap) (P33.root 1) :=
  Night6836Tree.sound w543 pick543 1 t10970 _ k543_1_14
private theorem k543_2_0 : check w543 pick543 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k543_2_1 : check w543 pick543 2 t2922 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k543_2_2 : check w543 pick543 2 t2923 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w543 pick543 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t2922 k543_2_0 k543_2_1
theorem cov543_2 : PA.Covered 2 (OZ.Valid 2 w543.low w543.t w543.y w543.r w543.cap) (P33.root 2) :=
  Night6836Tree.sound w543 pick543 2 t2923 _ k543_2_2
theorem cov543_3 : PA.Covered 3 (OZ.Valid 3 w543.low w543.t w543.y w543.r w543.cap) (P33.root 3) :=
  Night6836Tree.sound w543 pick543 3 t564 _ (by decide +kernel)
theorem cov543_4 : PA.Covered 4 (OZ.Valid 4 w543.low w543.t w543.y w543.r w543.cap) (P33.root 4) :=
  Night6836Tree.sound w543 pick543 4 t565 _ (by decide +kernel)
theorem cov543_5 : PA.Covered 5 (OZ.Valid 5 w543.low w543.t w543.y w543.r w543.cap) (P33.root 5) :=
  Night6836Tree.sound w543 pick543 5 t566 _ (by decide +kernel)
theorem cov543_6 : PA.Covered 6 (OZ.Valid 6 w543.low w543.t w543.y w543.r w543.cap) (P33.root 6) :=
  Night6836Tree.sound w543 pick543 6 t567 _ (by decide +kernel)
theorem cov543_7 : PA.Covered 7 (OZ.Valid 7 w543.low w543.t w543.y w543.r w543.cap) (P33.root 7) :=
  Night6836Tree.sound w543 pick543 7 t568 _ (by decide +kernel)
theorem window543 : P33.WindowCount w543 := by
  apply P33.window_count w543 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov543_1
  · exact cov543_2
  · exact cov543_3
  · exact cov543_4
  · exact cov543_5
  · exact cov543_6
  · exact cov543_7
def w544 : P33.Window := ⟨9,31,5430,4431,190041248378438759,28932,31000,5000000,81920000000⟩
def h544_0 : Height w544 := ⟨28932,31000,by decide +kernel⟩
def h544_1 : Height w544 := ⟨34362,27000,by decide +kernel⟩
def h544_2 : Height w544 := ⟨41909,23000,by decide +kernel⟩
def h544_3 : Height w544 := ⟨54401,19000,by decide +kernel⟩
def pick544 (cl : ℕ) : Height w544 := if cl<32 then (if cl<2 then (h544_0) else (h544_1)) else (if cl<302 then (h544_2) else (h544_3))
private theorem k544_1_0 : check w544 pick544 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k544_1_1 : check w544 pick544 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k544_1_2 : check w544 pick544 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w544 pick544 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k544_1_0 k544_1_1
private theorem k544_1_3 : check w544 pick544 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k544_1_4 : check w544 pick544 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w544 pick544 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k544_1_2 k544_1_3
private theorem k544_1_5 : check w544 pick544 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k544_1_6 : check w544 pick544 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k544_1_7 : check w544 pick544 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w544 pick544 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k544_1_5 k544_1_6
private theorem k544_1_8 : check w544 pick544 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k544_1_9 : check w544 pick544 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k544_1_10 : check w544 pick544 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w544 pick544 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k544_1_8 k544_1_9
private theorem k544_1_11 : check w544 pick544 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w544 pick544 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k544_1_7 k544_1_10
private theorem k544_1_12 : check w544 pick544 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w544 pick544 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k544_1_4 k544_1_11
theorem cov544_1 : PA.Covered 1 (OZ.Valid 1 w544.low w544.t w544.y w544.r w544.cap) (P33.root 1) :=
  Night6836Tree.sound w544 pick544 1 t10025 _ k544_1_12
theorem cov544_2 : PA.Covered 2 (OZ.Valid 2 w544.low w544.t w544.y w544.r w544.cap) (P33.root 2) :=
  Night6836Tree.sound w544 pick544 2 t2745 _ (by decide +kernel)
theorem cov544_3 : PA.Covered 3 (OZ.Valid 3 w544.low w544.t w544.y w544.r w544.cap) (P33.root 3) :=
  Night6836Tree.sound w544 pick544 3 t564 _ (by decide +kernel)
theorem cov544_4 : PA.Covered 4 (OZ.Valid 4 w544.low w544.t w544.y w544.r w544.cap) (P33.root 4) :=
  Night6836Tree.sound w544 pick544 4 t565 _ (by decide +kernel)
theorem cov544_5 : PA.Covered 5 (OZ.Valid 5 w544.low w544.t w544.y w544.r w544.cap) (P33.root 5) :=
  Night6836Tree.sound w544 pick544 5 t566 _ (by decide +kernel)
theorem cov544_6 : PA.Covered 6 (OZ.Valid 6 w544.low w544.t w544.y w544.r w544.cap) (P33.root 6) :=
  Night6836Tree.sound w544 pick544 6 t567 _ (by decide +kernel)
theorem cov544_7 : PA.Covered 7 (OZ.Valid 7 w544.low w544.t w544.y w544.r w544.cap) (P33.root 7) :=
  Night6836Tree.sound w544 pick544 7 t2134 _ (by decide +kernel)
theorem window544 : P33.WindowCount w544 := by
  apply P33.window_count w544 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov544_1
  · exact cov544_2
  · exact cov544_3
  · exact cov544_4
  · exact cov544_5
  · exact cov544_6
  · exact cov544_7
def w545 : P33.Window := ⟨9,31,7566,7529,236698255015477292,17333,18000,5000000,81920000000⟩
def h545_0 : Height w545 := ⟨17333,18000,by decide +kernel⟩
def h545_1 : Height w545 := ⟨21726,15000,by decide +kernel⟩
def h545_2 : Height w545 := ⟨28980,12000,by decide +kernel⟩
def pick545 (cl : ℕ) : Height w545 := if cl<5 then (h545_0) else (if cl<107 then (h545_1) else (h545_2))
private theorem k545_1_0 : check w545 pick545 1 t3036 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k545_1_1 : check w545 pick545 1 t9864 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k545_1_2 : check w545 pick545 1 t9865 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w545 pick545 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3036 t9864 k545_1_0 k545_1_1
private theorem k545_1_3 : check w545 pick545 1 t10973 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k545_1_4 : check w545 pick545 1 t10976 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k545_1_5 : check w545 pick545 1 t10977 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w545 pick545 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10973 t10976 k545_1_3 k545_1_4
private theorem k545_1_6 : check w545 pick545 1 t10978 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w545 pick545 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t9865 t10977 k545_1_2 k545_1_5
private theorem k545_1_7 : check w545 pick545 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k545_1_8 : check w545 pick545 1 t9910 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k545_1_9 : check w545 pick545 1 t9911 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w545 pick545 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t9910 k545_1_7 k545_1_8
private theorem k545_1_10 : check w545 pick545 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k545_1_11 : check w545 pick545 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k545_1_12 : check w545 pick545 1 t10968 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w545 pick545 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t10005 k545_1_10 k545_1_11
private theorem k545_1_13 : check w545 pick545 1 t10979 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w545 pick545 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t9911 t10968 k545_1_9 k545_1_12
private theorem k545_1_14 : check w545 pick545 1 t10980 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w545 pick545 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10978 t10979 k545_1_6 k545_1_13
theorem cov545_1 : PA.Covered 1 (OZ.Valid 1 w545.low w545.t w545.y w545.r w545.cap) (P33.root 1) :=
  Night6836Tree.sound w545 pick545 1 t10980 _ k545_1_14
private theorem k545_2_0 : check w545 pick545 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k545_2_1 : check w545 pick545 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k545_2_2 : check w545 pick545 2 t3059 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w545 pick545 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t3026 k545_2_0 k545_2_1
theorem cov545_2 : PA.Covered 2 (OZ.Valid 2 w545.low w545.t w545.y w545.r w545.cap) (P33.root 2) :=
  Night6836Tree.sound w545 pick545 2 t3059 _ k545_2_2
theorem cov545_3 : PA.Covered 3 (OZ.Valid 3 w545.low w545.t w545.y w545.r w545.cap) (P33.root 3) :=
  Night6836Tree.sound w545 pick545 3 t564 _ (by decide +kernel)
theorem cov545_4 : PA.Covered 4 (OZ.Valid 4 w545.low w545.t w545.y w545.r w545.cap) (P33.root 4) :=
  Night6836Tree.sound w545 pick545 4 t565 _ (by decide +kernel)
theorem cov545_5 : PA.Covered 5 (OZ.Valid 5 w545.low w545.t w545.y w545.r w545.cap) (P33.root 5) :=
  Night6836Tree.sound w545 pick545 5 t566 _ (by decide +kernel)
theorem cov545_6 : PA.Covered 6 (OZ.Valid 6 w545.low w545.t w545.y w545.r w545.cap) (P33.root 6) :=
  Night6836Tree.sound w545 pick545 6 t567 _ (by decide +kernel)
theorem cov545_7 : PA.Covered 7 (OZ.Valid 7 w545.low w545.t w545.y w545.r w545.cap) (P33.root 7) :=
  Night6836Tree.sound w545 pick545 7 t568 _ (by decide +kernel)
theorem window545 : P33.WindowCount w545 := by
  apply P33.window_count w545 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov545_1
  · exact cov545_2
  · exact cov545_3
  · exact cov545_4
  · exact cov545_5
  · exact cov545_6
  · exact cov545_7
def w546 : P33.Window := ⟨9,32,5431,4432,194225245307029587,30590,31000,5000000,81920000000⟩
def h546_0 : Height w546 := ⟨30590,31000,by decide +kernel⟩
def h546_1 : Height w546 := ⟨36145,27000,by decide +kernel⟩
def h546_2 : Height w546 := ⟨43893,23000,by decide +kernel⟩
def h546_3 : Height w546 := ⟨56763,19000,by decide +kernel⟩
def pick546 (cl : ℕ) : Height w546 := if cl<32 then (if cl<4 then (h546_0) else (h546_1)) else (if cl<347 then (h546_2) else (h546_3))
private theorem k546_1_0 : check w546 pick546 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k546_1_1 : check w546 pick546 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k546_1_2 : check w546 pick546 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w546 pick546 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k546_1_0 k546_1_1
private theorem k546_1_3 : check w546 pick546 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k546_1_4 : check w546 pick546 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w546 pick546 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k546_1_2 k546_1_3
private theorem k546_1_5 : check w546 pick546 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k546_1_6 : check w546 pick546 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k546_1_7 : check w546 pick546 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w546 pick546 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k546_1_5 k546_1_6
private theorem k546_1_8 : check w546 pick546 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k546_1_9 : check w546 pick546 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k546_1_10 : check w546 pick546 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w546 pick546 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k546_1_8 k546_1_9
private theorem k546_1_11 : check w546 pick546 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w546 pick546 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k546_1_7 k546_1_10
private theorem k546_1_12 : check w546 pick546 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w546 pick546 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k546_1_4 k546_1_11
theorem cov546_1 : PA.Covered 1 (OZ.Valid 1 w546.low w546.t w546.y w546.r w546.cap) (P33.root 1) :=
  Night6836Tree.sound w546 pick546 1 t10025 _ k546_1_12
theorem cov546_2 : PA.Covered 2 (OZ.Valid 2 w546.low w546.t w546.y w546.r w546.cap) (P33.root 2) :=
  Night6836Tree.sound w546 pick546 2 t2745 _ (by decide +kernel)
theorem cov546_3 : PA.Covered 3 (OZ.Valid 3 w546.low w546.t w546.y w546.r w546.cap) (P33.root 3) :=
  Night6836Tree.sound w546 pick546 3 t564 _ (by decide +kernel)
theorem cov546_4 : PA.Covered 4 (OZ.Valid 4 w546.low w546.t w546.y w546.r w546.cap) (P33.root 4) :=
  Night6836Tree.sound w546 pick546 4 t565 _ (by decide +kernel)
theorem cov546_5 : PA.Covered 5 (OZ.Valid 5 w546.low w546.t w546.y w546.r w546.cap) (P33.root 5) :=
  Night6836Tree.sound w546 pick546 5 t566 _ (by decide +kernel)
theorem cov546_6 : PA.Covered 6 (OZ.Valid 6 w546.low w546.t w546.y w546.r w546.cap) (P33.root 6) :=
  Night6836Tree.sound w546 pick546 6 t567 _ (by decide +kernel)
theorem cov546_7 : PA.Covered 7 (OZ.Valid 7 w546.low w546.t w546.y w546.r w546.cap) (P33.root 7) :=
  Night6836Tree.sound w546 pick546 7 t2134 _ (by decide +kernel)
theorem window546 : P33.WindowCount w546 := by
  apply P33.window_count w546 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov546_1
  · exact cov546_2
  · exact cov546_3
  · exact cov546_4
  · exact cov546_5
  · exact cov546_6
  · exact cov546_7
def w547 : P33.Window := ⟨9,32,7247,6298,243912989104854152,22566,21000,5000000,81920000000⟩
def h547_0 : Height w547 := ⟨22566,21000,by decide +kernel⟩
def h547_1 : Height w547 := ⟨27156,18000,by decide +kernel⟩
def h547_2 : Height w547 := ⟨34087,15000,by decide +kernel⟩
def h547_3 : Height w547 := ⟨47631,12000,by decide +kernel⟩
def pick547 (cl : ℕ) : Height w547 := if cl<92 then (if cl<6 then (h547_0) else (h547_1)) else (if cl<961 then (h547_2) else (h547_3))
private theorem k547_1_0 : check w547 pick547 1 t10158 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k547_1_1 : check w547 pick547 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k547_1_2 : check w547 pick547 1 t10159 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w547 pick547 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10158 t9991 k547_1_0 k547_1_1
private theorem k547_1_3 : check w547 pick547 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k547_1_4 : check w547 pick547 1 t10160 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w547 pick547 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10159 t10023 k547_1_2 k547_1_3
private theorem k547_1_5 : check w547 pick547 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k547_1_6 : check w547 pick547 1 t10981 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k547_1_7 : check w547 pick547 1 t10982 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w547 pick547 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t10981 k547_1_5 k547_1_6
private theorem k547_1_8 : check w547 pick547 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k547_1_9 : check w547 pick547 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k547_1_10 : check w547 pick547 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w547 pick547 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k547_1_8 k547_1_9
private theorem k547_1_11 : check w547 pick547 1 t10983 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w547 pick547 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t10982 t10006 k547_1_7 k547_1_10
private theorem k547_1_12 : check w547 pick547 1 t10984 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w547 pick547 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10160 t10983 k547_1_4 k547_1_11
theorem cov547_1 : PA.Covered 1 (OZ.Valid 1 w547.low w547.t w547.y w547.r w547.cap) (P33.root 1) :=
  Night6836Tree.sound w547 pick547 1 t10984 _ k547_1_12
private theorem k547_2_0 : check w547 pick547 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k547_2_1 : check w547 pick547 2 t2922 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k547_2_2 : check w547 pick547 2 t2923 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w547 pick547 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t2922 k547_2_0 k547_2_1
theorem cov547_2 : PA.Covered 2 (OZ.Valid 2 w547.low w547.t w547.y w547.r w547.cap) (P33.root 2) :=
  Night6836Tree.sound w547 pick547 2 t2923 _ k547_2_2
theorem cov547_3 : PA.Covered 3 (OZ.Valid 3 w547.low w547.t w547.y w547.r w547.cap) (P33.root 3) :=
  Night6836Tree.sound w547 pick547 3 t564 _ (by decide +kernel)
theorem cov547_4 : PA.Covered 4 (OZ.Valid 4 w547.low w547.t w547.y w547.r w547.cap) (P33.root 4) :=
  Night6836Tree.sound w547 pick547 4 t565 _ (by decide +kernel)
theorem cov547_5 : PA.Covered 5 (OZ.Valid 5 w547.low w547.t w547.y w547.r w547.cap) (P33.root 5) :=
  Night6836Tree.sound w547 pick547 5 t566 _ (by decide +kernel)
theorem cov547_6 : PA.Covered 6 (OZ.Valid 6 w547.low w547.t w547.y w547.r w547.cap) (P33.root 6) :=
  Night6836Tree.sound w547 pick547 6 t567 _ (by decide +kernel)
theorem cov547_7 : PA.Covered 7 (OZ.Valid 7 w547.low w547.t w547.y w547.r w547.cap) (P33.root 7) :=
  Night6836Tree.sound w547 pick547 7 t568 _ (by decide +kernel)
theorem window547 : P33.WindowCount w547 := by
  apply P33.window_count w547 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov547_1
  · exact cov547_2
  · exact cov547_3
  · exact cov547_4
  · exact cov547_5
  · exact cov547_6
  · exact cov547_7
def w548 : P33.Window := ⟨9,32,7528,7404,241980438660942713,19021,18000,5000000,81920000000⟩
def h548_0 : Height w548 := ⟨19021,18000,by decide +kernel⟩
def h548_1 : Height w548 := ⟨23684,15000,by decide +kernel⟩
def h548_2 : Height w548 := ⟨31529,12000,by decide +kernel⟩
def pick548 (cl : ℕ) : Height w548 := if cl<6 then (h548_0) else (if cl<170 then (h548_1) else (h548_2))
private theorem k548_1_0 : check w548 pick548 1 t3036 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k548_1_1 : check w548 pick548 1 t9864 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k548_1_2 : check w548 pick548 1 t9865 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w548 pick548 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3036 t9864 k548_1_0 k548_1_1
private theorem k548_1_3 : check w548 pick548 1 t10973 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k548_1_4 : check w548 pick548 1 t10976 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k548_1_5 : check w548 pick548 1 t10977 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w548 pick548 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10973 t10976 k548_1_3 k548_1_4
private theorem k548_1_6 : check w548 pick548 1 t10978 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w548 pick548 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t9865 t10977 k548_1_2 k548_1_5
private theorem k548_1_7 : check w548 pick548 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k548_1_8 : check w548 pick548 1 t9910 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k548_1_9 : check w548 pick548 1 t9911 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w548 pick548 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t9910 k548_1_7 k548_1_8
private theorem k548_1_10 : check w548 pick548 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k548_1_11 : check w548 pick548 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k548_1_12 : check w548 pick548 1 t10968 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w548 pick548 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t10005 k548_1_10 k548_1_11
private theorem k548_1_13 : check w548 pick548 1 t10979 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w548 pick548 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t9911 t10968 k548_1_9 k548_1_12
private theorem k548_1_14 : check w548 pick548 1 t10980 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w548 pick548 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10978 t10979 k548_1_6 k548_1_13
theorem cov548_1 : PA.Covered 1 (OZ.Valid 1 w548.low w548.t w548.y w548.r w548.cap) (P33.root 1) :=
  Night6836Tree.sound w548 pick548 1 t10980 _ k548_1_14
private theorem k548_2_0 : check w548 pick548 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k548_2_1 : check w548 pick548 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k548_2_2 : check w548 pick548 2 t3059 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w548 pick548 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t3026 k548_2_0 k548_2_1
theorem cov548_2 : PA.Covered 2 (OZ.Valid 2 w548.low w548.t w548.y w548.r w548.cap) (P33.root 2) :=
  Night6836Tree.sound w548 pick548 2 t3059 _ k548_2_2
theorem cov548_3 : PA.Covered 3 (OZ.Valid 3 w548.low w548.t w548.y w548.r w548.cap) (P33.root 3) :=
  Night6836Tree.sound w548 pick548 3 t564 _ (by decide +kernel)
theorem cov548_4 : PA.Covered 4 (OZ.Valid 4 w548.low w548.t w548.y w548.r w548.cap) (P33.root 4) :=
  Night6836Tree.sound w548 pick548 4 t565 _ (by decide +kernel)
theorem cov548_5 : PA.Covered 5 (OZ.Valid 5 w548.low w548.t w548.y w548.r w548.cap) (P33.root 5) :=
  Night6836Tree.sound w548 pick548 5 t566 _ (by decide +kernel)
theorem cov548_6 : PA.Covered 6 (OZ.Valid 6 w548.low w548.t w548.y w548.r w548.cap) (P33.root 6) :=
  Night6836Tree.sound w548 pick548 6 t567 _ (by decide +kernel)
theorem cov548_7 : PA.Covered 7 (OZ.Valid 7 w548.low w548.t w548.y w548.r w548.cap) (P33.root 7) :=
  Night6836Tree.sound w548 pick548 7 t568 _ (by decide +kernel)
theorem window548 : P33.WindowCount w548 := by
  apply P33.window_count w548 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov548_1
  · exact cov548_2
  · exact cov548_3
  · exact cov548_4
  · exact cov548_5
  · exact cov548_6
  · exact cov548_7
def w549 : P33.Window := ⟨9,33,5432,4433,198410005818717924,32247,31000,5000000,81920000000⟩
def h549_0 : Height w549 := ⟨32247,31000,by decide +kernel⟩
def h549_1 : Height w549 := ⟨37926,27000,by decide +kernel⟩
def h549_2 : Height w549 := ⟨45876,23000,by decide +kernel⟩
def h549_3 : Height w549 := ⟨59121,19000,by decide +kernel⟩
def pick549 (cl : ℕ) : Height w549 := if cl<37 then (if cl<4 then (h549_0) else (h549_1)) else (if cl<465 then (h549_2) else (h549_3))
private theorem k549_1_0 : check w549 pick549 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k549_1_1 : check w549 pick549 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k549_1_2 : check w549 pick549 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w549 pick549 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k549_1_0 k549_1_1
private theorem k549_1_3 : check w549 pick549 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k549_1_4 : check w549 pick549 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w549 pick549 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k549_1_2 k549_1_3
private theorem k549_1_5 : check w549 pick549 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k549_1_6 : check w549 pick549 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k549_1_7 : check w549 pick549 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w549 pick549 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k549_1_5 k549_1_6
private theorem k549_1_8 : check w549 pick549 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k549_1_9 : check w549 pick549 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k549_1_10 : check w549 pick549 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w549 pick549 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k549_1_8 k549_1_9
private theorem k549_1_11 : check w549 pick549 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w549 pick549 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k549_1_7 k549_1_10
private theorem k549_1_12 : check w549 pick549 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w549 pick549 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k549_1_4 k549_1_11
theorem cov549_1 : PA.Covered 1 (OZ.Valid 1 w549.low w549.t w549.y w549.r w549.cap) (P33.root 1) :=
  Night6836Tree.sound w549 pick549 1 t10025 _ k549_1_12
theorem cov549_2 : PA.Covered 2 (OZ.Valid 2 w549.low w549.t w549.y w549.r w549.cap) (P33.root 2) :=
  Night6836Tree.sound w549 pick549 2 t4654 _ (by decide +kernel)
theorem cov549_3 : PA.Covered 3 (OZ.Valid 3 w549.low w549.t w549.y w549.r w549.cap) (P33.root 3) :=
  Night6836Tree.sound w549 pick549 3 t564 _ (by decide +kernel)
theorem cov549_4 : PA.Covered 4 (OZ.Valid 4 w549.low w549.t w549.y w549.r w549.cap) (P33.root 4) :=
  Night6836Tree.sound w549 pick549 4 t565 _ (by decide +kernel)
theorem cov549_5 : PA.Covered 5 (OZ.Valid 5 w549.low w549.t w549.y w549.r w549.cap) (P33.root 5) :=
  Night6836Tree.sound w549 pick549 5 t566 _ (by decide +kernel)
theorem cov549_6 : PA.Covered 6 (OZ.Valid 6 w549.low w549.t w549.y w549.r w549.cap) (P33.root 6) :=
  Night6836Tree.sound w549 pick549 6 t567 _ (by decide +kernel)
theorem cov549_7 : PA.Covered 7 (OZ.Valid 7 w549.low w549.t w549.y w549.r w549.cap) (P33.root 7) :=
  Night6836Tree.sound w549 pick549 7 t2134 _ (by decide +kernel)
theorem window549 : P33.WindowCount w549 := by
  apply P33.window_count w549 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov549_1
  · exact cov549_2
  · exact cov549_3
  · exact cov549_4
  · exact cov549_5
  · exact cov549_6
  · exact cov549_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w550 : P33.Window := ⟨9,33,7490,7448,244550642609175713,19781,18000,5000000,81920000000⟩
def h550_0 : Height w550 := ⟨19781,18000,by decide +kernel⟩
def h550_1 : Height w550 := ⟨24497,15000,by decide +kernel⟩
def h550_2 : Height w550 := ⟨32429,12000,by decide +kernel⟩
def pick550 (cl : ℕ) : Height w550 := if cl<10 then (h550_0) else (if cl<172 then (h550_1) else (h550_2))
private theorem k550_1_0 : check w550 pick550 1 t3067 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k550_1_1 : check w550 pick550 1 t10987 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k550_1_2 : check w550 pick550 1 t10988 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w550 pick550 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3067 t10987 k550_1_0 k550_1_1
private theorem k550_1_3 : check w550 pick550 1 t10973 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k550_1_4 : check w550 pick550 1 t10991 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k550_1_5 : check w550 pick550 1 t10992 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w550 pick550 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t10973 t10991 k550_1_3 k550_1_4
private theorem k550_1_6 : check w550 pick550 1 t10993 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w550 pick550 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t10988 t10992 k550_1_2 k550_1_5
private theorem k550_1_7 : check w550 pick550 1 t11007 ⟨1,7,2,16,1,20,139,199⟩ = true := by decide +kernel
private theorem k550_1_8 : check w550 pick550 1 t3099 ⟨1,7,2,16,21,52,139,199⟩ = true := by decide +kernel
private theorem k550_1_9 : check w550 pick550 1 t11008 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w550 pick550 1 ⟨1,7,2,16,1,52,139,199⟩ 2 20 t11007 t3099 k550_1_7 k550_1_8
private theorem k550_1_10 : check w550 pick550 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k550_1_11 : check w550 pick550 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k550_1_12 : check w550 pick550 1 t10502 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w550 pick550 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10064 k550_1_10 k550_1_11
private theorem k550_1_13 : check w550 pick550 1 t11009 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w550 pick550 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t11008 t10502 k550_1_9 k550_1_12
private theorem k550_1_14 : check w550 pick550 1 t11010 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w550 pick550 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10993 t11009 k550_1_6 k550_1_13
theorem cov550_1 : PA.Covered 1 (OZ.Valid 1 w550.low w550.t w550.y w550.r w550.cap) (P33.root 1) :=
  Night6836Tree.sound w550 pick550 1 t11010 _ k550_1_14
private theorem k550_2_0 : check w550 pick550 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k550_2_1 : check w550 pick550 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k550_2_2 : check w550 pick550 2 t3059 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w550 pick550 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t3026 k550_2_0 k550_2_1
theorem cov550_2 : PA.Covered 2 (OZ.Valid 2 w550.low w550.t w550.y w550.r w550.cap) (P33.root 2) :=
  Night6836Tree.sound w550 pick550 2 t3059 _ k550_2_2
theorem cov550_3 : PA.Covered 3 (OZ.Valid 3 w550.low w550.t w550.y w550.r w550.cap) (P33.root 3) :=
  Night6836Tree.sound w550 pick550 3 t564 _ (by decide +kernel)
theorem cov550_4 : PA.Covered 4 (OZ.Valid 4 w550.low w550.t w550.y w550.r w550.cap) (P33.root 4) :=
  Night6836Tree.sound w550 pick550 4 t565 _ (by decide +kernel)
theorem cov550_5 : PA.Covered 5 (OZ.Valid 5 w550.low w550.t w550.y w550.r w550.cap) (P33.root 5) :=
  Night6836Tree.sound w550 pick550 5 t566 _ (by decide +kernel)
theorem cov550_6 : PA.Covered 6 (OZ.Valid 6 w550.low w550.t w550.y w550.r w550.cap) (P33.root 6) :=
  Night6836Tree.sound w550 pick550 6 t567 _ (by decide +kernel)
theorem cov550_7 : PA.Covered 7 (OZ.Valid 7 w550.low w550.t w550.y w550.r w550.cap) (P33.root 7) :=
  Night6836Tree.sound w550 pick550 7 t568 _ (by decide +kernel)
theorem window550 : P33.WindowCount w550 := by
  apply P33.window_count w550 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov550_1
  · exact cov550_2
  · exact cov550_3
  · exact cov550_4
  · exact cov550_5
  · exact cov550_6
  · exact cov550_7
def w551 : P33.Window := ⟨9,34,5433,4434,202595529913503770,33902,31000,5000000,81920000000⟩
def h551_0 : Height w551 := ⟨33902,31000,by decide +kernel⟩
def h551_1 : Height w551 := ⟨39706,27000,by decide +kernel⟩
def h551_2 : Height w551 := ⟨47856,23000,by decide +kernel⟩
def h551_3 : Height w551 := ⟨61476,19000,by decide +kernel⟩
def pick551 (cl : ℕ) : Height w551 := if cl<43 then (if cl<5 then (h551_0) else (h551_1)) else (if cl<594 then (h551_2) else (h551_3))
private theorem k551_1_0 : check w551 pick551 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k551_1_1 : check w551 pick551 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k551_1_2 : check w551 pick551 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w551 pick551 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k551_1_0 k551_1_1
private theorem k551_1_3 : check w551 pick551 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k551_1_4 : check w551 pick551 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w551 pick551 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k551_1_2 k551_1_3
private theorem k551_1_5 : check w551 pick551 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k551_1_6 : check w551 pick551 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k551_1_7 : check w551 pick551 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w551 pick551 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k551_1_5 k551_1_6
private theorem k551_1_8 : check w551 pick551 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k551_1_9 : check w551 pick551 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k551_1_10 : check w551 pick551 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w551 pick551 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k551_1_8 k551_1_9
private theorem k551_1_11 : check w551 pick551 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w551 pick551 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k551_1_7 k551_1_10
private theorem k551_1_12 : check w551 pick551 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w551 pick551 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k551_1_4 k551_1_11
theorem cov551_1 : PA.Covered 1 (OZ.Valid 1 w551.low w551.t w551.y w551.r w551.cap) (P33.root 1) :=
  Night6836Tree.sound w551 pick551 1 t10025 _ k551_1_12
theorem cov551_2 : PA.Covered 2 (OZ.Valid 2 w551.low w551.t w551.y w551.r w551.cap) (P33.root 2) :=
  Night6836Tree.sound w551 pick551 2 t4654 _ (by decide +kernel)
theorem cov551_3 : PA.Covered 3 (OZ.Valid 3 w551.low w551.t w551.y w551.r w551.cap) (P33.root 3) :=
  Night6836Tree.sound w551 pick551 3 t564 _ (by decide +kernel)
theorem cov551_4 : PA.Covered 4 (OZ.Valid 4 w551.low w551.t w551.y w551.r w551.cap) (P33.root 4) :=
  Night6836Tree.sound w551 pick551 4 t565 _ (by decide +kernel)
theorem cov551_5 : PA.Covered 5 (OZ.Valid 5 w551.low w551.t w551.y w551.r w551.cap) (P33.root 5) :=
  Night6836Tree.sound w551 pick551 5 t566 _ (by decide +kernel)
theorem cov551_6 : PA.Covered 6 (OZ.Valid 6 w551.low w551.t w551.y w551.r w551.cap) (P33.root 6) :=
  Night6836Tree.sound w551 pick551 6 t567 _ (by decide +kernel)
theorem cov551_7 : PA.Covered 7 (OZ.Valid 7 w551.low w551.t w551.y w551.r w551.cap) (P33.root 7) :=
  Night6836Tree.sound w551 pick551 7 t2134 _ (by decide +kernel)
theorem window551 : P33.WindowCount w551 := by
  apply P33.window_count w551 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov551_1
  · exact cov551_2
  · exact cov551_3
  · exact cov551_4
  · exact cov551_5
  · exact cov551_6
  · exact cov551_7
def w552 : P33.Window := ⟨9,34,7447,7404,245372068002402136,21056,18000,5000000,81920000000⟩
def h552_0 : Height w552 := ⟨21056,18000,by decide +kernel⟩
def h552_1 : Height w552 := ⟨25947,15000,by decide +kernel⟩
def h552_2 : Height w552 := ⟨34247,12000,by decide +kernel⟩
def pick552 (cl : ℕ) : Height w552 := if cl<12 then (h552_0) else (if cl<213 then (h552_1) else (h552_2))
private theorem k552_1_0 : check w552 pick552 1 t3146 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k552_1_1 : check w552 pick552 1 t11014 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k552_1_2 : check w552 pick552 1 t11015 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w552 pick552 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t3146 t11014 k552_1_0 k552_1_1
private theorem k552_1_3 : check w552 pick552 1 t10417 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k552_1_4 : check w552 pick552 1 t10225 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k552_1_5 : check w552 pick552 1 t11016 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w552 pick552 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10417 t10225 k552_1_3 k552_1_4
private theorem k552_1_6 : check w552 pick552 1 t11017 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w552 pick552 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t11015 t11016 k552_1_2 k552_1_5
private theorem k552_1_7 : check w552 pick552 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k552_1_8 : check w552 pick552 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k552_1_9 : check w552 pick552 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w552 pick552 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k552_1_7 k552_1_8
private theorem k552_1_10 : check w552 pick552 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k552_1_11 : check w552 pick552 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k552_1_12 : check w552 pick552 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w552 pick552 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k552_1_10 k552_1_11
private theorem k552_1_13 : check w552 pick552 1 t10228 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w552 pick552 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t10065 k552_1_9 k552_1_12
private theorem k552_1_14 : check w552 pick552 1 t11018 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w552 pick552 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t11017 t10228 k552_1_6 k552_1_13
theorem cov552_1 : PA.Covered 1 (OZ.Valid 1 w552.low w552.t w552.y w552.r w552.cap) (P33.root 1) :=
  Night6836Tree.sound w552 pick552 1 t11018 _ k552_1_14
private theorem k552_2_0 : check w552 pick552 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k552_2_1 : check w552 pick552 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k552_2_2 : check w552 pick552 2 t3059 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w552 pick552 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t3026 k552_2_0 k552_2_1
theorem cov552_2 : PA.Covered 2 (OZ.Valid 2 w552.low w552.t w552.y w552.r w552.cap) (P33.root 2) :=
  Night6836Tree.sound w552 pick552 2 t3059 _ k552_2_2
theorem cov552_3 : PA.Covered 3 (OZ.Valid 3 w552.low w552.t w552.y w552.r w552.cap) (P33.root 3) :=
  Night6836Tree.sound w552 pick552 3 t564 _ (by decide +kernel)
theorem cov552_4 : PA.Covered 4 (OZ.Valid 4 w552.low w552.t w552.y w552.r w552.cap) (P33.root 4) :=
  Night6836Tree.sound w552 pick552 4 t565 _ (by decide +kernel)
theorem cov552_5 : PA.Covered 5 (OZ.Valid 5 w552.low w552.t w552.y w552.r w552.cap) (P33.root 5) :=
  Night6836Tree.sound w552 pick552 5 t566 _ (by decide +kernel)
theorem cov552_6 : PA.Covered 6 (OZ.Valid 6 w552.low w552.t w552.y w552.r w552.cap) (P33.root 6) :=
  Night6836Tree.sound w552 pick552 6 t567 _ (by decide +kernel)
theorem cov552_7 : PA.Covered 7 (OZ.Valid 7 w552.low w552.t w552.y w552.r w552.cap) (P33.root 7) :=
  Night6836Tree.sound w552 pick552 7 t568 _ (by decide +kernel)
theorem window552 : P33.WindowCount w552 := by
  apply P33.window_count w552 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov552_1
  · exact cov552_2
  · exact cov552_3
  · exact cov552_4
  · exact cov552_5
  · exact cov552_6
  · exact cov552_7
def w553 : P33.Window := ⟨9,35,5434,4435,203375475153866294,35556,31000,5000000,81920000000⟩
def h553_0 : Height w553 := ⟨35556,31000,by decide +kernel⟩
def h553_1 : Height w553 := ⟨41484,27000,by decide +kernel⟩
def h553_2 : Height w553 := ⟨49834,23000,by decide +kernel⟩
def h553_3 : Height w553 := ⟨63827,19000,by decide +kernel⟩
def pick553 (cl : ℕ) : Height w553 := if cl<46 then (if cl<5 then (h553_0) else (h553_1)) else (if cl<676 then (h553_2) else (h553_3))
private theorem k553_1_0 : check w553 pick553 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k553_1_1 : check w553 pick553 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k553_1_2 : check w553 pick553 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w553 pick553 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k553_1_0 k553_1_1
private theorem k553_1_3 : check w553 pick553 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k553_1_4 : check w553 pick553 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w553 pick553 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k553_1_2 k553_1_3
private theorem k553_1_5 : check w553 pick553 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k553_1_6 : check w553 pick553 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k553_1_7 : check w553 pick553 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w553 pick553 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k553_1_5 k553_1_6
private theorem k553_1_8 : check w553 pick553 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k553_1_9 : check w553 pick553 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k553_1_10 : check w553 pick553 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w553 pick553 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k553_1_8 k553_1_9
private theorem k553_1_11 : check w553 pick553 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w553 pick553 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k553_1_7 k553_1_10
private theorem k553_1_12 : check w553 pick553 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w553 pick553 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k553_1_4 k553_1_11
theorem cov553_1 : PA.Covered 1 (OZ.Valid 1 w553.low w553.t w553.y w553.r w553.cap) (P33.root 1) :=
  Night6836Tree.sound w553 pick553 1 t10025 _ k553_1_12
private theorem k553_2_0 : check w553 pick553 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k553_2_1 : check w553 pick553 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k553_2_2 : check w553 pick553 2 t9556 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w553 pick553 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9133 k553_2_0 k553_2_1
theorem cov553_2 : PA.Covered 2 (OZ.Valid 2 w553.low w553.t w553.y w553.r w553.cap) (P33.root 2) :=
  Night6836Tree.sound w553 pick553 2 t9556 _ k553_2_2
theorem cov553_3 : PA.Covered 3 (OZ.Valid 3 w553.low w553.t w553.y w553.r w553.cap) (P33.root 3) :=
  Night6836Tree.sound w553 pick553 3 t564 _ (by decide +kernel)
theorem cov553_4 : PA.Covered 4 (OZ.Valid 4 w553.low w553.t w553.y w553.r w553.cap) (P33.root 4) :=
  Night6836Tree.sound w553 pick553 4 t565 _ (by decide +kernel)
theorem cov553_5 : PA.Covered 5 (OZ.Valid 5 w553.low w553.t w553.y w553.r w553.cap) (P33.root 5) :=
  Night6836Tree.sound w553 pick553 5 t566 _ (by decide +kernel)
theorem cov553_6 : PA.Covered 6 (OZ.Valid 6 w553.low w553.t w553.y w553.r w553.cap) (P33.root 6) :=
  Night6836Tree.sound w553 pick553 6 t567 _ (by decide +kernel)
theorem cov553_7 : PA.Covered 7 (OZ.Valid 7 w553.low w553.t w553.y w553.r w553.cap) (P33.root 7) :=
  Night6836Tree.sound w553 pick553 7 t2134 _ (by decide +kernel)
theorem window553 : P33.WindowCount w553 := by
  apply P33.window_count w553 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov553_1
  · exact cov553_2
  · exact cov553_3
  · exact cov553_4
  · exact cov553_5
  · exact cov553_6
  · exact cov553_7
def w554 : P33.Window := ⟨9,35,7247,6298,244342173045381436,26167,21000,5000000,81920000000⟩
def h554_0 : Height w554 := ⟨26167,21000,by decide +kernel⟩
def h554_1 : Height w554 := ⟨31090,18000,by decide +kernel⟩
def h554_2 : Height w554 := ⟨38605,15000,by decide +kernel⟩
def h554_3 : Height w554 := ⟨53432,12000,by decide +kernel⟩
def pick554 (cl : ℕ) : Height w554 := if cl<135 then (if cl<12 then (h554_0) else (h554_1)) else (if cl<1002 then (h554_2) else (h554_3))
private theorem k554_1_0 : check w554 pick554 1 t3146 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k554_1_1 : check w554 pick554 1 t11019 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k554_1_2 : check w554 pick554 1 t11020 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w554 pick554 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t3146 t11019 k554_1_0 k554_1_1
private theorem k554_1_3 : check w554 pick554 1 t10417 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k554_1_4 : check w554 pick554 1 t10225 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k554_1_5 : check w554 pick554 1 t11016 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w554 pick554 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10417 t10225 k554_1_3 k554_1_4
private theorem k554_1_6 : check w554 pick554 1 t11021 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w554 pick554 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t11020 t11016 k554_1_2 k554_1_5
private theorem k554_1_7 : check w554 pick554 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k554_1_8 : check w554 pick554 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k554_1_9 : check w554 pick554 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w554 pick554 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k554_1_7 k554_1_8
private theorem k554_1_10 : check w554 pick554 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k554_1_11 : check w554 pick554 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k554_1_12 : check w554 pick554 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w554 pick554 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k554_1_10 k554_1_11
private theorem k554_1_13 : check w554 pick554 1 t10228 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w554 pick554 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t10065 k554_1_9 k554_1_12
private theorem k554_1_14 : check w554 pick554 1 t11022 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w554 pick554 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t11021 t10228 k554_1_6 k554_1_13
theorem cov554_1 : PA.Covered 1 (OZ.Valid 1 w554.low w554.t w554.y w554.r w554.cap) (P33.root 1) :=
  Night6836Tree.sound w554 pick554 1 t11022 _ k554_1_14
private theorem k554_2_0 : check w554 pick554 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k554_2_1 : check w554 pick554 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k554_2_2 : check w554 pick554 2 t3059 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w554 pick554 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t3026 k554_2_0 k554_2_1
theorem cov554_2 : PA.Covered 2 (OZ.Valid 2 w554.low w554.t w554.y w554.r w554.cap) (P33.root 2) :=
  Night6836Tree.sound w554 pick554 2 t3059 _ k554_2_2
theorem cov554_3 : PA.Covered 3 (OZ.Valid 3 w554.low w554.t w554.y w554.r w554.cap) (P33.root 3) :=
  Night6836Tree.sound w554 pick554 3 t564 _ (by decide +kernel)
theorem cov554_4 : PA.Covered 4 (OZ.Valid 4 w554.low w554.t w554.y w554.r w554.cap) (P33.root 4) :=
  Night6836Tree.sound w554 pick554 4 t565 _ (by decide +kernel)
theorem cov554_5 : PA.Covered 5 (OZ.Valid 5 w554.low w554.t w554.y w554.r w554.cap) (P33.root 5) :=
  Night6836Tree.sound w554 pick554 5 t566 _ (by decide +kernel)
theorem cov554_6 : PA.Covered 6 (OZ.Valid 6 w554.low w554.t w554.y w554.r w554.cap) (P33.root 6) :=
  Night6836Tree.sound w554 pick554 6 t567 _ (by decide +kernel)
theorem cov554_7 : PA.Covered 7 (OZ.Valid 7 w554.low w554.t w554.y w554.r w554.cap) (P33.root 7) :=
  Night6836Tree.sound w554 pick554 7 t568 _ (by decide +kernel)
theorem window554 : P33.WindowCount w554 := by
  apply P33.window_count w554 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov554_1
  · exact cov554_2
  · exact cov554_3
  · exact cov554_4
  · exact cov554_5
  · exact cov554_6
  · exact cov554_7
def w555 : P33.Window := ⟨9,35,7403,7270,244558387327264161,22944,18000,5000000,81920000000⟩
def h555_0 : Height w555 := ⟨22944,18000,by decide +kernel⟩
def h555_1 : Height w555 := ⟨28159,15000,by decide +kernel⟩
def h555_2 : Height w555 := ⟨37178,12000,by decide +kernel⟩
def pick555 (cl : ℕ) : Height w555 := if cl<32 then (h555_0) else (if cl<281 then (h555_1) else (h555_2))
private theorem k555_1_0 : check w555 pick555 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k555_1_1 : check w555 pick555 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k555_1_2 : check w555 pick555 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w555 pick555 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k555_1_0 k555_1_1
private theorem k555_1_3 : check w555 pick555 1 t10054 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k555_1_4 : check w555 pick555 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k555_1_5 : check w555 pick555 1 t10059 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w555 pick555 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10054 t10058 k555_1_3 k555_1_4
private theorem k555_1_6 : check w555 pick555 1 t10235 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w555 pick555 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10059 k555_1_2 k555_1_5
private theorem k555_1_7 : check w555 pick555 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k555_1_8 : check w555 pick555 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k555_1_9 : check w555 pick555 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w555 pick555 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k555_1_7 k555_1_8
private theorem k555_1_10 : check w555 pick555 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k555_1_11 : check w555 pick555 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k555_1_12 : check w555 pick555 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w555 pick555 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k555_1_10 k555_1_11
private theorem k555_1_13 : check w555 pick555 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w555 pick555 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k555_1_9 k555_1_12
private theorem k555_1_14 : check w555 pick555 1 t10236 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w555 pick555 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10235 t10066 k555_1_6 k555_1_13
theorem cov555_1 : PA.Covered 1 (OZ.Valid 1 w555.low w555.t w555.y w555.r w555.cap) (P33.root 1) :=
  Night6836Tree.sound w555 pick555 1 t10236 _ k555_1_14
private theorem k555_2_0 : check w555 pick555 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k555_2_1 : check w555 pick555 2 t3115 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k555_2_2 : check w555 pick555 2 t3116 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w555 pick555 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t3115 k555_2_0 k555_2_1
theorem cov555_2 : PA.Covered 2 (OZ.Valid 2 w555.low w555.t w555.y w555.r w555.cap) (P33.root 2) :=
  Night6836Tree.sound w555 pick555 2 t3116 _ k555_2_2
theorem cov555_3 : PA.Covered 3 (OZ.Valid 3 w555.low w555.t w555.y w555.r w555.cap) (P33.root 3) :=
  Night6836Tree.sound w555 pick555 3 t564 _ (by decide +kernel)
theorem cov555_4 : PA.Covered 4 (OZ.Valid 4 w555.low w555.t w555.y w555.r w555.cap) (P33.root 4) :=
  Night6836Tree.sound w555 pick555 4 t565 _ (by decide +kernel)
theorem cov555_5 : PA.Covered 5 (OZ.Valid 5 w555.low w555.t w555.y w555.r w555.cap) (P33.root 5) :=
  Night6836Tree.sound w555 pick555 5 t566 _ (by decide +kernel)
theorem cov555_6 : PA.Covered 6 (OZ.Valid 6 w555.low w555.t w555.y w555.r w555.cap) (P33.root 6) :=
  Night6836Tree.sound w555 pick555 6 t567 _ (by decide +kernel)
theorem cov555_7 : PA.Covered 7 (OZ.Valid 7 w555.low w555.t w555.y w555.r w555.cap) (P33.root 7) :=
  Night6836Tree.sound w555 pick555 7 t568 _ (by decide +kernel)
theorem window555 : P33.WindowCount w555 := by
  apply P33.window_count w555 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov555_1
  · exact cov555_2
  · exact cov555_3
  · exact cov555_4
  · exact cov555_5
  · exact cov555_6
  · exact cov555_7
def w556 : P33.Window := ⟨9,36,4635,3636,190560776133094285,43864,39000,5000000,81920000000⟩
def h556_0 : Height w556 := ⟨43864,39000,by decide +kernel⟩
def h556_1 : Height w556 := ⟨49380,35000,by decide +kernel⟩
def h556_2 : Height w556 := ⟨56392,31000,by decide +kernel⟩
def h556_3 : Height w556 := ⟨66107,27000,by decide +kernel⟩
def h556_4 : Height w556 := ⟨81506,23000,by decide +kernel⟩
def pick556 (cl : ℕ) : Height w556 := if cl<32 then (if cl<3 then (h556_0) else (h556_1)) else (if cl<107 then (h556_2) else (if cl<925 then (h556_3) else (h556_4)))
private theorem k556_1_0 : check w556 pick556 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k556_1_1 : check w556 pick556 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k556_1_2 : check w556 pick556 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w556 pick556 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k556_1_0 k556_1_1
private theorem k556_1_3 : check w556 pick556 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k556_1_4 : check w556 pick556 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w556 pick556 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k556_1_2 k556_1_3
private theorem k556_1_5 : check w556 pick556 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k556_1_6 : check w556 pick556 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k556_1_7 : check w556 pick556 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w556 pick556 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k556_1_5 k556_1_6
private theorem k556_1_8 : check w556 pick556 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k556_1_9 : check w556 pick556 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k556_1_10 : check w556 pick556 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w556 pick556 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k556_1_8 k556_1_9
private theorem k556_1_11 : check w556 pick556 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w556 pick556 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k556_1_7 k556_1_10
private theorem k556_1_12 : check w556 pick556 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w556 pick556 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k556_1_4 k556_1_11
theorem cov556_1 : PA.Covered 1 (OZ.Valid 1 w556.low w556.t w556.y w556.r w556.cap) (P33.root 1) :=
  Night6836Tree.sound w556 pick556 1 t10025 _ k556_1_12
theorem cov556_2 : PA.Covered 2 (OZ.Valid 2 w556.low w556.t w556.y w556.r w556.cap) (P33.root 2) :=
  Night6836Tree.sound w556 pick556 2 t4654 _ (by decide +kernel)
theorem cov556_3 : PA.Covered 3 (OZ.Valid 3 w556.low w556.t w556.y w556.r w556.cap) (P33.root 3) :=
  Night6836Tree.sound w556 pick556 3 t564 _ (by decide +kernel)
theorem cov556_4 : PA.Covered 4 (OZ.Valid 4 w556.low w556.t w556.y w556.r w556.cap) (P33.root 4) :=
  Night6836Tree.sound w556 pick556 4 t565 _ (by decide +kernel)
theorem cov556_5 : PA.Covered 5 (OZ.Valid 5 w556.low w556.t w556.y w556.r w556.cap) (P33.root 5) :=
  Night6836Tree.sound w556 pick556 5 t566 _ (by decide +kernel)
theorem cov556_6 : PA.Covered 6 (OZ.Valid 6 w556.low w556.t w556.y w556.r w556.cap) (P33.root 6) :=
  Night6836Tree.sound w556 pick556 6 t567 _ (by decide +kernel)
theorem cov556_7 : PA.Covered 7 (OZ.Valid 7 w556.low w556.t w556.y w556.r w556.cap) (P33.root 7) :=
  Night6836Tree.sound w556 pick556 7 t2134 _ (by decide +kernel)
theorem window556 : P33.WindowCount w556 := by
  apply P33.window_count w556 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov556_1
  · exact cov556_2
  · exact cov556_3
  · exact cov556_4
  · exact cov556_5
  · exact cov556_6
  · exact cov556_7
def w557 : P33.Window := ⟨9,36,6167,5218,239299829555148909,30806,27000,5000000,81920000000⟩
def h557_0 : Height w557 := ⟨30806,27000,by decide +kernel⟩
def h557_1 : Height w557 := ⟨35045,24000,by decide +kernel⟩
def h557_2 : Height w557 := ⟨40603,21000,by decide +kernel⟩
def h557_3 : Height w557 := ⟨48729,18000,by decide +kernel⟩
def pick557 (cl : ℕ) : Height w557 := if cl<32 then (if cl<4 then (h557_0) else (h557_1)) else (if cl<200 then (h557_2) else (h557_3))
private theorem k557_1_0 : check w557 pick557 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k557_1_1 : check w557 pick557 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k557_1_2 : check w557 pick557 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w557 pick557 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k557_1_0 k557_1_1
private theorem k557_1_3 : check w557 pick557 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k557_1_4 : check w557 pick557 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w557 pick557 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k557_1_2 k557_1_3
private theorem k557_1_5 : check w557 pick557 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k557_1_6 : check w557 pick557 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k557_1_7 : check w557 pick557 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w557 pick557 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k557_1_5 k557_1_6
private theorem k557_1_8 : check w557 pick557 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k557_1_9 : check w557 pick557 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k557_1_10 : check w557 pick557 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w557 pick557 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k557_1_8 k557_1_9
private theorem k557_1_11 : check w557 pick557 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w557 pick557 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k557_1_7 k557_1_10
private theorem k557_1_12 : check w557 pick557 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w557 pick557 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k557_1_4 k557_1_11
theorem cov557_1 : PA.Covered 1 (OZ.Valid 1 w557.low w557.t w557.y w557.r w557.cap) (P33.root 1) :=
  Night6836Tree.sound w557 pick557 1 t10025 _ k557_1_12
theorem cov557_2 : PA.Covered 2 (OZ.Valid 2 w557.low w557.t w557.y w557.r w557.cap) (P33.root 2) :=
  Night6836Tree.sound w557 pick557 2 t4654 _ (by decide +kernel)
theorem cov557_3 : PA.Covered 3 (OZ.Valid 3 w557.low w557.t w557.y w557.r w557.cap) (P33.root 3) :=
  Night6836Tree.sound w557 pick557 3 t564 _ (by decide +kernel)
theorem cov557_4 : PA.Covered 4 (OZ.Valid 4 w557.low w557.t w557.y w557.r w557.cap) (P33.root 4) :=
  Night6836Tree.sound w557 pick557 4 t565 _ (by decide +kernel)
theorem cov557_5 : PA.Covered 5 (OZ.Valid 5 w557.low w557.t w557.y w557.r w557.cap) (P33.root 5) :=
  Night6836Tree.sound w557 pick557 5 t566 _ (by decide +kernel)
theorem cov557_6 : PA.Covered 6 (OZ.Valid 6 w557.low w557.t w557.y w557.r w557.cap) (P33.root 6) :=
  Night6836Tree.sound w557 pick557 6 t567 _ (by decide +kernel)
theorem cov557_7 : PA.Covered 7 (OZ.Valid 7 w557.low w557.t w557.y w557.r w557.cap) (P33.root 7) :=
  Night6836Tree.sound w557 pick557 7 t2134 _ (by decide +kernel)
theorem window557 : P33.WindowCount w557 := by
  apply P33.window_count w557 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov557_1
  · exact cov557_2
  · exact cov557_3
  · exact cov557_4
  · exact cov557_5
  · exact cov557_6
  · exact cov557_7
def w558 : P33.Window := ⟨9,36,7359,7315,245423638875113172,23682,18000,5000000,81920000000⟩
def h558_0 : Height w558 := ⟨23682,18000,by decide +kernel⟩
def h558_1 : Height w558 := ⟨28943,15000,by decide +kernel⟩
def h558_2 : Height w558 := ⟨38028,12000,by decide +kernel⟩
def pick558 (cl : ℕ) : Height w558 := if cl<27 then (h558_0) else (if cl<287 then (h558_1) else (h558_2))
private theorem k558_1_0 : check w558 pick558 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k558_1_1 : check w558 pick558 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k558_1_2 : check w558 pick558 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w558 pick558 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k558_1_0 k558_1_1
private theorem k558_1_3 : check w558 pick558 1 t10054 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k558_1_4 : check w558 pick558 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k558_1_5 : check w558 pick558 1 t10059 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w558 pick558 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10054 t10058 k558_1_3 k558_1_4
private theorem k558_1_6 : check w558 pick558 1 t10235 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w558 pick558 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10059 k558_1_2 k558_1_5
private theorem k558_1_7 : check w558 pick558 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k558_1_8 : check w558 pick558 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k558_1_9 : check w558 pick558 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w558 pick558 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k558_1_7 k558_1_8
private theorem k558_1_10 : check w558 pick558 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k558_1_11 : check w558 pick558 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k558_1_12 : check w558 pick558 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w558 pick558 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k558_1_10 k558_1_11
private theorem k558_1_13 : check w558 pick558 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w558 pick558 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k558_1_9 k558_1_12
private theorem k558_1_14 : check w558 pick558 1 t10236 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w558 pick558 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10235 t10066 k558_1_6 k558_1_13
theorem cov558_1 : PA.Covered 1 (OZ.Valid 1 w558.low w558.t w558.y w558.r w558.cap) (P33.root 1) :=
  Night6836Tree.sound w558 pick558 1 t10236 _ k558_1_14
private theorem k558_2_0 : check w558 pick558 2 t11023 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k558_2_1 : check w558 pick558 2 t11030 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k558_2_2 : check w558 pick558 2 t11031 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w558 pick558 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t11023 t11030 k558_2_0 k558_2_1
theorem cov558_2 : PA.Covered 2 (OZ.Valid 2 w558.low w558.t w558.y w558.r w558.cap) (P33.root 2) :=
  Night6836Tree.sound w558 pick558 2 t11031 _ k558_2_2
theorem cov558_3 : PA.Covered 3 (OZ.Valid 3 w558.low w558.t w558.y w558.r w558.cap) (P33.root 3) :=
  Night6836Tree.sound w558 pick558 3 t564 _ (by decide +kernel)
theorem cov558_4 : PA.Covered 4 (OZ.Valid 4 w558.low w558.t w558.y w558.r w558.cap) (P33.root 4) :=
  Night6836Tree.sound w558 pick558 4 t565 _ (by decide +kernel)
theorem cov558_5 : PA.Covered 5 (OZ.Valid 5 w558.low w558.t w558.y w558.r w558.cap) (P33.root 5) :=
  Night6836Tree.sound w558 pick558 5 t566 _ (by decide +kernel)
theorem cov558_6 : PA.Covered 6 (OZ.Valid 6 w558.low w558.t w558.y w558.r w558.cap) (P33.root 6) :=
  Night6836Tree.sound w558 pick558 6 t567 _ (by decide +kernel)
theorem cov558_7 : PA.Covered 7 (OZ.Valid 7 w558.low w558.t w558.y w558.r w558.cap) (P33.root 7) :=
  Night6836Tree.sound w558 pick558 7 t568 _ (by decide +kernel)
theorem window558 : P33.WindowCount w558 := by
  apply P33.window_count w558 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov558_1
  · exact cov558_2
  · exact cov558_3
  · exact cov558_4
  · exact cov558_5
  · exact cov558_6
  · exact cov558_7
def w559 : P33.Window := ⟨9,37,4636,3637,193708812950267486,45844,39000,5000000,81920000000⟩
def h559_0 : Height w559 := ⟨45844,39000,by decide +kernel⟩
def h559_1 : Height w559 := ⟨51467,35000,by decide +kernel⟩
def h559_2 : Height w559 := ⟨58630,31000,by decide +kernel⟩
def h559_3 : Height w559 := ⟨68576,27000,by decide +kernel⟩
def h559_4 : Height w559 := ⟨84371,23000,by decide +kernel⟩
def pick559 (cl : ℕ) : Height w559 := if cl<32 then (if cl<4 then (h559_0) else (h559_1)) else (if cl<132 then (h559_2) else (if cl<925 then (h559_3) else (h559_4)))
private theorem k559_1_0 : check w559 pick559 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k559_1_1 : check w559 pick559 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k559_1_2 : check w559 pick559 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w559 pick559 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k559_1_0 k559_1_1
private theorem k559_1_3 : check w559 pick559 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k559_1_4 : check w559 pick559 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w559 pick559 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k559_1_2 k559_1_3
private theorem k559_1_5 : check w559 pick559 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k559_1_6 : check w559 pick559 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k559_1_7 : check w559 pick559 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w559 pick559 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k559_1_5 k559_1_6
private theorem k559_1_8 : check w559 pick559 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k559_1_9 : check w559 pick559 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k559_1_10 : check w559 pick559 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w559 pick559 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k559_1_8 k559_1_9
private theorem k559_1_11 : check w559 pick559 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w559 pick559 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k559_1_7 k559_1_10
private theorem k559_1_12 : check w559 pick559 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w559 pick559 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k559_1_4 k559_1_11
theorem cov559_1 : PA.Covered 1 (OZ.Valid 1 w559.low w559.t w559.y w559.r w559.cap) (P33.root 1) :=
  Night6836Tree.sound w559 pick559 1 t10025 _ k559_1_12
theorem cov559_2 : PA.Covered 2 (OZ.Valid 2 w559.low w559.t w559.y w559.r w559.cap) (P33.root 2) :=
  Night6836Tree.sound w559 pick559 2 t4654 _ (by decide +kernel)
theorem cov559_3 : PA.Covered 3 (OZ.Valid 3 w559.low w559.t w559.y w559.r w559.cap) (P33.root 3) :=
  Night6836Tree.sound w559 pick559 3 t564 _ (by decide +kernel)
theorem cov559_4 : PA.Covered 4 (OZ.Valid 4 w559.low w559.t w559.y w559.r w559.cap) (P33.root 4) :=
  Night6836Tree.sound w559 pick559 4 t565 _ (by decide +kernel)
theorem cov559_5 : PA.Covered 5 (OZ.Valid 5 w559.low w559.t w559.y w559.r w559.cap) (P33.root 5) :=
  Night6836Tree.sound w559 pick559 5 t566 _ (by decide +kernel)
theorem cov559_6 : PA.Covered 6 (OZ.Valid 6 w559.low w559.t w559.y w559.r w559.cap) (P33.root 6) :=
  Night6836Tree.sound w559 pick559 6 t567 _ (by decide +kernel)
theorem cov559_7 : PA.Covered 7 (OZ.Valid 7 w559.low w559.t w559.y w559.r w559.cap) (P33.root 7) :=
  Night6836Tree.sound w559 pick559 7 t2134 _ (by decide +kernel)
theorem window559 : P33.WindowCount w559 := by
  apply P33.window_count w559 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov559_1
  · exact cov559_2
  · exact cov559_3
  · exact cov559_4
  · exact cov559_5
  · exact cov559_6
  · exact cov559_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w560 : P33.Window := ⟨9,37,5736,4737,203580018386889531,33911,31000,5000000,81920000000⟩
def h560_0 : Height w560 := ⟨33911,31000,by decide +kernel⟩
def h560_1 : Height w560 := ⟨39343,27000,by decide +kernel⟩
def h560_2 : Height w560 := ⟨46790,23000,by decide +kernel⟩
def h560_3 : Height w560 := ⟨58762,19000,by decide +kernel⟩
def pick560 (cl : ℕ) : Height w560 := if cl<32 then (if cl<2 then (h560_0) else (h560_1)) else (if cl<279 then (h560_2) else (h560_3))
private theorem k560_1_0 : check w560 pick560 1 t3146 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k560_1_1 : check w560 pick560 1 t11032 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k560_1_2 : check w560 pick560 1 t11033 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w560 pick560 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t3146 t11032 k560_1_0 k560_1_1
private theorem k560_1_3 : check w560 pick560 1 t10417 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k560_1_4 : check w560 pick560 1 t10225 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k560_1_5 : check w560 pick560 1 t11016 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w560 pick560 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10417 t10225 k560_1_3 k560_1_4
private theorem k560_1_6 : check w560 pick560 1 t11034 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w560 pick560 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t11033 t11016 k560_1_2 k560_1_5
private theorem k560_1_7 : check w560 pick560 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k560_1_8 : check w560 pick560 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k560_1_9 : check w560 pick560 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w560 pick560 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k560_1_7 k560_1_8
private theorem k560_1_10 : check w560 pick560 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k560_1_11 : check w560 pick560 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k560_1_12 : check w560 pick560 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w560 pick560 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k560_1_10 k560_1_11
private theorem k560_1_13 : check w560 pick560 1 t10228 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w560 pick560 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t10065 k560_1_9 k560_1_12
private theorem k560_1_14 : check w560 pick560 1 t11035 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w560 pick560 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t11034 t10228 k560_1_6 k560_1_13
theorem cov560_1 : PA.Covered 1 (OZ.Valid 1 w560.low w560.t w560.y w560.r w560.cap) (P33.root 1) :=
  Night6836Tree.sound w560 pick560 1 t11035 _ k560_1_14
private theorem k560_2_0 : check w560 pick560 2 t3206 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k560_2_1 : check w560 pick560 2 t3714 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k560_2_2 : check w560 pick560 2 t11036 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w560 pick560 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t3206 t3714 k560_2_0 k560_2_1
theorem cov560_2 : PA.Covered 2 (OZ.Valid 2 w560.low w560.t w560.y w560.r w560.cap) (P33.root 2) :=
  Night6836Tree.sound w560 pick560 2 t11036 _ k560_2_2
theorem cov560_3 : PA.Covered 3 (OZ.Valid 3 w560.low w560.t w560.y w560.r w560.cap) (P33.root 3) :=
  Night6836Tree.sound w560 pick560 3 t564 _ (by decide +kernel)
theorem cov560_4 : PA.Covered 4 (OZ.Valid 4 w560.low w560.t w560.y w560.r w560.cap) (P33.root 4) :=
  Night6836Tree.sound w560 pick560 4 t565 _ (by decide +kernel)
theorem cov560_5 : PA.Covered 5 (OZ.Valid 5 w560.low w560.t w560.y w560.r w560.cap) (P33.root 5) :=
  Night6836Tree.sound w560 pick560 5 t566 _ (by decide +kernel)
theorem cov560_6 : PA.Covered 6 (OZ.Valid 6 w560.low w560.t w560.y w560.r w560.cap) (P33.root 6) :=
  Night6836Tree.sound w560 pick560 6 t567 _ (by decide +kernel)
theorem cov560_7 : PA.Covered 7 (OZ.Valid 7 w560.low w560.t w560.y w560.r w560.cap) (P33.root 7) :=
  Night6836Tree.sound w560 pick560 7 t2134 _ (by decide +kernel)
theorem window560 : P33.WindowCount w560 := by
  apply P33.window_count w560 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov560_1
  · exact cov560_2
  · exact cov560_3
  · exact cov560_4
  · exact cov560_5
  · exact cov560_6
  · exact cov560_7
def w561 : P33.Window := ⟨9,37,7314,7270,245813263012888835,25035,18000,5000000,81920000000⟩
def h561_0 : Height w561 := ⟨25035,18000,by decide +kernel⟩
def h561_1 : Height w561 := ⟨30492,15000,by decide +kernel⟩
def h561_2 : Height w561 := ⟨39995,12000,by decide +kernel⟩
def pick561 (cl : ℕ) : Height w561 := if cl<27 then (h561_0) else (if cl<317 then (h561_1) else (h561_2))
private theorem k561_1_0 : check w561 pick561 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k561_1_1 : check w561 pick561 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k561_1_2 : check w561 pick561 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w561 pick561 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k561_1_0 k561_1_1
private theorem k561_1_3 : check w561 pick561 1 t10054 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k561_1_4 : check w561 pick561 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k561_1_5 : check w561 pick561 1 t10059 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w561 pick561 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10054 t10058 k561_1_3 k561_1_4
private theorem k561_1_6 : check w561 pick561 1 t10235 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w561 pick561 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10059 k561_1_2 k561_1_5
private theorem k561_1_7 : check w561 pick561 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k561_1_8 : check w561 pick561 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k561_1_9 : check w561 pick561 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w561 pick561 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k561_1_7 k561_1_8
private theorem k561_1_10 : check w561 pick561 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k561_1_11 : check w561 pick561 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k561_1_12 : check w561 pick561 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w561 pick561 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k561_1_10 k561_1_11
private theorem k561_1_13 : check w561 pick561 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w561 pick561 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k561_1_9 k561_1_12
private theorem k561_1_14 : check w561 pick561 1 t10236 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w561 pick561 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10235 t10066 k561_1_6 k561_1_13
theorem cov561_1 : PA.Covered 1 (OZ.Valid 1 w561.low w561.t w561.y w561.r w561.cap) (P33.root 1) :=
  Night6836Tree.sound w561 pick561 1 t10236 _ k561_1_14
private theorem k561_2_0 : check w561 pick561 2 t9641 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k561_2_1 : check w561 pick561 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k561_2_2 : check w561 pick561 2 t11037 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w561 pick561 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9641 t3490 k561_2_0 k561_2_1
private theorem k561_2_3 : check w561 pick561 2 t11041 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k561_2_4 : check w561 pick561 2 t4155 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k561_2_5 : check w561 pick561 2 t11042 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w561 pick561 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t11041 t4155 k561_2_3 k561_2_4
private theorem k561_2_6 : check w561 pick561 2 t11043 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w561 pick561 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11037 t11042 k561_2_2 k561_2_5
theorem cov561_2 : PA.Covered 2 (OZ.Valid 2 w561.low w561.t w561.y w561.r w561.cap) (P33.root 2) :=
  Night6836Tree.sound w561 pick561 2 t11043 _ k561_2_6
theorem cov561_3 : PA.Covered 3 (OZ.Valid 3 w561.low w561.t w561.y w561.r w561.cap) (P33.root 3) :=
  Night6836Tree.sound w561 pick561 3 t564 _ (by decide +kernel)
theorem cov561_4 : PA.Covered 4 (OZ.Valid 4 w561.low w561.t w561.y w561.r w561.cap) (P33.root 4) :=
  Night6836Tree.sound w561 pick561 4 t565 _ (by decide +kernel)
theorem cov561_5 : PA.Covered 5 (OZ.Valid 5 w561.low w561.t w561.y w561.r w561.cap) (P33.root 5) :=
  Night6836Tree.sound w561 pick561 5 t566 _ (by decide +kernel)
theorem cov561_6 : PA.Covered 6 (OZ.Valid 6 w561.low w561.t w561.y w561.r w561.cap) (P33.root 6) :=
  Night6836Tree.sound w561 pick561 6 t567 _ (by decide +kernel)
theorem cov561_7 : PA.Covered 7 (OZ.Valid 7 w561.low w561.t w561.y w561.r w561.cap) (P33.root 7) :=
  Night6836Tree.sound w561 pick561 7 t568 _ (by decide +kernel)
theorem window561 : P33.WindowCount w561 := by
  apply P33.window_count w561 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov561_1
  · exact cov561_2
  · exact cov561_3
  · exact cov561_4
  · exact cov561_5
  · exact cov561_6
  · exact cov561_7
def w562 : P33.Window := ⟨9,38,4637,3638,196855515690809666,47822,39000,5000000,81920000000⟩
def h562_0 : Height w562 := ⟨47822,39000,by decide +kernel⟩
def h562_1 : Height w562 := ⟨53551,35000,by decide +kernel⟩
def h562_2 : Height w562 := ⟨60865,31000,by decide +kernel⟩
def h562_3 : Height w562 := ⟨71042,27000,by decide +kernel⟩
def h562_4 : Height w562 := ⟨87230,23000,by decide +kernel⟩
def pick562 (cl : ℕ) : Height w562 := if cl<32 then (if cl<4 then (h562_0) else (h562_1)) else (if cl<172 then (h562_2) else (if cl<925 then (h562_3) else (h562_4)))
private theorem k562_1_0 : check w562 pick562 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k562_1_1 : check w562 pick562 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k562_1_2 : check w562 pick562 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w562 pick562 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k562_1_0 k562_1_1
private theorem k562_1_3 : check w562 pick562 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k562_1_4 : check w562 pick562 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w562 pick562 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k562_1_2 k562_1_3
private theorem k562_1_5 : check w562 pick562 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k562_1_6 : check w562 pick562 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k562_1_7 : check w562 pick562 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w562 pick562 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k562_1_5 k562_1_6
private theorem k562_1_8 : check w562 pick562 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k562_1_9 : check w562 pick562 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k562_1_10 : check w562 pick562 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w562 pick562 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k562_1_8 k562_1_9
private theorem k562_1_11 : check w562 pick562 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w562 pick562 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k562_1_7 k562_1_10
private theorem k562_1_12 : check w562 pick562 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w562 pick562 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k562_1_4 k562_1_11
theorem cov562_1 : PA.Covered 1 (OZ.Valid 1 w562.low w562.t w562.y w562.r w562.cap) (P33.root 1) :=
  Night6836Tree.sound w562 pick562 1 t10025 _ k562_1_12
theorem cov562_2 : PA.Covered 2 (OZ.Valid 2 w562.low w562.t w562.y w562.r w562.cap) (P33.root 2) :=
  Night6836Tree.sound w562 pick562 2 t4654 _ (by decide +kernel)
theorem cov562_3 : PA.Covered 3 (OZ.Valid 3 w562.low w562.t w562.y w562.r w562.cap) (P33.root 3) :=
  Night6836Tree.sound w562 pick562 3 t564 _ (by decide +kernel)
theorem cov562_4 : PA.Covered 4 (OZ.Valid 4 w562.low w562.t w562.y w562.r w562.cap) (P33.root 4) :=
  Night6836Tree.sound w562 pick562 4 t565 _ (by decide +kernel)
theorem cov562_5 : PA.Covered 5 (OZ.Valid 5 w562.low w562.t w562.y w562.r w562.cap) (P33.root 5) :=
  Night6836Tree.sound w562 pick562 5 t566 _ (by decide +kernel)
theorem cov562_6 : PA.Covered 6 (OZ.Valid 6 w562.low w562.t w562.y w562.r w562.cap) (P33.root 6) :=
  Night6836Tree.sound w562 pick562 6 t567 _ (by decide +kernel)
theorem cov562_7 : PA.Covered 7 (OZ.Valid 7 w562.low w562.t w562.y w562.r w562.cap) (P33.root 7) :=
  Night6836Tree.sound w562 pick562 7 t2134 _ (by decide +kernel)
theorem window562 : P33.WindowCount w562 := by
  apply P33.window_count w562 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov562_1
  · exact cov562_2
  · exact cov562_3
  · exact cov562_4
  · exact cov562_5
  · exact cov562_6
  · exact cov562_7
def w563 : P33.Window := ⟨9,38,7269,7223,241371284596991163,22451,21000,5000000,81920000000⟩
def h563_0 : Height w563 := ⟨22451,21000,by decide +kernel⟩
def h563_1 : Height w563 := ⟨26429,18000,by decide +kernel⟩
def h563_2 : Height w563 := ⟨32091,15000,by decide +kernel⟩
def h563_3 : Height w563 := ⟨42039,12000,by decide +kernel⟩
def pick563 (cl : ℕ) : Height w563 := if cl<27 then (if cl<2 then (h563_0) else (h563_1)) else (if cl<465 then (h563_2) else (h563_3))
private theorem k563_1_0 : check w563 pick563 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k563_1_1 : check w563 pick563 1 t10052 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k563_1_2 : check w563 pick563 1 t10053 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w563 pick563 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10052 k563_1_0 k563_1_1
private theorem k563_1_3 : check w563 pick563 1 t10054 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k563_1_4 : check w563 pick563 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k563_1_5 : check w563 pick563 1 t10059 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w563 pick563 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10054 t10058 k563_1_3 k563_1_4
private theorem k563_1_6 : check w563 pick563 1 t10060 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w563 pick563 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10053 t10059 k563_1_2 k563_1_5
private theorem k563_1_7 : check w563 pick563 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k563_1_8 : check w563 pick563 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k563_1_9 : check w563 pick563 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w563 pick563 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k563_1_7 k563_1_8
private theorem k563_1_10 : check w563 pick563 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k563_1_11 : check w563 pick563 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k563_1_12 : check w563 pick563 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w563 pick563 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k563_1_10 k563_1_11
private theorem k563_1_13 : check w563 pick563 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w563 pick563 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k563_1_9 k563_1_12
private theorem k563_1_14 : check w563 pick563 1 t10067 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w563 pick563 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10060 t10066 k563_1_6 k563_1_13
theorem cov563_1 : PA.Covered 1 (OZ.Valid 1 w563.low w563.t w563.y w563.r w563.cap) (P33.root 1) :=
  Night6836Tree.sound w563 pick563 1 t10067 _ k563_1_14
private theorem k563_2_0 : check w563 pick563 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k563_2_1 : check w563 pick563 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k563_2_2 : check w563 pick563 2 t3491 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w563 pick563 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3490 k563_2_0 k563_2_1
private theorem k563_2_3 : check w563 pick563 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k563_2_4 : check w563 pick563 2 t4155 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k563_2_5 : check w563 pick563 2 t4156 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w563 pick563 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4155 k563_2_3 k563_2_4
private theorem k563_2_6 : check w563 pick563 2 t4157 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w563 pick563 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3491 t4156 k563_2_2 k563_2_5
theorem cov563_2 : PA.Covered 2 (OZ.Valid 2 w563.low w563.t w563.y w563.r w563.cap) (P33.root 2) :=
  Night6836Tree.sound w563 pick563 2 t4157 _ k563_2_6
theorem cov563_3 : PA.Covered 3 (OZ.Valid 3 w563.low w563.t w563.y w563.r w563.cap) (P33.root 3) :=
  Night6836Tree.sound w563 pick563 3 t564 _ (by decide +kernel)
theorem cov563_4 : PA.Covered 4 (OZ.Valid 4 w563.low w563.t w563.y w563.r w563.cap) (P33.root 4) :=
  Night6836Tree.sound w563 pick563 4 t565 _ (by decide +kernel)
theorem cov563_5 : PA.Covered 5 (OZ.Valid 5 w563.low w563.t w563.y w563.r w563.cap) (P33.root 5) :=
  Night6836Tree.sound w563 pick563 5 t566 _ (by decide +kernel)
theorem cov563_6 : PA.Covered 6 (OZ.Valid 6 w563.low w563.t w563.y w563.r w563.cap) (P33.root 6) :=
  Night6836Tree.sound w563 pick563 6 t567 _ (by decide +kernel)
theorem cov563_7 : PA.Covered 7 (OZ.Valid 7 w563.low w563.t w563.y w563.r w563.cap) (P33.root 7) :=
  Night6836Tree.sound w563 pick563 7 t568 _ (by decide +kernel)
theorem window563 : P33.WindowCount w563 := by
  apply P33.window_count w563 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov563_1
  · exact cov563_2
  · exact cov563_3
  · exact cov563_4
  · exact cov563_5
  · exact cov563_6
  · exact cov563_7
def w564 : P33.Window := ⟨9,39,4638,3639,200000348005252212,49798,39000,5000000,81920000000⟩
def h564_0 : Height w564 := ⟨49798,39000,by decide +kernel⟩
def h564_1 : Height w564 := ⟨55633,35000,by decide +kernel⟩
def h564_2 : Height w564 := ⟨63098,31000,by decide +kernel⟩
def h564_3 : Height w564 := ⟨73504,27000,by decide +kernel⟩
def pick564 (cl : ℕ) : Height w564 := if cl<32 then (if cl<5 then (h564_0) else (h564_1)) else (if cl<172 then (h564_2) else (h564_3))
private theorem k564_1_0 : check w564 pick564 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k564_1_1 : check w564 pick564 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k564_1_2 : check w564 pick564 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w564 pick564 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k564_1_0 k564_1_1
private theorem k564_1_3 : check w564 pick564 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k564_1_4 : check w564 pick564 1 t10042 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w564 pick564 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10023 k564_1_2 k564_1_3
private theorem k564_1_5 : check w564 pick564 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k564_1_6 : check w564 pick564 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k564_1_7 : check w564 pick564 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w564 pick564 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k564_1_5 k564_1_6
private theorem k564_1_8 : check w564 pick564 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k564_1_9 : check w564 pick564 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k564_1_10 : check w564 pick564 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w564 pick564 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k564_1_8 k564_1_9
private theorem k564_1_11 : check w564 pick564 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w564 pick564 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k564_1_7 k564_1_10
private theorem k564_1_12 : check w564 pick564 1 t10043 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w564 pick564 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10042 t10007 k564_1_4 k564_1_11
theorem cov564_1 : PA.Covered 1 (OZ.Valid 1 w564.low w564.t w564.y w564.r w564.cap) (P33.root 1) :=
  Night6836Tree.sound w564 pick564 1 t10043 _ k564_1_12
theorem cov564_2 : PA.Covered 2 (OZ.Valid 2 w564.low w564.t w564.y w564.r w564.cap) (P33.root 2) :=
  Night6836Tree.sound w564 pick564 2 t4654 _ (by decide +kernel)
theorem cov564_3 : PA.Covered 3 (OZ.Valid 3 w564.low w564.t w564.y w564.r w564.cap) (P33.root 3) :=
  Night6836Tree.sound w564 pick564 3 t564 _ (by decide +kernel)
theorem cov564_4 : PA.Covered 4 (OZ.Valid 4 w564.low w564.t w564.y w564.r w564.cap) (P33.root 4) :=
  Night6836Tree.sound w564 pick564 4 t565 _ (by decide +kernel)
theorem cov564_5 : PA.Covered 5 (OZ.Valid 5 w564.low w564.t w564.y w564.r w564.cap) (P33.root 5) :=
  Night6836Tree.sound w564 pick564 5 t566 _ (by decide +kernel)
theorem cov564_6 : PA.Covered 6 (OZ.Valid 6 w564.low w564.t w564.y w564.r w564.cap) (P33.root 6) :=
  Night6836Tree.sound w564 pick564 6 t567 _ (by decide +kernel)
theorem cov564_7 : PA.Covered 7 (OZ.Valid 7 w564.low w564.t w564.y w564.r w564.cap) (P33.root 7) :=
  Night6836Tree.sound w564 pick564 7 t2134 _ (by decide +kernel)
theorem window564 : P33.WindowCount w564 := by
  apply P33.window_count w564 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov564_1
  · exact cov564_2
  · exact cov564_3
  · exact cov564_4
  · exact cov564_5
  · exact cov564_6
  · exact cov564_7
def w565 : P33.Window := ⟨9,39,7222,6976,244196100966320166,25164,21000,5000000,81920000000⟩
def h565_0 : Height w565 := ⟨25164,21000,by decide +kernel⟩
def h565_1 : Height w565 := ⟨29491,18000,by decide +kernel⟩
def h565_2 : Height w565 := ⟨35790,15000,by decide +kernel⟩
def h565_3 : Height w565 := ⟨47214,12000,by decide +kernel⟩
def pick565 (cl : ℕ) : Height w565 := if cl<49 then (if cl<5 then (h565_0) else (h565_1)) else (if cl<853 then (h565_2) else (h565_3))
private theorem k565_1_0 : check w565 pick565 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k565_1_1 : check w565 pick565 1 t10052 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k565_1_2 : check w565 pick565 1 t10053 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w565 pick565 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10052 k565_1_0 k565_1_1
private theorem k565_1_3 : check w565 pick565 1 t10054 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k565_1_4 : check w565 pick565 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k565_1_5 : check w565 pick565 1 t10059 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w565 pick565 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10054 t10058 k565_1_3 k565_1_4
private theorem k565_1_6 : check w565 pick565 1 t10060 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w565 pick565 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10053 t10059 k565_1_2 k565_1_5
private theorem k565_1_7 : check w565 pick565 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k565_1_8 : check w565 pick565 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k565_1_9 : check w565 pick565 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w565 pick565 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k565_1_7 k565_1_8
private theorem k565_1_10 : check w565 pick565 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k565_1_11 : check w565 pick565 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k565_1_12 : check w565 pick565 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w565 pick565 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k565_1_10 k565_1_11
private theorem k565_1_13 : check w565 pick565 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w565 pick565 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k565_1_9 k565_1_12
private theorem k565_1_14 : check w565 pick565 1 t10067 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w565 pick565 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10060 t10066 k565_1_6 k565_1_13
theorem cov565_1 : PA.Covered 1 (OZ.Valid 1 w565.low w565.t w565.y w565.r w565.cap) (P33.root 1) :=
  Night6836Tree.sound w565 pick565 1 t10067 _ k565_1_14
private theorem k565_2_0 : check w565 pick565 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k565_2_1 : check w565 pick565 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k565_2_2 : check w565 pick565 2 t3491 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w565 pick565 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3490 k565_2_0 k565_2_1
private theorem k565_2_3 : check w565 pick565 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k565_2_4 : check w565 pick565 2 t4155 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k565_2_5 : check w565 pick565 2 t4156 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w565 pick565 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4155 k565_2_3 k565_2_4
private theorem k565_2_6 : check w565 pick565 2 t4157 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w565 pick565 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3491 t4156 k565_2_2 k565_2_5
theorem cov565_2 : PA.Covered 2 (OZ.Valid 2 w565.low w565.t w565.y w565.r w565.cap) (P33.root 2) :=
  Night6836Tree.sound w565 pick565 2 t4157 _ k565_2_6
theorem cov565_3 : PA.Covered 3 (OZ.Valid 3 w565.low w565.t w565.y w565.r w565.cap) (P33.root 3) :=
  Night6836Tree.sound w565 pick565 3 t564 _ (by decide +kernel)
theorem cov565_4 : PA.Covered 4 (OZ.Valid 4 w565.low w565.t w565.y w565.r w565.cap) (P33.root 4) :=
  Night6836Tree.sound w565 pick565 4 t565 _ (by decide +kernel)
theorem cov565_5 : PA.Covered 5 (OZ.Valid 5 w565.low w565.t w565.y w565.r w565.cap) (P33.root 5) :=
  Night6836Tree.sound w565 pick565 5 t566 _ (by decide +kernel)
theorem cov565_6 : PA.Covered 6 (OZ.Valid 6 w565.low w565.t w565.y w565.r w565.cap) (P33.root 6) :=
  Night6836Tree.sound w565 pick565 6 t567 _ (by decide +kernel)
theorem cov565_7 : PA.Covered 7 (OZ.Valid 7 w565.low w565.t w565.y w565.r w565.cap) (P33.root 7) :=
  Night6836Tree.sound w565 pick565 7 t568 _ (by decide +kernel)
theorem window565 : P33.WindowCount w565 := by
  apply P33.window_count w565 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov565_1
  · exact cov565_2
  · exact cov565_3
  · exact cov565_4
  · exact cov565_5
  · exact cov565_6
  · exact cov565_7
def w566 : P33.Window := ⟨9,40,3639,2640,202839379450092526,69713,55000,5000000,81920000000⟩
def h566_0 : Height w566 := ⟨69713,55000,by decide +kernel⟩
def h566_1 : Height w566 := ⟨75204,51000,by decide +kernel⟩
def h566_2 : Height w566 := ⟨81616,47000,by decide +kernel⟩
def h566_3 : Height w566 := ⟨89367,43000,by decide +kernel⟩
def h566_4 : Height w566 := ⟨99173,39000,by decide +kernel⟩
def h566_5 : Height w566 := ⟨112367,35000,by decide +kernel⟩
def pick566 (cl : ℕ) : Height w566 := if cl<32 then (if cl<3 then (h566_0) else (if cl<10 then (h566_1) else (h566_2))) else (if cl<117 then (h566_3) else (if cl<491 then (h566_4) else (h566_5)))
private theorem k566_1_0 : check w566 pick566 1 t5236 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k566_1_1 : check w566 pick566 1 t11046 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k566_1_2 : check w566 pick566 1 t11047 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w566 pick566 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5236 t11046 k566_1_0 k566_1_1
private theorem k566_1_3 : check w566 pick566 1 t10879 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k566_1_4 : check w566 pick566 1 t10888 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k566_1_5 : check w566 pick566 1 t10889 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w566 pick566 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10879 t10888 k566_1_3 k566_1_4
private theorem k566_1_6 : check w566 pick566 1 t11048 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w566 pick566 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t11047 t10889 k566_1_2 k566_1_5
private theorem k566_1_7 : check w566 pick566 1 t10896 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k566_1_8 : check w566 pick566 1 t6586 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k566_1_9 : check w566 pick566 1 t10897 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w566 pick566 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10896 t6586 k566_1_7 k566_1_8
private theorem k566_1_10 : check w566 pick566 1 t6602 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k566_1_11 : check w566 pick566 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k566_1_12 : check w566 pick566 1 t10898 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w566 pick566 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6602 t10862 k566_1_10 k566_1_11
private theorem k566_1_13 : check w566 pick566 1 t10899 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w566 pick566 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10897 t10898 k566_1_9 k566_1_12
private theorem k566_1_14 : check w566 pick566 1 t11049 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w566 pick566 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t11048 t10899 k566_1_6 k566_1_13
theorem cov566_1 : PA.Covered 1 (OZ.Valid 1 w566.low w566.t w566.y w566.r w566.cap) (P33.root 1) :=
  Night6836Tree.sound w566 pick566 1 t11049 _ k566_1_14
theorem cov566_2 : PA.Covered 2 (OZ.Valid 2 w566.low w566.t w566.y w566.r w566.cap) (P33.root 2) :=
  Night6836Tree.sound w566 pick566 2 t11053 _ (by decide +kernel)
theorem cov566_3 : PA.Covered 3 (OZ.Valid 3 w566.low w566.t w566.y w566.r w566.cap) (P33.root 3) :=
  Night6836Tree.sound w566 pick566 3 t564 _ (by decide +kernel)
theorem cov566_4 : PA.Covered 4 (OZ.Valid 4 w566.low w566.t w566.y w566.r w566.cap) (P33.root 4) :=
  Night6836Tree.sound w566 pick566 4 t565 _ (by decide +kernel)
theorem cov566_5 : PA.Covered 5 (OZ.Valid 5 w566.low w566.t w566.y w566.r w566.cap) (P33.root 5) :=
  Night6836Tree.sound w566 pick566 5 t566 _ (by decide +kernel)
theorem cov566_6 : PA.Covered 6 (OZ.Valid 6 w566.low w566.t w566.y w566.r w566.cap) (P33.root 6) :=
  Night6836Tree.sound w566 pick566 6 t567 _ (by decide +kernel)
theorem cov566_7 : PA.Covered 7 (OZ.Valid 7 w566.low w566.t w566.y w566.r w566.cap) (P33.root 7) :=
  Night6836Tree.sound w566 pick566 7 t2134 _ (by decide +kernel)
theorem window566 : P33.WindowCount w566 := by
  apply P33.window_count w566 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov566_1
  · exact cov566_2
  · exact cov566_3
  · exact cov566_4
  · exact cov566_5
  · exact cov566_6
  · exact cov566_7
def w567 : P33.Window := ⟨9,40,4639,3640,203143846243063737,51772,39000,5000000,81920000000⟩
def h567_0 : Height w567 := ⟨51772,39000,by decide +kernel⟩
def h567_1 : Height w567 := ⟨57713,35000,by decide +kernel⟩
def h567_2 : Height w567 := ⟨65328,31000,by decide +kernel⟩
def h567_3 : Height w567 := ⟨75963,27000,by decide +kernel⟩
def pick567 (cl : ℕ) : Height w567 := if cl<32 then (if cl<5 then (h567_0) else (h567_1)) else (if cl<178 then (h567_2) else (h567_3))
private theorem k567_1_0 : check w567 pick567 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k567_1_1 : check w567 pick567 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k567_1_2 : check w567 pick567 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w567 pick567 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k567_1_0 k567_1_1
private theorem k567_1_3 : check w567 pick567 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k567_1_4 : check w567 pick567 1 t10042 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w567 pick567 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10023 k567_1_2 k567_1_3
private theorem k567_1_5 : check w567 pick567 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k567_1_6 : check w567 pick567 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k567_1_7 : check w567 pick567 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w567 pick567 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k567_1_5 k567_1_6
private theorem k567_1_8 : check w567 pick567 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k567_1_9 : check w567 pick567 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k567_1_10 : check w567 pick567 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w567 pick567 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k567_1_8 k567_1_9
private theorem k567_1_11 : check w567 pick567 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w567 pick567 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k567_1_7 k567_1_10
private theorem k567_1_12 : check w567 pick567 1 t10043 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w567 pick567 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10042 t10007 k567_1_4 k567_1_11
theorem cov567_1 : PA.Covered 1 (OZ.Valid 1 w567.low w567.t w567.y w567.r w567.cap) (P33.root 1) :=
  Night6836Tree.sound w567 pick567 1 t10043 _ k567_1_12
theorem cov567_2 : PA.Covered 2 (OZ.Valid 2 w567.low w567.t w567.y w567.r w567.cap) (P33.root 2) :=
  Night6836Tree.sound w567 pick567 2 t4654 _ (by decide +kernel)
theorem cov567_3 : PA.Covered 3 (OZ.Valid 3 w567.low w567.t w567.y w567.r w567.cap) (P33.root 3) :=
  Night6836Tree.sound w567 pick567 3 t564 _ (by decide +kernel)
theorem cov567_4 : PA.Covered 4 (OZ.Valid 4 w567.low w567.t w567.y w567.r w567.cap) (P33.root 4) :=
  Night6836Tree.sound w567 pick567 4 t565 _ (by decide +kernel)
theorem cov567_5 : PA.Covered 5 (OZ.Valid 5 w567.low w567.t w567.y w567.r w567.cap) (P33.root 5) :=
  Night6836Tree.sound w567 pick567 5 t566 _ (by decide +kernel)
theorem cov567_6 : PA.Covered 6 (OZ.Valid 6 w567.low w567.t w567.y w567.r w567.cap) (P33.root 6) :=
  Night6836Tree.sound w567 pick567 6 t567 _ (by decide +kernel)
theorem cov567_7 : PA.Covered 7 (OZ.Valid 7 w567.low w567.t w567.y w567.r w567.cap) (P33.root 7) :=
  Night6836Tree.sound w567 pick567 7 t2134 _ (by decide +kernel)
theorem window567 : P33.WindowCount w567 := by
  apply P33.window_count w567 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov567_1
  · exact cov567_2
  · exact cov567_3
  · exact cov567_4
  · exact cov567_5
  · exact cov567_6
  · exact cov567_7
def w568 : P33.Window := ⟨9,40,5739,4740,202074601159833747,38413,31000,5000000,81920000000⟩
def h568_0 : Height w568 := ⟨38413,31000,by decide +kernel⟩
def h568_1 : Height w568 := ⟨44150,27000,by decide +kernel⟩
def h568_2 : Height w568 := ⟨52079,23000,by decide +kernel⟩
def h568_3 : Height w568 := ⟨64924,19000,by decide +kernel⟩
def pick568 (cl : ℕ) : Height w568 := if cl<36 then (if cl<4 then (h568_0) else (h568_1)) else (if cl<342 then (h568_2) else (h568_3))
private theorem k568_1_0 : check w568 pick568 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k568_1_1 : check w568 pick568 1 t10052 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k568_1_2 : check w568 pick568 1 t10053 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w568 pick568 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10052 k568_1_0 k568_1_1
private theorem k568_1_3 : check w568 pick568 1 t10054 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k568_1_4 : check w568 pick568 1 t11059 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k568_1_5 : check w568 pick568 1 t11060 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w568 pick568 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10054 t11059 k568_1_3 k568_1_4
private theorem k568_1_6 : check w568 pick568 1 t11061 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w568 pick568 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10053 t11060 k568_1_2 k568_1_5
private theorem k568_1_7 : check w568 pick568 1 t11068 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k568_1_8 : check w568 pick568 1 t3840 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k568_1_9 : check w568 pick568 1 t11069 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w568 pick568 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t11068 t3840 k568_1_7 k568_1_8
private theorem k568_1_10 : check w568 pick568 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k568_1_11 : check w568 pick568 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k568_1_12 : check w568 pick568 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w568 pick568 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k568_1_10 k568_1_11
private theorem k568_1_13 : check w568 pick568 1 t11070 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w568 pick568 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t11069 t10065 k568_1_9 k568_1_12
private theorem k568_1_14 : check w568 pick568 1 t11071 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w568 pick568 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t11061 t11070 k568_1_6 k568_1_13
theorem cov568_1 : PA.Covered 1 (OZ.Valid 1 w568.low w568.t w568.y w568.r w568.cap) (P33.root 1) :=
  Night6836Tree.sound w568 pick568 1 t11071 _ k568_1_14
private theorem k568_2_0 : check w568 pick568 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k568_2_1 : check w568 pick568 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k568_2_2 : check w568 pick568 2 t3778 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w568 pick568 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3777 k568_2_0 k568_2_1
private theorem k568_2_3 : check w568 pick568 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k568_2_4 : check w568 pick568 2 t6001 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k568_2_5 : check w568 pick568 2 t6002 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w568 pick568 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t6001 k568_2_3 k568_2_4
private theorem k568_2_6 : check w568 pick568 2 t11072 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w568 pick568 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3778 t6002 k568_2_2 k568_2_5
theorem cov568_2 : PA.Covered 2 (OZ.Valid 2 w568.low w568.t w568.y w568.r w568.cap) (P33.root 2) :=
  Night6836Tree.sound w568 pick568 2 t11072 _ k568_2_6
theorem cov568_3 : PA.Covered 3 (OZ.Valid 3 w568.low w568.t w568.y w568.r w568.cap) (P33.root 3) :=
  Night6836Tree.sound w568 pick568 3 t564 _ (by decide +kernel)
theorem cov568_4 : PA.Covered 4 (OZ.Valid 4 w568.low w568.t w568.y w568.r w568.cap) (P33.root 4) :=
  Night6836Tree.sound w568 pick568 4 t565 _ (by decide +kernel)
theorem cov568_5 : PA.Covered 5 (OZ.Valid 5 w568.low w568.t w568.y w568.r w568.cap) (P33.root 5) :=
  Night6836Tree.sound w568 pick568 5 t566 _ (by decide +kernel)
theorem cov568_6 : PA.Covered 6 (OZ.Valid 6 w568.low w568.t w568.y w568.r w568.cap) (P33.root 6) :=
  Night6836Tree.sound w568 pick568 6 t567 _ (by decide +kernel)
theorem cov568_7 : PA.Covered 7 (OZ.Valid 7 w568.low w568.t w568.y w568.r w568.cap) (P33.root 7) :=
  Night6836Tree.sound w568 pick568 7 t2134 _ (by decide +kernel)
theorem window568 : P33.WindowCount w568 := by
  apply P33.window_count w568 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov568_1
  · exact cov568_2
  · exact cov568_3
  · exact cov568_4
  · exact cov568_5
  · exact cov568_6
  · exact cov568_7
def w569 : P33.Window := ⟨9,40,7176,7031,245763369836952260,25784,21000,5000000,81920000000⟩
def h569_0 : Height w569 := ⟨25784,21000,by decide +kernel⟩
def h569_1 : Height w569 := ⟨30125,18000,by decide +kernel⟩
def h569_2 : Height w569 := ⟨36436,15000,by decide +kernel⟩
def h569_3 : Height w569 := ⟨47839,12000,by decide +kernel⟩
def pick569 (cl : ℕ) : Height w569 := if cl<49 then (if cl<5 then (h569_0) else (h569_1)) else (if cl<853 then (h569_2) else (h569_3))
private theorem k569_1_0 : check w569 pick569 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k569_1_1 : check w569 pick569 1 t10052 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k569_1_2 : check w569 pick569 1 t10053 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w569 pick569 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10052 k569_1_0 k569_1_1
private theorem k569_1_3 : check w569 pick569 1 t11073 ⟨1,7,2,16,1,20,77,138⟩ = true := by decide +kernel
private theorem k569_1_4 : check w569 pick569 1 t10514 ⟨1,7,2,16,21,52,77,138⟩ = true := by decide +kernel
private theorem k569_1_5 : check w569 pick569 1 t11074 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w569 pick569 1 ⟨1,7,2,16,1,52,77,138⟩ 2 20 t11073 t10514 k569_1_3 k569_1_4
private theorem k569_1_6 : check w569 pick569 1 t11075 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w569 pick569 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t10053 t11074 k569_1_2 k569_1_5
private theorem k569_1_7 : check w569 pick569 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k569_1_8 : check w569 pick569 1 t3371 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k569_1_9 : check w569 pick569 1 t3372 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w569 pick569 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t3199 t3371 k569_1_7 k569_1_8
private theorem k569_1_10 : check w569 pick569 1 t11076 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k569_1_11 : check w569 pick569 1 t11078 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k569_1_12 : check w569 pick569 1 t11079 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w569 pick569 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t11076 t11078 k569_1_10 k569_1_11
private theorem k569_1_13 : check w569 pick569 1 t11080 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w569 pick569 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t3372 t11079 k569_1_9 k569_1_12
private theorem k569_1_14 : check w569 pick569 1 t11081 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w569 pick569 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t11075 t11080 k569_1_6 k569_1_13
theorem cov569_1 : PA.Covered 1 (OZ.Valid 1 w569.low w569.t w569.y w569.r w569.cap) (P33.root 1) :=
  Night6836Tree.sound w569 pick569 1 t11081 _ k569_1_14
private theorem k569_2_0 : check w569 pick569 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k569_2_1 : check w569 pick569 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k569_2_2 : check w569 pick569 2 t3491 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w569 pick569 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3490 k569_2_0 k569_2_1
private theorem k569_2_3 : check w569 pick569 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k569_2_4 : check w569 pick569 2 t4155 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k569_2_5 : check w569 pick569 2 t4156 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w569 pick569 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4155 k569_2_3 k569_2_4
private theorem k569_2_6 : check w569 pick569 2 t4157 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w569 pick569 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3491 t4156 k569_2_2 k569_2_5
theorem cov569_2 : PA.Covered 2 (OZ.Valid 2 w569.low w569.t w569.y w569.r w569.cap) (P33.root 2) :=
  Night6836Tree.sound w569 pick569 2 t4157 _ k569_2_6
theorem cov569_3 : PA.Covered 3 (OZ.Valid 3 w569.low w569.t w569.y w569.r w569.cap) (P33.root 3) :=
  Night6836Tree.sound w569 pick569 3 t564 _ (by decide +kernel)
theorem cov569_4 : PA.Covered 4 (OZ.Valid 4 w569.low w569.t w569.y w569.r w569.cap) (P33.root 4) :=
  Night6836Tree.sound w569 pick569 4 t565 _ (by decide +kernel)
theorem cov569_5 : PA.Covered 5 (OZ.Valid 5 w569.low w569.t w569.y w569.r w569.cap) (P33.root 5) :=
  Night6836Tree.sound w569 pick569 5 t566 _ (by decide +kernel)
theorem cov569_6 : PA.Covered 6 (OZ.Valid 6 w569.low w569.t w569.y w569.r w569.cap) (P33.root 6) :=
  Night6836Tree.sound w569 pick569 6 t567 _ (by decide +kernel)
theorem cov569_7 : PA.Covered 7 (OZ.Valid 7 w569.low w569.t w569.y w569.r w569.cap) (P33.root 7) :=
  Night6836Tree.sound w569 pick569 7 t568 _ (by decide +kernel)
theorem window569 : P33.WindowCount w569 := by
  apply P33.window_count w569 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov569_1
  · exact cov569_2
  · exact cov569_3
  · exact cov569_4
  · exact cov569_5
  · exact cov569_6
  · exact cov569_7
end ProximityPrize.SubmissionLower.Night6836Bank
