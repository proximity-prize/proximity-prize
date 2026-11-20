/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT03
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w450 : P33.Window := ⟨7,58,5719,5348,240929502086091806,53664,27000,5000000,81920000000⟩
def h450_0 : Height w450 := ⟨53664,27000,by decide +kernel⟩
def h450_1 : Height w450 := ⟨57932,24000,by decide +kernel⟩
def h450_2 : Height w450 := ⟨63341,21000,by decide +kernel⟩
def h450_3 : Height w450 := ⟨70778,18000,by decide +kernel⟩
def h450_4 : Height w450 := ⟨82367,15000,by decide +kernel⟩
def pick450 (cl : ℕ) : Height w450 := if cl<25 then (if cl<4 then (h450_0) else (h450_1)) else (if cl<126 then (h450_2) else (if cl<922 then (h450_3) else (h450_4)))
private theorem k450_1_0 : check w450 pick450 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k450_1_1 : check w450 pick450 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k450_1_2 : check w450 pick450 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w450 pick450 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k450_1_0 k450_1_1
private theorem k450_1_3 : check w450 pick450 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k450_1_4 : check w450 pick450 1 t9579 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k450_1_5 : check w450 pick450 1 t9580 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w450 pick450 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9579 k450_1_3 k450_1_4
private theorem k450_1_6 : check w450 pick450 1 t9581 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w450 pick450 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9580 k450_1_2 k450_1_5
private theorem k450_1_7 : check w450 pick450 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k450_1_8 : check w450 pick450 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k450_1_9 : check w450 pick450 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w450 pick450 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k450_1_7 k450_1_8
private theorem k450_1_10 : check w450 pick450 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k450_1_11 : check w450 pick450 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k450_1_12 : check w450 pick450 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w450 pick450 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k450_1_10 k450_1_11
private theorem k450_1_13 : check w450 pick450 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w450 pick450 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k450_1_9 k450_1_12
private theorem k450_1_14 : check w450 pick450 1 t9782 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w450 pick450 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9581 t9212 k450_1_6 k450_1_13
theorem cov450_1 : PA.Covered 1 (OZ.Valid 1 w450.low w450.t w450.y w450.r w450.cap) (P33.root 1) :=
  Night6836Tree.sound w450 pick450 1 t9782 _ k450_1_14
private theorem k450_2_0 : check w450 pick450 2 t9626 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k450_2_1 : check w450 pick450 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k450_2_2 : check w450 pick450 2 t9682 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w450 pick450 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9626 t9321 k450_2_0 k450_2_1
private theorem k450_2_3 : check w450 pick450 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k450_2_4 : check w450 pick450 2 t9382 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k450_2_5 : check w450 pick450 2 t9503 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w450 pick450 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t9382 k450_2_3 k450_2_4
private theorem k450_2_6 : check w450 pick450 2 t9797 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w450 pick450 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9682 t9503 k450_2_2 k450_2_5
theorem cov450_2 : PA.Covered 2 (OZ.Valid 2 w450.low w450.t w450.y w450.r w450.cap) (P33.root 2) :=
  Night6836Tree.sound w450 pick450 2 t9797 _ k450_2_6
theorem cov450_3 : PA.Covered 3 (OZ.Valid 3 w450.low w450.t w450.y w450.r w450.cap) (P33.root 3) :=
  Night6836Tree.sound w450 pick450 3 t564 _ (by decide +kernel)
theorem cov450_4 : PA.Covered 4 (OZ.Valid 4 w450.low w450.t w450.y w450.r w450.cap) (P33.root 4) :=
  Night6836Tree.sound w450 pick450 4 t565 _ (by decide +kernel)
theorem cov450_5 : PA.Covered 5 (OZ.Valid 5 w450.low w450.t w450.y w450.r w450.cap) (P33.root 5) :=
  Night6836Tree.sound w450 pick450 5 t566 _ (by decide +kernel)
theorem cov450_6 : PA.Covered 6 (OZ.Valid 6 w450.low w450.t w450.y w450.r w450.cap) (P33.root 6) :=
  Night6836Tree.sound w450 pick450 6 t567 _ (by decide +kernel)
theorem cov450_7 : PA.Covered 7 (OZ.Valid 7 w450.low w450.t w450.y w450.r w450.cap) (P33.root 7) :=
  Night6836Tree.sound w450 pick450 7 t2134 _ (by decide +kernel)
theorem window450 : P33.WindowCount w450 := by
  apply P33.window_count w450 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov450_1
  · exact cov450_2
  · exact cov450_3
  · exact cov450_4
  · exact cov450_5
  · exact cov450_6
  · exact cov450_7
def w451 : P33.Window := ⟨7,59,5347,4960,245495029798912593,58052,30000,5000000,81920000000⟩
def h451_0 : Height w451 := ⟨58052,30000,by decide +kernel⟩
def h451_1 : Height w451 := ⟨62107,27000,by decide +kernel⟩
def h451_2 : Height w451 := ⟨67061,24000,by decide +kernel⟩
def h451_3 : Height w451 := ⟨73489,21000,by decide +kernel⟩
def h451_4 : Height w451 := ⟨82584,18000,by decide +kernel⟩
def pick451 (cl : ℕ) : Height w451 := if cl<13 then (if cl<2 then (h451_0) else (h451_1)) else (if cl<55 then (h451_2) else (if cl<287 then (h451_3) else (h451_4)))
private theorem k451_1_0 : check w451 pick451 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k451_1_1 : check w451 pick451 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k451_1_2 : check w451 pick451 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w451 pick451 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k451_1_0 k451_1_1
private theorem k451_1_3 : check w451 pick451 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k451_1_4 : check w451 pick451 1 t9799 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k451_1_5 : check w451 pick451 1 t9800 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w451 pick451 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9799 k451_1_3 k451_1_4
private theorem k451_1_6 : check w451 pick451 1 t9801 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w451 pick451 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9800 k451_1_2 k451_1_5
private theorem k451_1_7 : check w451 pick451 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k451_1_8 : check w451 pick451 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k451_1_9 : check w451 pick451 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w451 pick451 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k451_1_7 k451_1_8
private theorem k451_1_10 : check w451 pick451 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k451_1_11 : check w451 pick451 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k451_1_12 : check w451 pick451 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w451 pick451 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k451_1_10 k451_1_11
private theorem k451_1_13 : check w451 pick451 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w451 pick451 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k451_1_9 k451_1_12
private theorem k451_1_14 : check w451 pick451 1 t9802 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w451 pick451 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9801 t9212 k451_1_6 k451_1_13
theorem cov451_1 : PA.Covered 1 (OZ.Valid 1 w451.low w451.t w451.y w451.r w451.cap) (P33.root 1) :=
  Night6836Tree.sound w451 pick451 1 t9802 _ k451_1_14
private theorem k451_2_0 : check w451 pick451 2 t5184 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k451_2_1 : check w451 pick451 2 t9806 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k451_2_2 : check w451 pick451 2 t9807 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w451 pick451 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5184 t9806 k451_2_0 k451_2_1
theorem cov451_2 : PA.Covered 2 (OZ.Valid 2 w451.low w451.t w451.y w451.r w451.cap) (P33.root 2) :=
  Night6836Tree.sound w451 pick451 2 t9807 _ k451_2_2
theorem cov451_3 : PA.Covered 3 (OZ.Valid 3 w451.low w451.t w451.y w451.r w451.cap) (P33.root 3) :=
  Night6836Tree.sound w451 pick451 3 t564 _ (by decide +kernel)
theorem cov451_4 : PA.Covered 4 (OZ.Valid 4 w451.low w451.t w451.y w451.r w451.cap) (P33.root 4) :=
  Night6836Tree.sound w451 pick451 4 t565 _ (by decide +kernel)
theorem cov451_5 : PA.Covered 5 (OZ.Valid 5 w451.low w451.t w451.y w451.r w451.cap) (P33.root 5) :=
  Night6836Tree.sound w451 pick451 5 t566 _ (by decide +kernel)
theorem cov451_6 : PA.Covered 6 (OZ.Valid 6 w451.low w451.t w451.y w451.r w451.cap) (P33.root 6) :=
  Night6836Tree.sound w451 pick451 6 t567 _ (by decide +kernel)
theorem cov451_7 : PA.Covered 7 (OZ.Valid 7 w451.low w451.t w451.y w451.r w451.cap) (P33.root 7) :=
  Night6836Tree.sound w451 pick451 7 t2134 _ (by decide +kernel)
theorem window451 : P33.WindowCount w451 := by
  apply P33.window_count w451 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov451_1
  · exact cov451_2
  · exact cov451_3
  · exact cov451_4
  · exact cov451_5
  · exact cov451_6
  · exact cov451_7
def w452 : P33.Window := ⟨7,60,4959,4557,244939055125236115,64173,33000,5000000,81920000000⟩
def h452_0 : Height w452 := ⟨64173,33000,by decide +kernel⟩
def h452_1 : Height w452 := ⟨68166,30000,by decide +kernel⟩
def h452_2 : Height w452 := ⟨72927,27000,by decide +kernel⟩
def h452_3 : Height w452 := ⟨78876,24000,by decide +kernel⟩
def h452_4 : Height w452 := ⟨86806,21000,by decide +kernel⟩
def h452_5 : Height w452 := ⟨98412,18000,by decide +kernel⟩
def pick452 (cl : ℕ) : Height w452 := if cl<36 then (if cl<2 then (h452_0) else (if cl<10 then (h452_1) else (h452_2))) else (if cl<172 then (h452_3) else (if cl<922 then (h452_4) else (h452_5)))
private theorem k452_1_0 : check w452 pick452 1 t5132 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k452_1_1 : check w452 pick452 1 t5141 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k452_1_2 : check w452 pick452 1 t5142 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w452 pick452 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5132 t5141 k452_1_0 k452_1_1
private theorem k452_1_3 : check w452 pick452 1 t9811 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k452_1_4 : check w452 pick452 1 t9824 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k452_1_5 : check w452 pick452 1 t9825 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w452 pick452 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t9811 t9824 k452_1_3 k452_1_4
private theorem k452_1_6 : check w452 pick452 1 t9826 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w452 pick452 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t5142 t9825 k452_1_2 k452_1_5
private theorem k452_1_7 : check w452 pick452 1 t5178 ⟨1,7,2,16,1,52,146,179⟩ = true := by decide +kernel
private theorem k452_1_8 : check w452 pick452 1 t2374 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k452_1_9 : check w452 pick452 1 t5179 ⟨1,7,2,16,1,52,146,206⟩ = true := glue w452 pick452 1 ⟨1,7,2,16,1,52,146,206⟩ 3 179 t5178 t2374 k452_1_7 k452_1_8
private theorem k452_1_10 : check w452 pick452 1 t2385 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k452_1_11 : check w452 pick452 1 t9150 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k452_1_12 : check w452 pick452 1 t9183 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w452 pick452 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t2385 t9150 k452_1_10 k452_1_11
private theorem k452_1_13 : check w452 pick452 1 t9184 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w452 pick452 1 ⟨1,7,2,16,1,52,146,450⟩ 3 206 t5179 t9183 k452_1_9 k452_1_12
private theorem k452_1_14 : check w452 pick452 1 t9827 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w452 pick452 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t9826 t9184 k452_1_6 k452_1_13
theorem cov452_1 : PA.Covered 1 (OZ.Valid 1 w452.low w452.t w452.y w452.r w452.cap) (P33.root 1) :=
  Night6836Tree.sound w452 pick452 1 t9827 _ k452_1_14
private theorem k452_2_0 : check w452 pick452 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k452_2_1 : check w452 pick452 2 t4017 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k452_2_2 : check w452 pick452 2 t4018 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w452 pick452 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t4017 k452_2_0 k452_2_1
theorem cov452_2 : PA.Covered 2 (OZ.Valid 2 w452.low w452.t w452.y w452.r w452.cap) (P33.root 2) :=
  Night6836Tree.sound w452 pick452 2 t4018 _ k452_2_2
theorem cov452_3 : PA.Covered 3 (OZ.Valid 3 w452.low w452.t w452.y w452.r w452.cap) (P33.root 3) :=
  Night6836Tree.sound w452 pick452 3 t564 _ (by decide +kernel)
theorem cov452_4 : PA.Covered 4 (OZ.Valid 4 w452.low w452.t w452.y w452.r w452.cap) (P33.root 4) :=
  Night6836Tree.sound w452 pick452 4 t565 _ (by decide +kernel)
theorem cov452_5 : PA.Covered 5 (OZ.Valid 5 w452.low w452.t w452.y w452.r w452.cap) (P33.root 5) :=
  Night6836Tree.sound w452 pick452 5 t566 _ (by decide +kernel)
theorem cov452_6 : PA.Covered 6 (OZ.Valid 6 w452.low w452.t w452.y w452.r w452.cap) (P33.root 6) :=
  Night6836Tree.sound w452 pick452 6 t567 _ (by decide +kernel)
theorem cov452_7 : PA.Covered 7 (OZ.Valid 7 w452.low w452.t w452.y w452.r w452.cap) (P33.root 7) :=
  Night6836Tree.sound w452 pick452 7 t2134 _ (by decide +kernel)
theorem window452 : P33.WindowCount w452 := by
  apply P33.window_count w452 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov452_1
  · exact cov452_2
  · exact cov452_3
  · exact cov452_4
  · exact cov452_5
  · exact cov452_6
  · exact cov452_7
def w453 : P33.Window := ⟨7,61,4556,4140,237862668863681105,72597,36000,5000000,81920000000⟩
def h453_0 : Height w453 := ⟨72597,36000,by decide +kernel⟩
def h453_1 : Height w453 := ⟨76661,33000,by decide +kernel⟩
def h453_2 : Height w453 := ⟨81433,30000,by decide +kernel⟩
def h453_3 : Height w453 := ⟨87254,27000,by decide +kernel⟩
def h453_4 : Height w453 := ⟨94722,24000,by decide +kernel⟩
def h453_5 : Height w453 := ⟨104998,21000,by decide +kernel⟩
def pick453 (cl : ℕ) : Height w453 := if cl<32 then (if cl<2 then (h453_0) else (if cl<10 then (h453_1) else (h453_2))) else (if cl<132 then (h453_3) else (if cl<615 then (h453_4) else (h453_5)))
private theorem k453_1_0 : check w453 pick453 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k453_1_1 : check w453 pick453 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k453_1_2 : check w453 pick453 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w453 pick453 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k453_1_0 k453_1_1
private theorem k453_1_3 : check w453 pick453 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k453_1_4 : check w453 pick453 1 t9829 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k453_1_5 : check w453 pick453 1 t9830 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w453 pick453 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9829 k453_1_3 k453_1_4
private theorem k453_1_6 : check w453 pick453 1 t9831 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w453 pick453 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9830 k453_1_2 k453_1_5
private theorem k453_1_7 : check w453 pick453 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k453_1_8 : check w453 pick453 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k453_1_9 : check w453 pick453 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w453 pick453 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k453_1_7 k453_1_8
private theorem k453_1_10 : check w453 pick453 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k453_1_11 : check w453 pick453 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k453_1_12 : check w453 pick453 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w453 pick453 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k453_1_10 k453_1_11
private theorem k453_1_13 : check w453 pick453 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w453 pick453 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k453_1_9 k453_1_12
private theorem k453_1_14 : check w453 pick453 1 t9832 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w453 pick453 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9831 t9097 k453_1_6 k453_1_13
theorem cov453_1 : PA.Covered 1 (OZ.Valid 1 w453.low w453.t w453.y w453.r w453.cap) (P33.root 1) :=
  Night6836Tree.sound w453 pick453 1 t9832 _ k453_1_14
theorem cov453_2 : PA.Covered 2 (OZ.Valid 2 w453.low w453.t w453.y w453.r w453.cap) (P33.root 2) :=
  Night6836Tree.sound w453 pick453 2 t4654 _ (by decide +kernel)
theorem cov453_3 : PA.Covered 3 (OZ.Valid 3 w453.low w453.t w453.y w453.r w453.cap) (P33.root 3) :=
  Night6836Tree.sound w453 pick453 3 t564 _ (by decide +kernel)
theorem cov453_4 : PA.Covered 4 (OZ.Valid 4 w453.low w453.t w453.y w453.r w453.cap) (P33.root 4) :=
  Night6836Tree.sound w453 pick453 4 t565 _ (by decide +kernel)
theorem cov453_5 : PA.Covered 5 (OZ.Valid 5 w453.low w453.t w453.y w453.r w453.cap) (P33.root 5) :=
  Night6836Tree.sound w453 pick453 5 t566 _ (by decide +kernel)
theorem cov453_6 : PA.Covered 6 (OZ.Valid 6 w453.low w453.t w453.y w453.r w453.cap) (P33.root 6) :=
  Night6836Tree.sound w453 pick453 6 t567 _ (by decide +kernel)
theorem cov453_7 : PA.Covered 7 (OZ.Valid 7 w453.low w453.t w453.y w453.r w453.cap) (P33.root 7) :=
  Night6836Tree.sound w453 pick453 7 t2134 _ (by decide +kernel)
theorem window453 : P33.WindowCount w453 := by
  apply P33.window_count w453 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov453_1
  · exact cov453_2
  · exact cov453_3
  · exact cov453_4
  · exact cov453_5
  · exact cov453_6
  · exact cov453_7
def w454 : P33.Window := ⟨7,62,4139,3707,244234100171495838,84382,39000,5000000,81920000000⟩
def h454_0 : Height w454 := ⟨84382,39000,by decide +kernel⟩
def h454_1 : Height w454 := ⟨88677,36000,by decide +kernel⟩
def h454_2 : Height w454 := ⟨93677,33000,by decide +kernel⟩
def h454_3 : Height w454 := ⟨99687,30000,by decide +kernel⟩
def h454_4 : Height w454 := ⟨107216,27000,by decide +kernel⟩
def h454_5 : Height w454 := ⟨117187,24000,by decide +kernel⟩
def pick454 (cl : ℕ) : Height w454 := if cl<40 then (if cl<4 then (h454_0) else (if cl<16 then (h454_1) else (h454_2))) else (if cl<136 then (h454_3) else (if cl<498 then (h454_4) else (h454_5)))
private theorem k454_1_0 : check w454 pick454 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k454_1_1 : check w454 pick454 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k454_1_2 : check w454 pick454 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w454 pick454 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k454_1_0 k454_1_1
private theorem k454_1_3 : check w454 pick454 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k454_1_4 : check w454 pick454 1 t9829 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k454_1_5 : check w454 pick454 1 t9830 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w454 pick454 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9829 k454_1_3 k454_1_4
private theorem k454_1_6 : check w454 pick454 1 t9831 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w454 pick454 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9830 k454_1_2 k454_1_5
private theorem k454_1_7 : check w454 pick454 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k454_1_8 : check w454 pick454 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k454_1_9 : check w454 pick454 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w454 pick454 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k454_1_7 k454_1_8
private theorem k454_1_10 : check w454 pick454 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k454_1_11 : check w454 pick454 1 t5274 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k454_1_12 : check w454 pick454 1 t9519 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w454 pick454 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t5274 k454_1_10 k454_1_11
private theorem k454_1_13 : check w454 pick454 1 t9520 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w454 pick454 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9519 k454_1_9 k454_1_12
private theorem k454_1_14 : check w454 pick454 1 t9833 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w454 pick454 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9831 t9520 k454_1_6 k454_1_13
theorem cov454_1 : PA.Covered 1 (OZ.Valid 1 w454.low w454.t w454.y w454.r w454.cap) (P33.root 1) :=
  Night6836Tree.sound w454 pick454 1 t9833 _ k454_1_14
theorem cov454_2 : PA.Covered 2 (OZ.Valid 2 w454.low w454.t w454.y w454.r w454.cap) (P33.root 2) :=
  Night6836Tree.sound w454 pick454 2 t4274 _ (by decide +kernel)
theorem cov454_3 : PA.Covered 3 (OZ.Valid 3 w454.low w454.t w454.y w454.r w454.cap) (P33.root 3) :=
  Night6836Tree.sound w454 pick454 3 t564 _ (by decide +kernel)
theorem cov454_4 : PA.Covered 4 (OZ.Valid 4 w454.low w454.t w454.y w454.r w454.cap) (P33.root 4) :=
  Night6836Tree.sound w454 pick454 4 t565 _ (by decide +kernel)
theorem cov454_5 : PA.Covered 5 (OZ.Valid 5 w454.low w454.t w454.y w454.r w454.cap) (P33.root 5) :=
  Night6836Tree.sound w454 pick454 5 t566 _ (by decide +kernel)
theorem cov454_6 : PA.Covered 6 (OZ.Valid 6 w454.low w454.t w454.y w454.r w454.cap) (P33.root 6) :=
  Night6836Tree.sound w454 pick454 6 t567 _ (by decide +kernel)
theorem cov454_7 : PA.Covered 7 (OZ.Valid 7 w454.low w454.t w454.y w454.r w454.cap) (P33.root 7) :=
  Night6836Tree.sound w454 pick454 7 t2134 _ (by decide +kernel)
theorem window454 : P33.WindowCount w454 := by
  apply P33.window_count w454 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov454_1
  · exact cov454_2
  · exact cov454_3
  · exact cov454_4
  · exact cov454_5
  · exact cov454_6
  · exact cov454_7
def w455 : P33.Window := ⟨7,63,3706,3259,238707098228485210,97106,45000,5000000,81920000000⟩
def h455_0 : Height w455 := ⟨97106,45000,by decide +kernel⟩
def h455_1 : Height w455 := ⟨101295,42000,by decide +kernel⟩
def h455_2 : Height w455 := ⟨106049,39000,by decide +kernel⟩
def h455_3 : Height w455 := ⟨111567,36000,by decide +kernel⟩
def h455_4 : Height w455 := ⟨118153,33000,by decide +kernel⟩
def h455_5 : Height w455 := ⟨126297,30000,by decide +kernel⟩
def h455_6 : Height w455 := ⟨136841,27000,by decide +kernel⟩
def pick455 (cl : ℕ) : Height w455 := if cl<32 then (if cl<4 then (h455_0) else (if cl<10 then (h455_1) else (h455_2))) else (if cl<201 then (if cl<62 then (h455_3) else (h455_4)) else (if cl<732 then (h455_5) else (h455_6)))
private theorem k455_1_0 : check w455 pick455 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k455_1_1 : check w455 pick455 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k455_1_2 : check w455 pick455 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w455 pick455 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k455_1_0 k455_1_1
private theorem k455_1_3 : check w455 pick455 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k455_1_4 : check w455 pick455 1 t9829 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k455_1_5 : check w455 pick455 1 t9830 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w455 pick455 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9829 k455_1_3 k455_1_4
private theorem k455_1_6 : check w455 pick455 1 t9831 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w455 pick455 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9830 k455_1_2 k455_1_5
private theorem k455_1_7 : check w455 pick455 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k455_1_8 : check w455 pick455 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k455_1_9 : check w455 pick455 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w455 pick455 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k455_1_7 k455_1_8
private theorem k455_1_10 : check w455 pick455 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k455_1_11 : check w455 pick455 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w455 pick455 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k455_1_9 k455_1_10
private theorem k455_1_12 : check w455 pick455 1 t9834 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w455 pick455 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9831 t5276 k455_1_6 k455_1_11
theorem cov455_1 : PA.Covered 1 (OZ.Valid 1 w455.low w455.t w455.y w455.r w455.cap) (P33.root 1) :=
  Night6836Tree.sound w455 pick455 1 t9834 _ k455_1_12
theorem cov455_2 : PA.Covered 2 (OZ.Valid 2 w455.low w455.t w455.y w455.r w455.cap) (P33.root 2) :=
  Night6836Tree.sound w455 pick455 2 t9836 _ (by decide +kernel)
theorem cov455_3 : PA.Covered 3 (OZ.Valid 3 w455.low w455.t w455.y w455.r w455.cap) (P33.root 3) :=
  Night6836Tree.sound w455 pick455 3 t564 _ (by decide +kernel)
theorem cov455_4 : PA.Covered 4 (OZ.Valid 4 w455.low w455.t w455.y w455.r w455.cap) (P33.root 4) :=
  Night6836Tree.sound w455 pick455 4 t565 _ (by decide +kernel)
theorem cov455_5 : PA.Covered 5 (OZ.Valid 5 w455.low w455.t w455.y w455.r w455.cap) (P33.root 5) :=
  Night6836Tree.sound w455 pick455 5 t566 _ (by decide +kernel)
theorem cov455_6 : PA.Covered 6 (OZ.Valid 6 w455.low w455.t w455.y w455.r w455.cap) (P33.root 6) :=
  Night6836Tree.sound w455 pick455 6 t567 _ (by decide +kernel)
theorem cov455_7 : PA.Covered 7 (OZ.Valid 7 w455.low w455.t w455.y w455.r w455.cap) (P33.root 7) :=
  Night6836Tree.sound w455 pick455 7 t2134 _ (by decide +kernel)
theorem window455 : P33.WindowCount w455 := by
  apply P33.window_count w455 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov455_1
  · exact cov455_2
  · exact cov455_3
  · exact cov455_4
  · exact cov455_5
  · exact cov455_6
  · exact cov455_7
def w456 : P33.Window := ⟨7,64,3258,2795,217454362030475828,113516,54000,5000000,81920000000⟩
def h456_0 : Height w456 := ⟨113516,54000,by decide +kernel⟩
def h456_1 : Height w456 := ⟨117503,51000,by decide +kernel⟩
def h456_2 : Height w456 := ⟨121906,48000,by decide +kernel⟩
def h456_3 : Height w456 := ⟨126839,45000,by decide +kernel⟩
def h456_4 : Height w456 := ⟨132461,42000,by decide +kernel⟩
def h456_5 : Height w456 := ⟨139002,39000,by decide +kernel⟩
def h456_6 : Height w456 := ⟨146807,36000,by decide +kernel⟩
def h456_7 : Height w456 := ⟨156417,33000,by decide +kernel⟩
def pick456 (cl : ℕ) : Height w456 := if cl<32 then (if cl<5 then (if cl<2 then (h456_0) else (h456_1)) else (if cl<13 then (h456_2) else (h456_3))) else (if cl<172 then (if cl<62 then (h456_4) else (h456_5)) else (if cl<337 then (h456_6) else (h456_7)))
private theorem k456_1_0 : check w456 pick456 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k456_1_1 : check w456 pick456 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k456_1_2 : check w456 pick456 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w456 pick456 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k456_1_0 k456_1_1
private theorem k456_1_3 : check w456 pick456 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k456_1_4 : check w456 pick456 1 t9829 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k456_1_5 : check w456 pick456 1 t9830 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w456 pick456 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9829 k456_1_3 k456_1_4
private theorem k456_1_6 : check w456 pick456 1 t9831 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w456 pick456 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9830 k456_1_2 k456_1_5
private theorem k456_1_7 : check w456 pick456 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k456_1_8 : check w456 pick456 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k456_1_9 : check w456 pick456 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w456 pick456 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k456_1_7 k456_1_8
private theorem k456_1_10 : check w456 pick456 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k456_1_11 : check w456 pick456 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w456 pick456 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k456_1_9 k456_1_10
private theorem k456_1_12 : check w456 pick456 1 t9834 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w456 pick456 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9831 t5276 k456_1_6 k456_1_11
theorem cov456_1 : PA.Covered 1 (OZ.Valid 1 w456.low w456.t w456.y w456.r w456.cap) (P33.root 1) :=
  Night6836Tree.sound w456 pick456 1 t9834 _ k456_1_12
theorem cov456_2 : PA.Covered 2 (OZ.Valid 2 w456.low w456.t w456.y w456.r w456.cap) (P33.root 2) :=
  Night6836Tree.sound w456 pick456 2 t5222 _ (by decide +kernel)
theorem cov456_3 : PA.Covered 3 (OZ.Valid 3 w456.low w456.t w456.y w456.r w456.cap) (P33.root 3) :=
  Night6836Tree.sound w456 pick456 3 t564 _ (by decide +kernel)
theorem cov456_4 : PA.Covered 4 (OZ.Valid 4 w456.low w456.t w456.y w456.r w456.cap) (P33.root 4) :=
  Night6836Tree.sound w456 pick456 4 t565 _ (by decide +kernel)
theorem cov456_5 : PA.Covered 5 (OZ.Valid 5 w456.low w456.t w456.y w456.r w456.cap) (P33.root 5) :=
  Night6836Tree.sound w456 pick456 5 t566 _ (by decide +kernel)
theorem cov456_6 : PA.Covered 6 (OZ.Valid 6 w456.low w456.t w456.y w456.r w456.cap) (P33.root 6) :=
  Night6836Tree.sound w456 pick456 6 t567 _ (by decide +kernel)
theorem cov456_7 : PA.Covered 7 (OZ.Valid 7 w456.low w456.t w456.y w456.r w456.cap) (P33.root 7) :=
  Night6836Tree.sound w456 pick456 7 t2134 _ (by decide +kernel)
theorem window456 : P33.WindowCount w456 := by
  apply P33.window_count w456 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov456_1
  · exact cov456_2
  · exact cov456_3
  · exact cov456_4
  · exact cov456_5
  · exact cov456_6
  · exact cov456_7
def w457 : P33.Window := ⟨7,65,2794,2378,208128675480852554,136661,63000,5000000,81920000000⟩
def h457_0 : Height w457 := ⟨136661,63000,by decide +kernel⟩
def h457_1 : Height w457 := ⟨140698,60000,by decide +kernel⟩
def h457_2 : Height w457 := ⟨145091,57000,by decide +kernel⟩
def h457_3 : Height w457 := ⟨149919,54000,by decide +kernel⟩
def h457_4 : Height w457 := ⟨155289,51000,by decide +kernel⟩
def h457_5 : Height w457 := ⟨161345,48000,by decide +kernel⟩
def h457_6 : Height w457 := ⟨168285,45000,by decide +kernel⟩
def h457_7 : Height w457 := ⟨176394,42000,by decide +kernel⟩
def h457_8 : Height w457 := ⟨186093,39000,by decide +kernel⟩
def pick457 (cl : ℕ) : Height w457 := if cl<32 then (if cl<5 then (if cl<2 then (h457_0) else (h457_1)) else (if cl<10 then (h457_2) else (h457_3))) else (if cl<92 then (if cl<40 then (h457_4) else (h457_5)) else (if cl<197 then (h457_6) else (if cl<360 then (h457_7) else (h457_8))))
private theorem k457_1_0 : check w457 pick457 1 t9843 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k457_1_1 : check w457 pick457 1 t9846 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k457_1_2 : check w457 pick457 1 t9847 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w457 pick457 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t9843 t9846 k457_1_0 k457_1_1
private theorem k457_1_3 : check w457 pick457 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k457_1_4 : check w457 pick457 1 t9829 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k457_1_5 : check w457 pick457 1 t9830 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w457 pick457 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9829 k457_1_3 k457_1_4
private theorem k457_1_6 : check w457 pick457 1 t9848 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w457 pick457 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9847 t9830 k457_1_2 k457_1_5
private theorem k457_1_7 : check w457 pick457 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k457_1_8 : check w457 pick457 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k457_1_9 : check w457 pick457 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w457 pick457 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k457_1_7 k457_1_8
private theorem k457_1_10 : check w457 pick457 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k457_1_11 : check w457 pick457 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w457 pick457 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k457_1_9 k457_1_10
private theorem k457_1_12 : check w457 pick457 1 t9849 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w457 pick457 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9848 t5276 k457_1_6 k457_1_11
theorem cov457_1 : PA.Covered 1 (OZ.Valid 1 w457.low w457.t w457.y w457.r w457.cap) (P33.root 1) :=
  Night6836Tree.sound w457 pick457 1 t9849 _ k457_1_12
theorem cov457_2 : PA.Covered 2 (OZ.Valid 2 w457.low w457.t w457.y w457.r w457.cap) (P33.root 2) :=
  Night6836Tree.sound w457 pick457 2 t5222 _ (by decide +kernel)
theorem cov457_3 : PA.Covered 3 (OZ.Valid 3 w457.low w457.t w457.y w457.r w457.cap) (P33.root 3) :=
  Night6836Tree.sound w457 pick457 3 t564 _ (by decide +kernel)
theorem cov457_4 : PA.Covered 4 (OZ.Valid 4 w457.low w457.t w457.y w457.r w457.cap) (P33.root 4) :=
  Night6836Tree.sound w457 pick457 4 t565 _ (by decide +kernel)
theorem cov457_5 : PA.Covered 5 (OZ.Valid 5 w457.low w457.t w457.y w457.r w457.cap) (P33.root 5) :=
  Night6836Tree.sound w457 pick457 5 t566 _ (by decide +kernel)
theorem cov457_6 : PA.Covered 6 (OZ.Valid 6 w457.low w457.t w457.y w457.r w457.cap) (P33.root 6) :=
  Night6836Tree.sound w457 pick457 6 t567 _ (by decide +kernel)
theorem cov457_7 : PA.Covered 7 (OZ.Valid 7 w457.low w457.t w457.y w457.r w457.cap) (P33.root 7) :=
  Night6836Tree.sound w457 pick457 7 t2134 _ (by decide +kernel)
theorem window457 : P33.WindowCount w457 := by
  apply P33.window_count w457 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov457_1
  · exact cov457_2
  · exact cov457_3
  · exact cov457_4
  · exact cov457_5
  · exact cov457_6
  · exact cov457_7
def w458 : P33.Window := ⟨8,22,8121,7122,198746562460649910,12692,15000,5000000,81920000000⟩
def h458_0 : Height w458 := ⟨12692,15000,by decide +kernel⟩
def h458_1 : Height w458 := ⟨20278,11000,by decide +kernel⟩
def pick458 (cl : ℕ) : Height w458 := if cl<32 then (h458_0) else (h458_1)
private theorem k458_1_0 : check w458 pick458 1 t3036 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k458_1_1 : check w458 pick458 1 t9864 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k458_1_2 : check w458 pick458 1 t9865 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w458 pick458 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3036 t9864 k458_1_0 k458_1_1
private theorem k458_1_3 : check w458 pick458 1 t9886 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k458_1_4 : check w458 pick458 1 t9900 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k458_1_5 : check w458 pick458 1 t9901 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w458 pick458 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t9886 t9900 k458_1_3 k458_1_4
private theorem k458_1_6 : check w458 pick458 1 t9902 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w458 pick458 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t9865 t9901 k458_1_2 k458_1_5
private theorem k458_1_7 : check w458 pick458 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k458_1_8 : check w458 pick458 1 t9910 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k458_1_9 : check w458 pick458 1 t9911 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w458 pick458 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t9910 k458_1_7 k458_1_8
private theorem k458_1_10 : check w458 pick458 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k458_1_11 : check w458 pick458 1 t9930 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k458_1_12 : check w458 pick458 1 t9931 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w458 pick458 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t9930 k458_1_10 k458_1_11
private theorem k458_1_13 : check w458 pick458 1 t9932 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w458 pick458 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t9911 t9931 k458_1_9 k458_1_12
private theorem k458_1_14 : check w458 pick458 1 t9933 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w458 pick458 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t9902 t9932 k458_1_6 k458_1_13
theorem cov458_1 : PA.Covered 1 (OZ.Valid 1 w458.low w458.t w458.y w458.r w458.cap) (P33.root 1) :=
  Night6836Tree.sound w458 pick458 1 t9933 _ k458_1_14
private theorem k458_2_0 : check w458 pick458 2 t9983 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k458_2_1 : check w458 pick458 2 t7376 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k458_2_2 : check w458 pick458 2 t9984 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w458 pick458 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t9983 t7376 k458_2_0 k458_2_1
theorem cov458_2 : PA.Covered 2 (OZ.Valid 2 w458.low w458.t w458.y w458.r w458.cap) (P33.root 2) :=
  Night6836Tree.sound w458 pick458 2 t9984 _ k458_2_2
theorem cov458_3 : PA.Covered 3 (OZ.Valid 3 w458.low w458.t w458.y w458.r w458.cap) (P33.root 3) :=
  Night6836Tree.sound w458 pick458 3 t564 _ (by decide +kernel)
theorem cov458_4 : PA.Covered 4 (OZ.Valid 4 w458.low w458.t w458.y w458.r w458.cap) (P33.root 4) :=
  Night6836Tree.sound w458 pick458 4 t565 _ (by decide +kernel)
theorem cov458_5 : PA.Covered 5 (OZ.Valid 5 w458.low w458.t w458.y w458.r w458.cap) (P33.root 5) :=
  Night6836Tree.sound w458 pick458 5 t566 _ (by decide +kernel)
theorem cov458_6 : PA.Covered 6 (OZ.Valid 6 w458.low w458.t w458.y w458.r w458.cap) (P33.root 6) :=
  Night6836Tree.sound w458 pick458 6 t567 _ (by decide +kernel)
theorem cov458_7 : PA.Covered 7 (OZ.Valid 7 w458.low w458.t w458.y w458.r w458.cap) (P33.root 7) :=
  Night6836Tree.sound w458 pick458 7 t568 _ (by decide +kernel)
theorem window458 : P33.WindowCount w458 := by
  apply P33.window_count w458 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov458_1
  · exact cov458_2
  · exact cov458_3
  · exact cov458_4
  · exact cov458_5
  · exact cov458_6
  · exact cov458_7
def w459 : P33.Window := ⟨8,23,7990,7957,218653082421555809,10453,15000,5000000,81920000000⟩
def h459_0 : Height w459 := ⟨10453,15000,by decide +kernel⟩
def h459_1 : Height w459 := ⟨14532,12000,by decide +kernel⟩
def h459_2 : Height w459 := ⟨22483,9000,by decide +kernel⟩
def pick459 (cl : ℕ) : Height w459 := if cl<2 then (h459_0) else (if cl<175 then (h459_1) else (h459_2))
private theorem k459_1_0 : check w459 pick459 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k459_1_1 : check w459 pick459 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k459_1_2 : check w459 pick459 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w459 pick459 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k459_1_0 k459_1_1
private theorem k459_1_3 : check w459 pick459 1 t9998 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k459_1_4 : check w459 pick459 1 t9999 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w459 pick459 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t9998 k459_1_2 k459_1_3
private theorem k459_1_5 : check w459 pick459 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k459_1_6 : check w459 pick459 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k459_1_7 : check w459 pick459 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w459 pick459 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k459_1_5 k459_1_6
private theorem k459_1_8 : check w459 pick459 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k459_1_9 : check w459 pick459 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k459_1_10 : check w459 pick459 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w459 pick459 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k459_1_8 k459_1_9
private theorem k459_1_11 : check w459 pick459 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w459 pick459 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k459_1_7 k459_1_10
private theorem k459_1_12 : check w459 pick459 1 t10008 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w459 pick459 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9999 t10007 k459_1_4 k459_1_11
theorem cov459_1 : PA.Covered 1 (OZ.Valid 1 w459.low w459.t w459.y w459.r w459.cap) (P33.root 1) :=
  Night6836Tree.sound w459 pick459 1 t10008 _ k459_1_12
theorem cov459_2 : PA.Covered 2 (OZ.Valid 2 w459.low w459.t w459.y w459.r w459.cap) (P33.root 2) :=
  Night6836Tree.sound w459 pick459 2 t10022 _ (by decide +kernel)
theorem cov459_3 : PA.Covered 3 (OZ.Valid 3 w459.low w459.t w459.y w459.r w459.cap) (P33.root 3) :=
  Night6836Tree.sound w459 pick459 3 t564 _ (by decide +kernel)
theorem cov459_4 : PA.Covered 4 (OZ.Valid 4 w459.low w459.t w459.y w459.r w459.cap) (P33.root 4) :=
  Night6836Tree.sound w459 pick459 4 t565 _ (by decide +kernel)
theorem cov459_5 : PA.Covered 5 (OZ.Valid 5 w459.low w459.t w459.y w459.r w459.cap) (P33.root 5) :=
  Night6836Tree.sound w459 pick459 5 t566 _ (by decide +kernel)
theorem cov459_6 : PA.Covered 6 (OZ.Valid 6 w459.low w459.t w459.y w459.r w459.cap) (P33.root 6) :=
  Night6836Tree.sound w459 pick459 6 t567 _ (by decide +kernel)
theorem cov459_7 : PA.Covered 7 (OZ.Valid 7 w459.low w459.t w459.y w459.r w459.cap) (P33.root 7) :=
  Night6836Tree.sound w459 pick459 7 t568 _ (by decide +kernel)
theorem window459 : P33.WindowCount w459 := by
  apply P33.window_count w459 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov459_1
  · exact cov459_2
  · exact cov459_3
  · exact cov459_4
  · exact cov459_5
  · exact cov459_6
  · exact cov459_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w460 : P33.Window := ⟨8,24,6923,5924,194500988274907329,16672,19000,5000000,81920000000⟩
def h460_0 : Height w460 := ⟨16672,19000,by decide +kernel⟩
def h460_1 : Height w460 := ⟨23157,15000,by decide +kernel⟩
def h460_2 : Height w460 := ⟨37985,11000,by decide +kernel⟩
def pick460 (cl : ℕ) : Height w460 := if cl<12 then (h460_0) else (if cl<925 then (h460_1) else (h460_2))
private theorem k460_1_0 : check w460 pick460 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k460_1_1 : check w460 pick460 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k460_1_2 : check w460 pick460 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w460 pick460 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k460_1_0 k460_1_1
private theorem k460_1_3 : check w460 pick460 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k460_1_4 : check w460 pick460 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w460 pick460 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k460_1_2 k460_1_3
private theorem k460_1_5 : check w460 pick460 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k460_1_6 : check w460 pick460 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k460_1_7 : check w460 pick460 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w460 pick460 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k460_1_5 k460_1_6
private theorem k460_1_8 : check w460 pick460 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k460_1_9 : check w460 pick460 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k460_1_10 : check w460 pick460 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w460 pick460 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k460_1_8 k460_1_9
private theorem k460_1_11 : check w460 pick460 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w460 pick460 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k460_1_7 k460_1_10
private theorem k460_1_12 : check w460 pick460 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w460 pick460 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k460_1_4 k460_1_11
theorem cov460_1 : PA.Covered 1 (OZ.Valid 1 w460.low w460.t w460.y w460.r w460.cap) (P33.root 1) :=
  Night6836Tree.sound w460 pick460 1 t10025 _ k460_1_12
theorem cov460_2 : PA.Covered 2 (OZ.Valid 2 w460.low w460.t w460.y w460.r w460.cap) (P33.root 2) :=
  Night6836Tree.sound w460 pick460 2 t10022 _ (by decide +kernel)
theorem cov460_3 : PA.Covered 3 (OZ.Valid 3 w460.low w460.t w460.y w460.r w460.cap) (P33.root 3) :=
  Night6836Tree.sound w460 pick460 3 t564 _ (by decide +kernel)
theorem cov460_4 : PA.Covered 4 (OZ.Valid 4 w460.low w460.t w460.y w460.r w460.cap) (P33.root 4) :=
  Night6836Tree.sound w460 pick460 4 t565 _ (by decide +kernel)
theorem cov460_5 : PA.Covered 5 (OZ.Valid 5 w460.low w460.t w460.y w460.r w460.cap) (P33.root 5) :=
  Night6836Tree.sound w460 pick460 5 t566 _ (by decide +kernel)
theorem cov460_6 : PA.Covered 6 (OZ.Valid 6 w460.low w460.t w460.y w460.r w460.cap) (P33.root 6) :=
  Night6836Tree.sound w460 pick460 6 t567 _ (by decide +kernel)
theorem cov460_7 : PA.Covered 7 (OZ.Valid 7 w460.low w460.t w460.y w460.r w460.cap) (P33.root 7) :=
  Night6836Tree.sound w460 pick460 7 t568 _ (by decide +kernel)
theorem window460 : P33.WindowCount w460 := by
  apply P33.window_count w460 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov460_1
  · exact cov460_2
  · exact cov460_3
  · exact cov460_4
  · exact cov460_5
  · exact cov460_6
  · exact cov460_7
def w461 : P33.Window := ⟨8,24,7956,7922,223442926425277526,11522,15000,5000000,81920000000⟩
def h461_0 : Height w461 := ⟨11522,15000,by decide +kernel⟩
def h461_1 : Height w461 := ⟨15776,12000,by decide +kernel⟩
def h461_2 : Height w461 := ⟨24182,9000,by decide +kernel⟩
def pick461 (cl : ℕ) : Height w461 := if cl<4 then (h461_0) else (if cl<227 then (h461_1) else (h461_2))
private theorem k461_1_0 : check w461 pick461 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k461_1_1 : check w461 pick461 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k461_1_2 : check w461 pick461 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w461 pick461 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k461_1_0 k461_1_1
private theorem k461_1_3 : check w461 pick461 1 t9998 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k461_1_4 : check w461 pick461 1 t9999 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w461 pick461 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t9998 k461_1_2 k461_1_3
private theorem k461_1_5 : check w461 pick461 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k461_1_6 : check w461 pick461 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k461_1_7 : check w461 pick461 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w461 pick461 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k461_1_5 k461_1_6
private theorem k461_1_8 : check w461 pick461 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k461_1_9 : check w461 pick461 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k461_1_10 : check w461 pick461 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w461 pick461 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k461_1_8 k461_1_9
private theorem k461_1_11 : check w461 pick461 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w461 pick461 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k461_1_7 k461_1_10
private theorem k461_1_12 : check w461 pick461 1 t10008 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w461 pick461 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9999 t10007 k461_1_4 k461_1_11
theorem cov461_1 : PA.Covered 1 (OZ.Valid 1 w461.low w461.t w461.y w461.r w461.cap) (P33.root 1) :=
  Night6836Tree.sound w461 pick461 1 t10008 _ k461_1_12
theorem cov461_2 : PA.Covered 2 (OZ.Valid 2 w461.low w461.t w461.y w461.r w461.cap) (P33.root 2) :=
  Night6836Tree.sound w461 pick461 2 t10022 _ (by decide +kernel)
theorem cov461_3 : PA.Covered 3 (OZ.Valid 3 w461.low w461.t w461.y w461.r w461.cap) (P33.root 3) :=
  Night6836Tree.sound w461 pick461 3 t564 _ (by decide +kernel)
theorem cov461_4 : PA.Covered 4 (OZ.Valid 4 w461.low w461.t w461.y w461.r w461.cap) (P33.root 4) :=
  Night6836Tree.sound w461 pick461 4 t565 _ (by decide +kernel)
theorem cov461_5 : PA.Covered 5 (OZ.Valid 5 w461.low w461.t w461.y w461.r w461.cap) (P33.root 5) :=
  Night6836Tree.sound w461 pick461 5 t566 _ (by decide +kernel)
theorem cov461_6 : PA.Covered 6 (OZ.Valid 6 w461.low w461.t w461.y w461.r w461.cap) (P33.root 6) :=
  Night6836Tree.sound w461 pick461 6 t567 _ (by decide +kernel)
theorem cov461_7 : PA.Covered 7 (OZ.Valid 7 w461.low w461.t w461.y w461.r w461.cap) (P33.root 7) :=
  Night6836Tree.sound w461 pick461 7 t568 _ (by decide +kernel)
theorem window461 : P33.WindowCount w461 := by
  apply P33.window_count w461 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov461_1
  · exact cov461_2
  · exact cov461_3
  · exact cov461_4
  · exact cov461_5
  · exact cov461_6
  · exact cov461_7
def w462 : P33.Window := ⟨8,25,6824,5825,196632085100886117,18709,19000,5000000,81920000000⟩
def h462_0 : Height w462 := ⟨18709,19000,by decide +kernel⟩
def h462_1 : Height w462 := ⟨25690,15000,by decide +kernel⟩
def h462_2 : Height w462 := ⟨42180,11000,by decide +kernel⟩
def pick462 (cl : ℕ) : Height w462 := if cl<32 then (h462_0) else (if cl<925 then (h462_1) else (h462_2))
private theorem k462_1_0 : check w462 pick462 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k462_1_1 : check w462 pick462 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k462_1_2 : check w462 pick462 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w462 pick462 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k462_1_0 k462_1_1
private theorem k462_1_3 : check w462 pick462 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k462_1_4 : check w462 pick462 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w462 pick462 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k462_1_2 k462_1_3
private theorem k462_1_5 : check w462 pick462 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k462_1_6 : check w462 pick462 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k462_1_7 : check w462 pick462 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w462 pick462 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k462_1_5 k462_1_6
private theorem k462_1_8 : check w462 pick462 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k462_1_9 : check w462 pick462 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k462_1_10 : check w462 pick462 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w462 pick462 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k462_1_8 k462_1_9
private theorem k462_1_11 : check w462 pick462 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w462 pick462 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k462_1_7 k462_1_10
private theorem k462_1_12 : check w462 pick462 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w462 pick462 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k462_1_4 k462_1_11
theorem cov462_1 : PA.Covered 1 (OZ.Valid 1 w462.low w462.t w462.y w462.r w462.cap) (P33.root 1) :=
  Night6836Tree.sound w462 pick462 1 t10025 _ k462_1_12
theorem cov462_2 : PA.Covered 2 (OZ.Valid 2 w462.low w462.t w462.y w462.r w462.cap) (P33.root 2) :=
  Night6836Tree.sound w462 pick462 2 t10022 _ (by decide +kernel)
theorem cov462_3 : PA.Covered 3 (OZ.Valid 3 w462.low w462.t w462.y w462.r w462.cap) (P33.root 3) :=
  Night6836Tree.sound w462 pick462 3 t564 _ (by decide +kernel)
theorem cov462_4 : PA.Covered 4 (OZ.Valid 4 w462.low w462.t w462.y w462.r w462.cap) (P33.root 4) :=
  Night6836Tree.sound w462 pick462 4 t565 _ (by decide +kernel)
theorem cov462_5 : PA.Covered 5 (OZ.Valid 5 w462.low w462.t w462.y w462.r w462.cap) (P33.root 5) :=
  Night6836Tree.sound w462 pick462 5 t566 _ (by decide +kernel)
theorem cov462_6 : PA.Covered 6 (OZ.Valid 6 w462.low w462.t w462.y w462.r w462.cap) (P33.root 6) :=
  Night6836Tree.sound w462 pick462 6 t567 _ (by decide +kernel)
theorem cov462_7 : PA.Covered 7 (OZ.Valid 7 w462.low w462.t w462.y w462.r w462.cap) (P33.root 7) :=
  Night6836Tree.sound w462 pick462 7 t568 _ (by decide +kernel)
theorem window462 : P33.WindowCount w462 := by
  apply P33.window_count w462 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov462_1
  · exact cov462_2
  · exact cov462_3
  · exact cov462_4
  · exact cov462_5
  · exact cov462_6
  · exact cov462_7
def w463 : P33.Window := ⟨8,25,7921,7887,228154510327715719,12606,15000,5000000,81920000000⟩
def h463_0 : Height w463 := ⟨12606,15000,by decide +kernel⟩
def h463_1 : Height w463 := ⟨17038,12000,by decide +kernel⟩
def h463_2 : Height w463 := ⟨25915,9000,by decide +kernel⟩
def pick463 (cl : ℕ) : Height w463 := if cl<5 then (h463_0) else (if cl<273 then (h463_1) else (h463_2))
private theorem k463_1_0 : check w463 pick463 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k463_1_1 : check w463 pick463 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k463_1_2 : check w463 pick463 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w463 pick463 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k463_1_0 k463_1_1
private theorem k463_1_3 : check w463 pick463 1 t9998 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k463_1_4 : check w463 pick463 1 t9999 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w463 pick463 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t9998 k463_1_2 k463_1_3
private theorem k463_1_5 : check w463 pick463 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k463_1_6 : check w463 pick463 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k463_1_7 : check w463 pick463 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w463 pick463 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k463_1_5 k463_1_6
private theorem k463_1_8 : check w463 pick463 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k463_1_9 : check w463 pick463 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k463_1_10 : check w463 pick463 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w463 pick463 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k463_1_8 k463_1_9
private theorem k463_1_11 : check w463 pick463 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w463 pick463 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k463_1_7 k463_1_10
private theorem k463_1_12 : check w463 pick463 1 t10008 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w463 pick463 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9999 t10007 k463_1_4 k463_1_11
theorem cov463_1 : PA.Covered 1 (OZ.Valid 1 w463.low w463.t w463.y w463.r w463.cap) (P33.root 1) :=
  Night6836Tree.sound w463 pick463 1 t10008 _ k463_1_12
theorem cov463_2 : PA.Covered 2 (OZ.Valid 2 w463.low w463.t w463.y w463.r w463.cap) (P33.root 2) :=
  Night6836Tree.sound w463 pick463 2 t10022 _ (by decide +kernel)
theorem cov463_3 : PA.Covered 3 (OZ.Valid 3 w463.low w463.t w463.y w463.r w463.cap) (P33.root 3) :=
  Night6836Tree.sound w463 pick463 3 t564 _ (by decide +kernel)
theorem cov463_4 : PA.Covered 4 (OZ.Valid 4 w463.low w463.t w463.y w463.r w463.cap) (P33.root 4) :=
  Night6836Tree.sound w463 pick463 4 t565 _ (by decide +kernel)
theorem cov463_5 : PA.Covered 5 (OZ.Valid 5 w463.low w463.t w463.y w463.r w463.cap) (P33.root 5) :=
  Night6836Tree.sound w463 pick463 5 t566 _ (by decide +kernel)
theorem cov463_6 : PA.Covered 6 (OZ.Valid 6 w463.low w463.t w463.y w463.r w463.cap) (P33.root 6) :=
  Night6836Tree.sound w463 pick463 6 t567 _ (by decide +kernel)
theorem cov463_7 : PA.Covered 7 (OZ.Valid 7 w463.low w463.t w463.y w463.r w463.cap) (P33.root 7) :=
  Night6836Tree.sound w463 pick463 7 t568 _ (by decide +kernel)
theorem window463 : P33.WindowCount w463 := by
  apply P33.window_count w463 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov463_1
  · exact cov463_2
  · exact cov463_3
  · exact cov463_4
  · exact cov463_5
  · exact cov463_6
  · exact cov463_7
def w464 : P33.Window := ⟨8,26,6825,5826,201565636207178329,20042,19000,5000000,81920000000⟩
def h464_0 : Height w464 := ⟨20042,19000,by decide +kernel⟩
def h464_1 : Height w464 := ⟨27256,15000,by decide +kernel⟩
def pick464 (cl : ℕ) : Height w464 := if cl<32 then (h464_0) else (h464_1)
private theorem k464_1_0 : check w464 pick464 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k464_1_1 : check w464 pick464 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k464_1_2 : check w464 pick464 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w464 pick464 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k464_1_0 k464_1_1
private theorem k464_1_3 : check w464 pick464 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k464_1_4 : check w464 pick464 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w464 pick464 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k464_1_2 k464_1_3
private theorem k464_1_5 : check w464 pick464 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k464_1_6 : check w464 pick464 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k464_1_7 : check w464 pick464 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w464 pick464 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k464_1_5 k464_1_6
private theorem k464_1_8 : check w464 pick464 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k464_1_9 : check w464 pick464 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k464_1_10 : check w464 pick464 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w464 pick464 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k464_1_8 k464_1_9
private theorem k464_1_11 : check w464 pick464 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w464 pick464 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k464_1_7 k464_1_10
private theorem k464_1_12 : check w464 pick464 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w464 pick464 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k464_1_4 k464_1_11
theorem cov464_1 : PA.Covered 1 (OZ.Valid 1 w464.low w464.t w464.y w464.r w464.cap) (P33.root 1) :=
  Night6836Tree.sound w464 pick464 1 t10025 _ k464_1_12
theorem cov464_2 : PA.Covered 2 (OZ.Valid 2 w464.low w464.t w464.y w464.r w464.cap) (P33.root 2) :=
  Night6836Tree.sound w464 pick464 2 t10022 _ (by decide +kernel)
theorem cov464_3 : PA.Covered 3 (OZ.Valid 3 w464.low w464.t w464.y w464.r w464.cap) (P33.root 3) :=
  Night6836Tree.sound w464 pick464 3 t564 _ (by decide +kernel)
theorem cov464_4 : PA.Covered 4 (OZ.Valid 4 w464.low w464.t w464.y w464.r w464.cap) (P33.root 4) :=
  Night6836Tree.sound w464 pick464 4 t565 _ (by decide +kernel)
theorem cov464_5 : PA.Covered 5 (OZ.Valid 5 w464.low w464.t w464.y w464.r w464.cap) (P33.root 5) :=
  Night6836Tree.sound w464 pick464 5 t566 _ (by decide +kernel)
theorem cov464_6 : PA.Covered 6 (OZ.Valid 6 w464.low w464.t w464.y w464.r w464.cap) (P33.root 6) :=
  Night6836Tree.sound w464 pick464 6 t567 _ (by decide +kernel)
theorem cov464_7 : PA.Covered 7 (OZ.Valid 7 w464.low w464.t w464.y w464.r w464.cap) (P33.root 7) :=
  Night6836Tree.sound w464 pick464 7 t568 _ (by decide +kernel)
theorem window464 : P33.WindowCount w464 := by
  apply P33.window_count w464 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov464_1
  · exact cov464_2
  · exact cov464_3
  · exact cov464_4
  · exact cov464_5
  · exact cov464_6
  · exact cov464_7
def w465 : P33.Window := ⟨8,26,7886,7851,232815133740362607,13709,15000,5000000,81920000000⟩
def h465_0 : Height w465 := ⟨13709,15000,by decide +kernel⟩
def h465_1 : Height w465 := ⟨18325,12000,by decide +kernel⟩
def h465_2 : Height w465 := ⟨27692,9000,by decide +kernel⟩
def pick465 (cl : ℕ) : Height w465 := if cl<6 then (h465_0) else (if cl<302 then (h465_1) else (h465_2))
private theorem k465_1_0 : check w465 pick465 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k465_1_1 : check w465 pick465 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k465_1_2 : check w465 pick465 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w465 pick465 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k465_1_0 k465_1_1
private theorem k465_1_3 : check w465 pick465 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k465_1_4 : check w465 pick465 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w465 pick465 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k465_1_2 k465_1_3
private theorem k465_1_5 : check w465 pick465 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k465_1_6 : check w465 pick465 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k465_1_7 : check w465 pick465 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w465 pick465 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k465_1_5 k465_1_6
private theorem k465_1_8 : check w465 pick465 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k465_1_9 : check w465 pick465 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k465_1_10 : check w465 pick465 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w465 pick465 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k465_1_8 k465_1_9
private theorem k465_1_11 : check w465 pick465 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w465 pick465 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k465_1_7 k465_1_10
private theorem k465_1_12 : check w465 pick465 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w465 pick465 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k465_1_4 k465_1_11
theorem cov465_1 : PA.Covered 1 (OZ.Valid 1 w465.low w465.t w465.y w465.r w465.cap) (P33.root 1) :=
  Night6836Tree.sound w465 pick465 1 t10025 _ k465_1_12
theorem cov465_2 : PA.Covered 2 (OZ.Valid 2 w465.low w465.t w465.y w465.r w465.cap) (P33.root 2) :=
  Night6836Tree.sound w465 pick465 2 t10022 _ (by decide +kernel)
theorem cov465_3 : PA.Covered 3 (OZ.Valid 3 w465.low w465.t w465.y w465.r w465.cap) (P33.root 3) :=
  Night6836Tree.sound w465 pick465 3 t564 _ (by decide +kernel)
theorem cov465_4 : PA.Covered 4 (OZ.Valid 4 w465.low w465.t w465.y w465.r w465.cap) (P33.root 4) :=
  Night6836Tree.sound w465 pick465 4 t565 _ (by decide +kernel)
theorem cov465_5 : PA.Covered 5 (OZ.Valid 5 w465.low w465.t w465.y w465.r w465.cap) (P33.root 5) :=
  Night6836Tree.sound w465 pick465 5 t566 _ (by decide +kernel)
theorem cov465_6 : PA.Covered 6 (OZ.Valid 6 w465.low w465.t w465.y w465.r w465.cap) (P33.root 6) :=
  Night6836Tree.sound w465 pick465 6 t567 _ (by decide +kernel)
theorem cov465_7 : PA.Covered 7 (OZ.Valid 7 w465.low w465.t w465.y w465.r w465.cap) (P33.root 7) :=
  Night6836Tree.sound w465 pick465 7 t568 _ (by decide +kernel)
theorem window465 : P33.WindowCount w465 := by
  apply P33.window_count w465 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov465_1
  · exact cov465_2
  · exact cov465_3
  · exact cov465_4
  · exact cov465_5
  · exact cov465_6
  · exact cov465_7
def w466 : P33.Window := ⟨8,27,7850,7815,237394626037286838,14827,15000,5000000,81920000000⟩
def h466_0 : Height w466 := ⟨14827,15000,by decide +kernel⟩
def h466_1 : Height w466 := ⟨19632,12000,by decide +kernel⟩
def h466_2 : Height w466 := ⟨29505,9000,by decide +kernel⟩
def pick466 (cl : ℕ) : Height w466 := if cl<10 then (h466_0) else (if cl<434 then (h466_1) else (h466_2))
private theorem k466_1_0 : check w466 pick466 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k466_1_1 : check w466 pick466 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k466_1_2 : check w466 pick466 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w466 pick466 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k466_1_0 k466_1_1
private theorem k466_1_3 : check w466 pick466 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k466_1_4 : check w466 pick466 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w466 pick466 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k466_1_2 k466_1_3
private theorem k466_1_5 : check w466 pick466 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k466_1_6 : check w466 pick466 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k466_1_7 : check w466 pick466 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w466 pick466 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k466_1_5 k466_1_6
private theorem k466_1_8 : check w466 pick466 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k466_1_9 : check w466 pick466 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k466_1_10 : check w466 pick466 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w466 pick466 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k466_1_8 k466_1_9
private theorem k466_1_11 : check w466 pick466 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w466 pick466 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k466_1_7 k466_1_10
private theorem k466_1_12 : check w466 pick466 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w466 pick466 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k466_1_4 k466_1_11
theorem cov466_1 : PA.Covered 1 (OZ.Valid 1 w466.low w466.t w466.y w466.r w466.cap) (P33.root 1) :=
  Night6836Tree.sound w466 pick466 1 t10025 _ k466_1_12
theorem cov466_2 : PA.Covered 2 (OZ.Valid 2 w466.low w466.t w466.y w466.r w466.cap) (P33.root 2) :=
  Night6836Tree.sound w466 pick466 2 t10022 _ (by decide +kernel)
theorem cov466_3 : PA.Covered 3 (OZ.Valid 3 w466.low w466.t w466.y w466.r w466.cap) (P33.root 3) :=
  Night6836Tree.sound w466 pick466 3 t564 _ (by decide +kernel)
theorem cov466_4 : PA.Covered 4 (OZ.Valid 4 w466.low w466.t w466.y w466.r w466.cap) (P33.root 4) :=
  Night6836Tree.sound w466 pick466 4 t565 _ (by decide +kernel)
theorem cov466_5 : PA.Covered 5 (OZ.Valid 5 w466.low w466.t w466.y w466.r w466.cap) (P33.root 5) :=
  Night6836Tree.sound w466 pick466 5 t566 _ (by decide +kernel)
theorem cov466_6 : PA.Covered 6 (OZ.Valid 6 w466.low w466.t w466.y w466.r w466.cap) (P33.root 6) :=
  Night6836Tree.sound w466 pick466 6 t567 _ (by decide +kernel)
theorem cov466_7 : PA.Covered 7 (OZ.Valid 7 w466.low w466.t w466.y w466.r w466.cap) (P33.root 7) :=
  Night6836Tree.sound w466 pick466 7 t568 _ (by decide +kernel)
theorem window466 : P33.WindowCount w466 := by
  apply P33.window_count w466 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov466_1
  · exact cov466_2
  · exact cov466_3
  · exact cov466_4
  · exact cov466_5
  · exact cov466_6
  · exact cov466_7
def w467 : P33.Window := ⟨8,28,7814,7779,241921722337200203,15960,15000,5000000,81920000000⟩
def h467_0 : Height w467 := ⟨15960,15000,by decide +kernel⟩
def h467_1 : Height w467 := ⟨20961,12000,by decide +kernel⟩
def h467_2 : Height w467 := ⟨31357,9000,by decide +kernel⟩
def pick467 (cl : ℕ) : Height w467 := if cl<14 then (h467_0) else (if cl<676 then (h467_1) else (h467_2))
private theorem k467_1_0 : check w467 pick467 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k467_1_1 : check w467 pick467 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k467_1_2 : check w467 pick467 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w467 pick467 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k467_1_0 k467_1_1
private theorem k467_1_3 : check w467 pick467 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k467_1_4 : check w467 pick467 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w467 pick467 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k467_1_2 k467_1_3
private theorem k467_1_5 : check w467 pick467 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k467_1_6 : check w467 pick467 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k467_1_7 : check w467 pick467 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w467 pick467 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k467_1_5 k467_1_6
private theorem k467_1_8 : check w467 pick467 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k467_1_9 : check w467 pick467 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k467_1_10 : check w467 pick467 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w467 pick467 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k467_1_8 k467_1_9
private theorem k467_1_11 : check w467 pick467 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w467 pick467 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k467_1_7 k467_1_10
private theorem k467_1_12 : check w467 pick467 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w467 pick467 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k467_1_4 k467_1_11
theorem cov467_1 : PA.Covered 1 (OZ.Valid 1 w467.low w467.t w467.y w467.r w467.cap) (P33.root 1) :=
  Night6836Tree.sound w467 pick467 1 t10025 _ k467_1_12
theorem cov467_2 : PA.Covered 2 (OZ.Valid 2 w467.low w467.t w467.y w467.r w467.cap) (P33.root 2) :=
  Night6836Tree.sound w467 pick467 2 t10022 _ (by decide +kernel)
theorem cov467_3 : PA.Covered 3 (OZ.Valid 3 w467.low w467.t w467.y w467.r w467.cap) (P33.root 3) :=
  Night6836Tree.sound w467 pick467 3 t564 _ (by decide +kernel)
theorem cov467_4 : PA.Covered 4 (OZ.Valid 4 w467.low w467.t w467.y w467.r w467.cap) (P33.root 4) :=
  Night6836Tree.sound w467 pick467 4 t565 _ (by decide +kernel)
theorem cov467_5 : PA.Covered 5 (OZ.Valid 5 w467.low w467.t w467.y w467.r w467.cap) (P33.root 5) :=
  Night6836Tree.sound w467 pick467 5 t566 _ (by decide +kernel)
theorem cov467_6 : PA.Covered 6 (OZ.Valid 6 w467.low w467.t w467.y w467.r w467.cap) (P33.root 6) :=
  Night6836Tree.sound w467 pick467 6 t567 _ (by decide +kernel)
theorem cov467_7 : PA.Covered 7 (OZ.Valid 7 w467.low w467.t w467.y w467.r w467.cap) (P33.root 7) :=
  Night6836Tree.sound w467 pick467 7 t568 _ (by decide +kernel)
theorem window467 : P33.WindowCount w467 := by
  apply P33.window_count w467 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov467_1
  · exact cov467_2
  · exact cov467_3
  · exact cov467_4
  · exact cov467_5
  · exact cov467_6
  · exact cov467_7
def w468 : P33.Window := ⟨8,29,7778,7567,235256972086489063,17992,15000,5000000,81920000000⟩
def h468_0 : Height w468 := ⟨17992,15000,by decide +kernel⟩
def h468_1 : Height w468 := ⟨23483,12000,by decide +kernel⟩
def h468_2 : Height w468 := ⟨35354,9000,by decide +kernel⟩
def pick468 (cl : ℕ) : Height w468 := if cl<32 then (h468_0) else (if cl<925 then (h468_1) else (h468_2))
private theorem k468_1_0 : check w468 pick468 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k468_1_1 : check w468 pick468 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k468_1_2 : check w468 pick468 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w468 pick468 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k468_1_0 k468_1_1
private theorem k468_1_3 : check w468 pick468 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k468_1_4 : check w468 pick468 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w468 pick468 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k468_1_2 k468_1_3
private theorem k468_1_5 : check w468 pick468 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k468_1_6 : check w468 pick468 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k468_1_7 : check w468 pick468 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w468 pick468 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k468_1_5 k468_1_6
private theorem k468_1_8 : check w468 pick468 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k468_1_9 : check w468 pick468 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k468_1_10 : check w468 pick468 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w468 pick468 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k468_1_8 k468_1_9
private theorem k468_1_11 : check w468 pick468 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w468 pick468 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k468_1_7 k468_1_10
private theorem k468_1_12 : check w468 pick468 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w468 pick468 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k468_1_4 k468_1_11
theorem cov468_1 : PA.Covered 1 (OZ.Valid 1 w468.low w468.t w468.y w468.r w468.cap) (P33.root 1) :=
  Night6836Tree.sound w468 pick468 1 t10025 _ k468_1_12
private theorem k468_2_0 : check w468 pick468 2 t10027 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k468_2_1 : check w468 pick468 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k468_2_2 : check w468 pick468 2 t10028 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w468 pick468 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t10027 t9135 k468_2_0 k468_2_1
theorem cov468_2 : PA.Covered 2 (OZ.Valid 2 w468.low w468.t w468.y w468.r w468.cap) (P33.root 2) :=
  Night6836Tree.sound w468 pick468 2 t10028 _ k468_2_2
theorem cov468_3 : PA.Covered 3 (OZ.Valid 3 w468.low w468.t w468.y w468.r w468.cap) (P33.root 3) :=
  Night6836Tree.sound w468 pick468 3 t564 _ (by decide +kernel)
theorem cov468_4 : PA.Covered 4 (OZ.Valid 4 w468.low w468.t w468.y w468.r w468.cap) (P33.root 4) :=
  Night6836Tree.sound w468 pick468 4 t565 _ (by decide +kernel)
theorem cov468_5 : PA.Covered 5 (OZ.Valid 5 w468.low w468.t w468.y w468.r w468.cap) (P33.root 5) :=
  Night6836Tree.sound w468 pick468 5 t566 _ (by decide +kernel)
theorem cov468_6 : PA.Covered 6 (OZ.Valid 6 w468.low w468.t w468.y w468.r w468.cap) (P33.root 6) :=
  Night6836Tree.sound w468 pick468 6 t567 _ (by decide +kernel)
theorem cov468_7 : PA.Covered 7 (OZ.Valid 7 w468.low w468.t w468.y w468.r w468.cap) (P33.root 7) :=
  Night6836Tree.sound w468 pick468 7 t568 _ (by decide +kernel)
theorem window468 : P33.WindowCount w468 := by
  apply P33.window_count w468 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov468_1
  · exact cov468_2
  · exact cov468_3
  · exact cov468_4
  · exact cov468_5
  · exact cov468_6
  · exact cov468_7
def w469 : P33.Window := ⟨8,30,5629,4630,182518354220640183,27754,27000,5000000,81920000000⟩
def h469_0 : Height w469 := ⟨27754,27000,by decide +kernel⟩
def h469_1 : Height w469 := ⟨33403,23000,by decide +kernel⟩
def h469_2 : Height w469 := ⟨41845,19000,by decide +kernel⟩
def h469_3 : Height w469 := ⟨58254,15000,by decide +kernel⟩
def pick469 (cl : ℕ) : Height w469 := if cl<49 then (if cl<4 then (h469_0) else (h469_1)) else (if cl<925 then (h469_2) else (h469_3))
private theorem k469_1_0 : check w469 pick469 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k469_1_1 : check w469 pick469 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k469_1_2 : check w469 pick469 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w469 pick469 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k469_1_0 k469_1_1
private theorem k469_1_3 : check w469 pick469 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k469_1_4 : check w469 pick469 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w469 pick469 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k469_1_2 k469_1_3
private theorem k469_1_5 : check w469 pick469 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k469_1_6 : check w469 pick469 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k469_1_7 : check w469 pick469 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w469 pick469 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k469_1_5 k469_1_6
private theorem k469_1_8 : check w469 pick469 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k469_1_9 : check w469 pick469 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k469_1_10 : check w469 pick469 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w469 pick469 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k469_1_8 k469_1_9
private theorem k469_1_11 : check w469 pick469 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w469 pick469 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k469_1_7 k469_1_10
private theorem k469_1_12 : check w469 pick469 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w469 pick469 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k469_1_4 k469_1_11
theorem cov469_1 : PA.Covered 1 (OZ.Valid 1 w469.low w469.t w469.y w469.r w469.cap) (P33.root 1) :=
  Night6836Tree.sound w469 pick469 1 t10025 _ k469_1_12
theorem cov469_2 : PA.Covered 2 (OZ.Valid 2 w469.low w469.t w469.y w469.r w469.cap) (P33.root 2) :=
  Night6836Tree.sound w469 pick469 2 t10029 _ (by decide +kernel)
theorem cov469_3 : PA.Covered 3 (OZ.Valid 3 w469.low w469.t w469.y w469.r w469.cap) (P33.root 3) :=
  Night6836Tree.sound w469 pick469 3 t564 _ (by decide +kernel)
theorem cov469_4 : PA.Covered 4 (OZ.Valid 4 w469.low w469.t w469.y w469.r w469.cap) (P33.root 4) :=
  Night6836Tree.sound w469 pick469 4 t565 _ (by decide +kernel)
theorem cov469_5 : PA.Covered 5 (OZ.Valid 5 w469.low w469.t w469.y w469.r w469.cap) (P33.root 5) :=
  Night6836Tree.sound w469 pick469 5 t566 _ (by decide +kernel)
theorem cov469_6 : PA.Covered 6 (OZ.Valid 6 w469.low w469.t w469.y w469.r w469.cap) (P33.root 6) :=
  Night6836Tree.sound w469 pick469 6 t567 _ (by decide +kernel)
theorem cov469_7 : PA.Covered 7 (OZ.Valid 7 w469.low w469.t w469.y w469.r w469.cap) (P33.root 7) :=
  Night6836Tree.sound w469 pick469 7 t2134 _ (by decide +kernel)
theorem window469 : P33.WindowCount w469 := by
  apply P33.window_count w469 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov469_1
  · exact cov469_2
  · exact cov469_3
  · exact cov469_4
  · exact cov469_5
  · exact cov469_6
  · exact cov469_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w470 : P33.Window := ⟨8,30,7741,7705,238259091263942376,18285,15000,5000000,81920000000⟩
def h470_0 : Height w470 := ⟨18285,15000,by decide +kernel⟩
def h470_1 : Height w470 := ⟨23695,12000,by decide +kernel⟩
def h470_2 : Height w470 := ⟨35203,9000,by decide +kernel⟩
def pick470 (cl : ℕ) : Height w470 := if cl<32 then (h470_0) else (if cl<925 then (h470_1) else (h470_2))
private theorem k470_1_0 : check w470 pick470 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k470_1_1 : check w470 pick470 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k470_1_2 : check w470 pick470 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w470 pick470 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k470_1_0 k470_1_1
private theorem k470_1_3 : check w470 pick470 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k470_1_4 : check w470 pick470 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w470 pick470 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k470_1_2 k470_1_3
private theorem k470_1_5 : check w470 pick470 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k470_1_6 : check w470 pick470 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k470_1_7 : check w470 pick470 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w470 pick470 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k470_1_5 k470_1_6
private theorem k470_1_8 : check w470 pick470 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k470_1_9 : check w470 pick470 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k470_1_10 : check w470 pick470 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w470 pick470 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k470_1_8 k470_1_9
private theorem k470_1_11 : check w470 pick470 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w470 pick470 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k470_1_7 k470_1_10
private theorem k470_1_12 : check w470 pick470 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w470 pick470 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k470_1_4 k470_1_11
theorem cov470_1 : PA.Covered 1 (OZ.Valid 1 w470.low w470.t w470.y w470.r w470.cap) (P33.root 1) :=
  Night6836Tree.sound w470 pick470 1 t10025 _ k470_1_12
private theorem k470_2_0 : check w470 pick470 2 t10027 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k470_2_1 : check w470 pick470 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k470_2_2 : check w470 pick470 2 t10028 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w470 pick470 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t10027 t9135 k470_2_0 k470_2_1
theorem cov470_2 : PA.Covered 2 (OZ.Valid 2 w470.low w470.t w470.y w470.r w470.cap) (P33.root 2) :=
  Night6836Tree.sound w470 pick470 2 t10028 _ k470_2_2
theorem cov470_3 : PA.Covered 3 (OZ.Valid 3 w470.low w470.t w470.y w470.r w470.cap) (P33.root 3) :=
  Night6836Tree.sound w470 pick470 3 t564 _ (by decide +kernel)
theorem cov470_4 : PA.Covered 4 (OZ.Valid 4 w470.low w470.t w470.y w470.r w470.cap) (P33.root 4) :=
  Night6836Tree.sound w470 pick470 4 t565 _ (by decide +kernel)
theorem cov470_5 : PA.Covered 5 (OZ.Valid 5 w470.low w470.t w470.y w470.r w470.cap) (P33.root 5) :=
  Night6836Tree.sound w470 pick470 5 t566 _ (by decide +kernel)
theorem cov470_6 : PA.Covered 6 (OZ.Valid 6 w470.low w470.t w470.y w470.r w470.cap) (P33.root 6) :=
  Night6836Tree.sound w470 pick470 6 t567 _ (by decide +kernel)
theorem cov470_7 : PA.Covered 7 (OZ.Valid 7 w470.low w470.t w470.y w470.r w470.cap) (P33.root 7) :=
  Night6836Tree.sound w470 pick470 7 t568 _ (by decide +kernel)
theorem window470 : P33.WindowCount w470 := by
  apply P33.window_count w470 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov470_1
  · exact cov470_2
  · exact cov470_3
  · exact cov470_4
  · exact cov470_5
  · exact cov470_6
  · exact cov470_7
def w471 : P33.Window := ⟨8,31,5430,4431,179985861771662789,32219,27000,5000000,81920000000⟩
def h471_0 : Height w471 := ⟨32219,27000,by decide +kernel⟩
def h471_1 : Height w471 := ⟨38556,23000,by decide +kernel⟩
def h471_2 : Height w471 := ⟨48335,19000,by decide +kernel⟩
def pick471 (cl : ℕ) : Height w471 := if cl<10 then (h471_0) else (if cl<117 then (h471_1) else (h471_2))
private theorem k471_1_0 : check w471 pick471 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k471_1_1 : check w471 pick471 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k471_1_2 : check w471 pick471 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w471 pick471 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k471_1_0 k471_1_1
private theorem k471_1_3 : check w471 pick471 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k471_1_4 : check w471 pick471 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w471 pick471 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k471_1_2 k471_1_3
private theorem k471_1_5 : check w471 pick471 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k471_1_6 : check w471 pick471 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k471_1_7 : check w471 pick471 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w471 pick471 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k471_1_5 k471_1_6
private theorem k471_1_8 : check w471 pick471 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k471_1_9 : check w471 pick471 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k471_1_10 : check w471 pick471 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w471 pick471 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k471_1_8 k471_1_9
private theorem k471_1_11 : check w471 pick471 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w471 pick471 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k471_1_7 k471_1_10
private theorem k471_1_12 : check w471 pick471 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w471 pick471 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k471_1_4 k471_1_11
theorem cov471_1 : PA.Covered 1 (OZ.Valid 1 w471.low w471.t w471.y w471.r w471.cap) (P33.root 1) :=
  Night6836Tree.sound w471 pick471 1 t10025 _ k471_1_12
theorem cov471_2 : PA.Covered 2 (OZ.Valid 2 w471.low w471.t w471.y w471.r w471.cap) (P33.root 2) :=
  Night6836Tree.sound w471 pick471 2 t10037 _ (by decide +kernel)
theorem cov471_3 : PA.Covered 3 (OZ.Valid 3 w471.low w471.t w471.y w471.r w471.cap) (P33.root 3) :=
  Night6836Tree.sound w471 pick471 3 t564 _ (by decide +kernel)
theorem cov471_4 : PA.Covered 4 (OZ.Valid 4 w471.low w471.t w471.y w471.r w471.cap) (P33.root 4) :=
  Night6836Tree.sound w471 pick471 4 t565 _ (by decide +kernel)
theorem cov471_5 : PA.Covered 5 (OZ.Valid 5 w471.low w471.t w471.y w471.r w471.cap) (P33.root 5) :=
  Night6836Tree.sound w471 pick471 5 t566 _ (by decide +kernel)
theorem cov471_6 : PA.Covered 6 (OZ.Valid 6 w471.low w471.t w471.y w471.r w471.cap) (P33.root 6) :=
  Night6836Tree.sound w471 pick471 6 t567 _ (by decide +kernel)
theorem cov471_7 : PA.Covered 7 (OZ.Valid 7 w471.low w471.t w471.y w471.r w471.cap) (P33.root 7) :=
  Night6836Tree.sound w471 pick471 7 t2134 _ (by decide +kernel)
theorem window471 : P33.WindowCount w471 := by
  apply P33.window_count w471 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov471_1
  · exact cov471_2
  · exact cov471_3
  · exact cov471_4
  · exact cov471_5
  · exact cov471_6
  · exact cov471_7
def w472 : P33.Window := ⟨8,31,7332,6383,242831061756315590,23417,18000,5000000,81920000000⟩
def h472_0 : Height w472 := ⟨23417,18000,by decide +kernel⟩
def h472_1 : Height w472 := ⟨28768,15000,by decide +kernel⟩
def h472_2 : Height w472 := ⟨38109,12000,by decide +kernel⟩
def pick472 (cl : ℕ) : Height w472 := if cl<32 then (h472_0) else (if cl<302 then (h472_1) else (h472_2))
private theorem k472_1_0 : check w472 pick472 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k472_1_1 : check w472 pick472 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k472_1_2 : check w472 pick472 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w472 pick472 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k472_1_0 k472_1_1
private theorem k472_1_3 : check w472 pick472 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k472_1_4 : check w472 pick472 1 t10042 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w472 pick472 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10023 k472_1_2 k472_1_3
private theorem k472_1_5 : check w472 pick472 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k472_1_6 : check w472 pick472 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k472_1_7 : check w472 pick472 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w472 pick472 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k472_1_5 k472_1_6
private theorem k472_1_8 : check w472 pick472 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k472_1_9 : check w472 pick472 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k472_1_10 : check w472 pick472 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w472 pick472 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k472_1_8 k472_1_9
private theorem k472_1_11 : check w472 pick472 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w472 pick472 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k472_1_7 k472_1_10
private theorem k472_1_12 : check w472 pick472 1 t10043 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w472 pick472 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10042 t10007 k472_1_4 k472_1_11
theorem cov472_1 : PA.Covered 1 (OZ.Valid 1 w472.low w472.t w472.y w472.r w472.cap) (P33.root 1) :=
  Night6836Tree.sound w472 pick472 1 t10043 _ k472_1_12
theorem cov472_2 : PA.Covered 2 (OZ.Valid 2 w472.low w472.t w472.y w472.r w472.cap) (P33.root 2) :=
  Night6836Tree.sound w472 pick472 2 t10022 _ (by decide +kernel)
theorem cov472_3 : PA.Covered 3 (OZ.Valid 3 w472.low w472.t w472.y w472.r w472.cap) (P33.root 3) :=
  Night6836Tree.sound w472 pick472 3 t564 _ (by decide +kernel)
theorem cov472_4 : PA.Covered 4 (OZ.Valid 4 w472.low w472.t w472.y w472.r w472.cap) (P33.root 4) :=
  Night6836Tree.sound w472 pick472 4 t565 _ (by decide +kernel)
theorem cov472_5 : PA.Covered 5 (OZ.Valid 5 w472.low w472.t w472.y w472.r w472.cap) (P33.root 5) :=
  Night6836Tree.sound w472 pick472 5 t566 _ (by decide +kernel)
theorem cov472_6 : PA.Covered 6 (OZ.Valid 6 w472.low w472.t w472.y w472.r w472.cap) (P33.root 6) :=
  Night6836Tree.sound w472 pick472 6 t567 _ (by decide +kernel)
theorem cov472_7 : PA.Covered 7 (OZ.Valid 7 w472.low w472.t w472.y w472.r w472.cap) (P33.root 7) :=
  Night6836Tree.sound w472 pick472 7 t568 _ (by decide +kernel)
theorem window472 : P33.WindowCount w472 := by
  apply P33.window_count w472 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov472_1
  · exact cov472_2
  · exact cov472_3
  · exact cov472_4
  · exact cov472_5
  · exact cov472_6
  · exact cov472_7
def w473 : P33.Window := ⟨8,31,7704,7668,241221123748442080,19473,15000,5000000,81920000000⟩
def h473_0 : Height w473 := ⟨19473,15000,by decide +kernel⟩
def h473_1 : Height w473 := ⟨25097,12000,by decide +kernel⟩
def h473_2 : Height w473 := ⟨37190,9000,by decide +kernel⟩
def pick473 (cl : ℕ) : Height w473 := if cl<32 then (h473_0) else (if cl<925 then (h473_1) else (h473_2))
private theorem k473_1_0 : check w473 pick473 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k473_1_1 : check w473 pick473 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k473_1_2 : check w473 pick473 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w473 pick473 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k473_1_0 k473_1_1
private theorem k473_1_3 : check w473 pick473 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k473_1_4 : check w473 pick473 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w473 pick473 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k473_1_2 k473_1_3
private theorem k473_1_5 : check w473 pick473 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k473_1_6 : check w473 pick473 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k473_1_7 : check w473 pick473 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w473 pick473 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k473_1_5 k473_1_6
private theorem k473_1_8 : check w473 pick473 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k473_1_9 : check w473 pick473 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k473_1_10 : check w473 pick473 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w473 pick473 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k473_1_8 k473_1_9
private theorem k473_1_11 : check w473 pick473 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w473 pick473 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k473_1_7 k473_1_10
private theorem k473_1_12 : check w473 pick473 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w473 pick473 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k473_1_4 k473_1_11
theorem cov473_1 : PA.Covered 1 (OZ.Valid 1 w473.low w473.t w473.y w473.r w473.cap) (P33.root 1) :=
  Night6836Tree.sound w473 pick473 1 t10025 _ k473_1_12
private theorem k473_2_0 : check w473 pick473 2 t10027 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k473_2_1 : check w473 pick473 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k473_2_2 : check w473 pick473 2 t10028 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w473 pick473 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t10027 t9135 k473_2_0 k473_2_1
theorem cov473_2 : PA.Covered 2 (OZ.Valid 2 w473.low w473.t w473.y w473.r w473.cap) (P33.root 2) :=
  Night6836Tree.sound w473 pick473 2 t10028 _ k473_2_2
theorem cov473_3 : PA.Covered 3 (OZ.Valid 3 w473.low w473.t w473.y w473.r w473.cap) (P33.root 3) :=
  Night6836Tree.sound w473 pick473 3 t564 _ (by decide +kernel)
theorem cov473_4 : PA.Covered 4 (OZ.Valid 4 w473.low w473.t w473.y w473.r w473.cap) (P33.root 4) :=
  Night6836Tree.sound w473 pick473 4 t565 _ (by decide +kernel)
theorem cov473_5 : PA.Covered 5 (OZ.Valid 5 w473.low w473.t w473.y w473.r w473.cap) (P33.root 5) :=
  Night6836Tree.sound w473 pick473 5 t566 _ (by decide +kernel)
theorem cov473_6 : PA.Covered 6 (OZ.Valid 6 w473.low w473.t w473.y w473.r w473.cap) (P33.root 6) :=
  Night6836Tree.sound w473 pick473 6 t567 _ (by decide +kernel)
theorem cov473_7 : PA.Covered 7 (OZ.Valid 7 w473.low w473.t w473.y w473.r w473.cap) (P33.root 7) :=
  Night6836Tree.sound w473 pick473 7 t568 _ (by decide +kernel)
theorem window473 : P33.WindowCount w473 := by
  apply P33.window_count w473 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov473_1
  · exact cov473_2
  · exact cov473_3
  · exact cov473_4
  · exact cov473_5
  · exact cov473_6
  · exact cov473_7
def w474 : P33.Window := ⟨8,32,5431,4432,183918864444937943,33892,27000,5000000,81920000000⟩
def h474_0 : Height w474 := ⟨33892,27000,by decide +kernel⟩
def h474_1 : Height w474 := ⟨40385,23000,by decide +kernel⟩
def h474_2 : Height w474 := ⟨50441,19000,by decide +kernel⟩
def pick474 (cl : ℕ) : Height w474 := if cl<12 then (h474_0) else (if cl<136 then (h474_1) else (h474_2))
private theorem k474_1_0 : check w474 pick474 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k474_1_1 : check w474 pick474 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k474_1_2 : check w474 pick474 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w474 pick474 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k474_1_0 k474_1_1
private theorem k474_1_3 : check w474 pick474 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k474_1_4 : check w474 pick474 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w474 pick474 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k474_1_2 k474_1_3
private theorem k474_1_5 : check w474 pick474 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k474_1_6 : check w474 pick474 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k474_1_7 : check w474 pick474 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w474 pick474 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k474_1_5 k474_1_6
private theorem k474_1_8 : check w474 pick474 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k474_1_9 : check w474 pick474 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k474_1_10 : check w474 pick474 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w474 pick474 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k474_1_8 k474_1_9
private theorem k474_1_11 : check w474 pick474 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w474 pick474 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k474_1_7 k474_1_10
private theorem k474_1_12 : check w474 pick474 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w474 pick474 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k474_1_4 k474_1_11
theorem cov474_1 : PA.Covered 1 (OZ.Valid 1 w474.low w474.t w474.y w474.r w474.cap) (P33.root 1) :=
  Night6836Tree.sound w474 pick474 1 t10025 _ k474_1_12
theorem cov474_2 : PA.Covered 2 (OZ.Valid 2 w474.low w474.t w474.y w474.r w474.cap) (P33.root 2) :=
  Night6836Tree.sound w474 pick474 2 t10037 _ (by decide +kernel)
theorem cov474_3 : PA.Covered 3 (OZ.Valid 3 w474.low w474.t w474.y w474.r w474.cap) (P33.root 3) :=
  Night6836Tree.sound w474 pick474 3 t564 _ (by decide +kernel)
theorem cov474_4 : PA.Covered 4 (OZ.Valid 4 w474.low w474.t w474.y w474.r w474.cap) (P33.root 4) :=
  Night6836Tree.sound w474 pick474 4 t565 _ (by decide +kernel)
theorem cov474_5 : PA.Covered 5 (OZ.Valid 5 w474.low w474.t w474.y w474.r w474.cap) (P33.root 5) :=
  Night6836Tree.sound w474 pick474 5 t566 _ (by decide +kernel)
theorem cov474_6 : PA.Covered 6 (OZ.Valid 6 w474.low w474.t w474.y w474.r w474.cap) (P33.root 6) :=
  Night6836Tree.sound w474 pick474 6 t567 _ (by decide +kernel)
theorem cov474_7 : PA.Covered 7 (OZ.Valid 7 w474.low w474.t w474.y w474.r w474.cap) (P33.root 7) :=
  Night6836Tree.sound w474 pick474 7 t2134 _ (by decide +kernel)
theorem window474 : P33.WindowCount w474 := by
  apply P33.window_count w474 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov474_1
  · exact cov474_2
  · exact cov474_3
  · exact cov474_4
  · exact cov474_5
  · exact cov474_6
  · exact cov474_7
def w475 : P33.Window := ⟨8,32,6931,5932,203846926192347335,27045,19000,5000000,81920000000⟩
def h475_0 : Height w475 := ⟨27045,19000,by decide +kernel⟩
def h475_1 : Height w475 := ⟨35274,15000,by decide +kernel⟩
def h475_2 : Height w475 := ⟨55007,11000,by decide +kernel⟩
def pick475 (cl : ℕ) : Height w475 := if cl<43 then (h475_0) else (if cl<1002 then (h475_1) else (h475_2))
private theorem k475_1_0 : check w475 pick475 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k475_1_1 : check w475 pick475 1 t10052 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k475_1_2 : check w475 pick475 1 t10053 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w475 pick475 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10052 k475_1_0 k475_1_1
private theorem k475_1_3 : check w475 pick475 1 t10054 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k475_1_4 : check w475 pick475 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k475_1_5 : check w475 pick475 1 t10059 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w475 pick475 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10054 t10058 k475_1_3 k475_1_4
private theorem k475_1_6 : check w475 pick475 1 t10060 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w475 pick475 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10053 t10059 k475_1_2 k475_1_5
private theorem k475_1_7 : check w475 pick475 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k475_1_8 : check w475 pick475 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k475_1_9 : check w475 pick475 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w475 pick475 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k475_1_7 k475_1_8
private theorem k475_1_10 : check w475 pick475 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k475_1_11 : check w475 pick475 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k475_1_12 : check w475 pick475 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w475 pick475 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k475_1_10 k475_1_11
private theorem k475_1_13 : check w475 pick475 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w475 pick475 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k475_1_9 k475_1_12
private theorem k475_1_14 : check w475 pick475 1 t10067 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w475 pick475 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10060 t10066 k475_1_6 k475_1_13
theorem cov475_1 : PA.Covered 1 (OZ.Valid 1 w475.low w475.t w475.y w475.r w475.cap) (P33.root 1) :=
  Night6836Tree.sound w475 pick475 1 t10067 _ k475_1_14
private theorem k475_2_0 : check w475 pick475 2 t10108 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k475_2_1 : check w475 pick475 2 t10149 ⟨2,7,4,16,2,52,71,91⟩ = true := by decide +kernel
private theorem k475_2_2 : check w475 pick475 2 t10150 ⟨2,7,4,16,2,52,2,91⟩ = true := glue w475 pick475 2 ⟨2,7,4,16,2,52,2,91⟩ 3 70 t10108 t10149 k475_2_0 k475_2_1
private theorem k475_2_3 : check w475 pick475 2 t10156 ⟨2,7,4,16,2,52,92,450⟩ = true := by decide +kernel
private theorem k475_2_4 : check w475 pick475 2 t10157 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w475 pick475 2 ⟨2,7,4,16,0,52,0,450⟩ 3 91 t10150 t10156 k475_2_2 k475_2_3
theorem cov475_2 : PA.Covered 2 (OZ.Valid 2 w475.low w475.t w475.y w475.r w475.cap) (P33.root 2) :=
  Night6836Tree.sound w475 pick475 2 t10157 _ k475_2_4
theorem cov475_3 : PA.Covered 3 (OZ.Valid 3 w475.low w475.t w475.y w475.r w475.cap) (P33.root 3) :=
  Night6836Tree.sound w475 pick475 3 t564 _ (by decide +kernel)
theorem cov475_4 : PA.Covered 4 (OZ.Valid 4 w475.low w475.t w475.y w475.r w475.cap) (P33.root 4) :=
  Night6836Tree.sound w475 pick475 4 t565 _ (by decide +kernel)
theorem cov475_5 : PA.Covered 5 (OZ.Valid 5 w475.low w475.t w475.y w475.r w475.cap) (P33.root 5) :=
  Night6836Tree.sound w475 pick475 5 t566 _ (by decide +kernel)
theorem cov475_6 : PA.Covered 6 (OZ.Valid 6 w475.low w475.t w475.y w475.r w475.cap) (P33.root 6) :=
  Night6836Tree.sound w475 pick475 6 t567 _ (by decide +kernel)
theorem cov475_7 : PA.Covered 7 (OZ.Valid 7 w475.low w475.t w475.y w475.r w475.cap) (P33.root 7) :=
  Night6836Tree.sound w475 pick475 7 t568 _ (by decide +kernel)
theorem window475 : P33.WindowCount w475 := by
  apply P33.window_count w475 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov475_1
  · exact cov475_2
  · exact cov475_3
  · exact cov475_4
  · exact cov475_5
  · exact cov475_6
  · exact cov475_7
def w476 : P33.Window := ⟨8,32,7667,7630,244143069539988176,20685,15000,5000000,81920000000⟩
def h476_0 : Height w476 := ⟨20685,15000,by decide +kernel⟩
def h476_1 : Height w476 := ⟨26530,12000,by decide +kernel⟩
def pick476 (cl : ℕ) : Height w476 := if cl<36 then (h476_0) else (h476_1)
private theorem k476_1_0 : check w476 pick476 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k476_1_1 : check w476 pick476 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k476_1_2 : check w476 pick476 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w476 pick476 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k476_1_0 k476_1_1
private theorem k476_1_3 : check w476 pick476 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k476_1_4 : check w476 pick476 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w476 pick476 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k476_1_2 k476_1_3
private theorem k476_1_5 : check w476 pick476 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k476_1_6 : check w476 pick476 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k476_1_7 : check w476 pick476 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w476 pick476 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k476_1_5 k476_1_6
private theorem k476_1_8 : check w476 pick476 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k476_1_9 : check w476 pick476 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k476_1_10 : check w476 pick476 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w476 pick476 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k476_1_8 k476_1_9
private theorem k476_1_11 : check w476 pick476 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w476 pick476 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k476_1_7 k476_1_10
private theorem k476_1_12 : check w476 pick476 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w476 pick476 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k476_1_4 k476_1_11
theorem cov476_1 : PA.Covered 1 (OZ.Valid 1 w476.low w476.t w476.y w476.r w476.cap) (P33.root 1) :=
  Night6836Tree.sound w476 pick476 1 t10025 _ k476_1_12
private theorem k476_2_0 : check w476 pick476 2 t10027 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k476_2_1 : check w476 pick476 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k476_2_2 : check w476 pick476 2 t10028 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w476 pick476 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t10027 t9135 k476_2_0 k476_2_1
theorem cov476_2 : PA.Covered 2 (OZ.Valid 2 w476.low w476.t w476.y w476.r w476.cap) (P33.root 2) :=
  Night6836Tree.sound w476 pick476 2 t10028 _ k476_2_2
theorem cov476_3 : PA.Covered 3 (OZ.Valid 3 w476.low w476.t w476.y w476.r w476.cap) (P33.root 3) :=
  Night6836Tree.sound w476 pick476 3 t564 _ (by decide +kernel)
theorem cov476_4 : PA.Covered 4 (OZ.Valid 4 w476.low w476.t w476.y w476.r w476.cap) (P33.root 4) :=
  Night6836Tree.sound w476 pick476 4 t565 _ (by decide +kernel)
theorem cov476_5 : PA.Covered 5 (OZ.Valid 5 w476.low w476.t w476.y w476.r w476.cap) (P33.root 5) :=
  Night6836Tree.sound w476 pick476 5 t566 _ (by decide +kernel)
theorem cov476_6 : PA.Covered 6 (OZ.Valid 6 w476.low w476.t w476.y w476.r w476.cap) (P33.root 6) :=
  Night6836Tree.sound w476 pick476 6 t567 _ (by decide +kernel)
theorem cov476_7 : PA.Covered 7 (OZ.Valid 7 w476.low w476.t w476.y w476.r w476.cap) (P33.root 7) :=
  Night6836Tree.sound w476 pick476 7 t568 _ (by decide +kernel)
theorem window476 : P33.WindowCount w476 := by
  apply P33.window_count w476 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov476_1
  · exact cov476_2
  · exact cov476_3
  · exact cov476_4
  · exact cov476_5
  · exact cov476_6
  · exact cov476_7
def w477 : P33.Window := ⟨8,33,5432,4433,187852584888326116,35564,27000,5000000,81920000000⟩
def h477_0 : Height w477 := ⟨35564,27000,by decide +kernel⟩
def h477_1 : Height w477 := ⟨42212,23000,by decide +kernel⟩
def h477_2 : Height w477 := ⟨52543,19000,by decide +kernel⟩
def pick477 (cl : ℕ) : Height w477 := if cl<14 then (h477_0) else (if cl<172 then (h477_1) else (h477_2))
private theorem k477_1_0 : check w477 pick477 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k477_1_1 : check w477 pick477 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k477_1_2 : check w477 pick477 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w477 pick477 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k477_1_0 k477_1_1
private theorem k477_1_3 : check w477 pick477 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k477_1_4 : check w477 pick477 1 t10042 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w477 pick477 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10023 k477_1_2 k477_1_3
private theorem k477_1_5 : check w477 pick477 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k477_1_6 : check w477 pick477 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k477_1_7 : check w477 pick477 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w477 pick477 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k477_1_5 k477_1_6
private theorem k477_1_8 : check w477 pick477 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k477_1_9 : check w477 pick477 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k477_1_10 : check w477 pick477 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w477 pick477 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k477_1_8 k477_1_9
private theorem k477_1_11 : check w477 pick477 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w477 pick477 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k477_1_7 k477_1_10
private theorem k477_1_12 : check w477 pick477 1 t10043 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w477 pick477 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10042 t10007 k477_1_4 k477_1_11
theorem cov477_1 : PA.Covered 1 (OZ.Valid 1 w477.low w477.t w477.y w477.r w477.cap) (P33.root 1) :=
  Night6836Tree.sound w477 pick477 1 t10043 _ k477_1_12
theorem cov477_2 : PA.Covered 2 (OZ.Valid 2 w477.low w477.t w477.y w477.r w477.cap) (P33.root 2) :=
  Night6836Tree.sound w477 pick477 2 t10037 _ (by decide +kernel)
theorem cov477_3 : PA.Covered 3 (OZ.Valid 3 w477.low w477.t w477.y w477.r w477.cap) (P33.root 3) :=
  Night6836Tree.sound w477 pick477 3 t564 _ (by decide +kernel)
theorem cov477_4 : PA.Covered 4 (OZ.Valid 4 w477.low w477.t w477.y w477.r w477.cap) (P33.root 4) :=
  Night6836Tree.sound w477 pick477 4 t565 _ (by decide +kernel)
theorem cov477_5 : PA.Covered 5 (OZ.Valid 5 w477.low w477.t w477.y w477.r w477.cap) (P33.root 5) :=
  Night6836Tree.sound w477 pick477 5 t566 _ (by decide +kernel)
theorem cov477_6 : PA.Covered 6 (OZ.Valid 6 w477.low w477.t w477.y w477.r w477.cap) (P33.root 6) :=
  Night6836Tree.sound w477 pick477 6 t567 _ (by decide +kernel)
theorem cov477_7 : PA.Covered 7 (OZ.Valid 7 w477.low w477.t w477.y w477.r w477.cap) (P33.root 7) :=
  Night6836Tree.sound w477 pick477 7 t2134 _ (by decide +kernel)
theorem window477 : P33.WindowCount w477 := by
  apply P33.window_count w477 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov477_1
  · exact cov477_2
  · exact cov477_3
  · exact cov477_4
  · exact cov477_5
  · exact cov477_6
  · exact cov477_7
def w478 : P33.Window := ⟨8,33,7629,7514,244305791385195597,18388,18000,5000000,81920000000⟩
def h478_0 : Height w478 := ⟨18388,18000,by decide +kernel⟩
def h478_1 : Height w478 := ⟨22387,15000,by decide +kernel⟩
def h478_2 : Height w478 := ⟨28619,12000,by decide +kernel⟩
def h478_3 : Height w478 := ⟨42478,9000,by decide +kernel⟩
def pick478 (cl : ℕ) : Height w478 := if cl<44 then (if cl<2 then (h478_0) else (h478_1)) else (if cl<1021 then (h478_2) else (h478_3))
private theorem k478_1_0 : check w478 pick478 1 t10158 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k478_1_1 : check w478 pick478 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k478_1_2 : check w478 pick478 1 t10159 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w478 pick478 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10158 t9991 k478_1_0 k478_1_1
private theorem k478_1_3 : check w478 pick478 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k478_1_4 : check w478 pick478 1 t10160 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w478 pick478 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10159 t10023 k478_1_2 k478_1_3
private theorem k478_1_5 : check w478 pick478 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k478_1_6 : check w478 pick478 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k478_1_7 : check w478 pick478 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w478 pick478 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k478_1_5 k478_1_6
private theorem k478_1_8 : check w478 pick478 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k478_1_9 : check w478 pick478 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k478_1_10 : check w478 pick478 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w478 pick478 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k478_1_8 k478_1_9
private theorem k478_1_11 : check w478 pick478 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w478 pick478 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k478_1_7 k478_1_10
private theorem k478_1_12 : check w478 pick478 1 t10161 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w478 pick478 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10160 t10007 k478_1_4 k478_1_11
theorem cov478_1 : PA.Covered 1 (OZ.Valid 1 w478.low w478.t w478.y w478.r w478.cap) (P33.root 1) :=
  Night6836Tree.sound w478 pick478 1 t10161 _ k478_1_12
private theorem k478_2_0 : check w478 pick478 2 t10172 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k478_2_1 : check w478 pick478 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k478_2_2 : check w478 pick478 2 t10173 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w478 pick478 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t10172 t9135 k478_2_0 k478_2_1
theorem cov478_2 : PA.Covered 2 (OZ.Valid 2 w478.low w478.t w478.y w478.r w478.cap) (P33.root 2) :=
  Night6836Tree.sound w478 pick478 2 t10173 _ k478_2_2
theorem cov478_3 : PA.Covered 3 (OZ.Valid 3 w478.low w478.t w478.y w478.r w478.cap) (P33.root 3) :=
  Night6836Tree.sound w478 pick478 3 t564 _ (by decide +kernel)
theorem cov478_4 : PA.Covered 4 (OZ.Valid 4 w478.low w478.t w478.y w478.r w478.cap) (P33.root 4) :=
  Night6836Tree.sound w478 pick478 4 t565 _ (by decide +kernel)
theorem cov478_5 : PA.Covered 5 (OZ.Valid 5 w478.low w478.t w478.y w478.r w478.cap) (P33.root 5) :=
  Night6836Tree.sound w478 pick478 5 t566 _ (by decide +kernel)
theorem cov478_6 : PA.Covered 6 (OZ.Valid 6 w478.low w478.t w478.y w478.r w478.cap) (P33.root 6) :=
  Night6836Tree.sound w478 pick478 6 t567 _ (by decide +kernel)
theorem cov478_7 : PA.Covered 7 (OZ.Valid 7 w478.low w478.t w478.y w478.r w478.cap) (P33.root 7) :=
  Night6836Tree.sound w478 pick478 7 t568 _ (by decide +kernel)
theorem window478 : P33.WindowCount w478 := by
  apply P33.window_count w478 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov478_1
  · exact cov478_2
  · exact cov478_3
  · exact cov478_4
  · exact cov478_5
  · exact cov478_6
  · exact cov478_7
def w479 : P33.Window := ⟨8,34,5433,4434,191787023101827307,37235,27000,5000000,81920000000⟩
def h479_0 : Height w479 := ⟨37235,27000,by decide +kernel⟩
def h479_1 : Height w479 := ⟨44037,23000,by decide +kernel⟩
def h479_2 : Height w479 := ⟨54643,19000,by decide +kernel⟩
def pick479 (cl : ℕ) : Height w479 := if cl<18 then (h479_0) else (if cl<175 then (h479_1) else (h479_2))
private theorem k479_1_0 : check w479 pick479 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k479_1_1 : check w479 pick479 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k479_1_2 : check w479 pick479 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w479 pick479 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k479_1_0 k479_1_1
private theorem k479_1_3 : check w479 pick479 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k479_1_4 : check w479 pick479 1 t10042 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w479 pick479 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10023 k479_1_2 k479_1_3
private theorem k479_1_5 : check w479 pick479 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k479_1_6 : check w479 pick479 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k479_1_7 : check w479 pick479 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w479 pick479 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k479_1_5 k479_1_6
private theorem k479_1_8 : check w479 pick479 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k479_1_9 : check w479 pick479 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k479_1_10 : check w479 pick479 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w479 pick479 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k479_1_8 k479_1_9
private theorem k479_1_11 : check w479 pick479 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w479 pick479 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k479_1_7 k479_1_10
private theorem k479_1_12 : check w479 pick479 1 t10043 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w479 pick479 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10042 t10007 k479_1_4 k479_1_11
theorem cov479_1 : PA.Covered 1 (OZ.Valid 1 w479.low w479.t w479.y w479.r w479.cap) (P33.root 1) :=
  Night6836Tree.sound w479 pick479 1 t10043 _ k479_1_12
theorem cov479_2 : PA.Covered 2 (OZ.Valid 2 w479.low w479.t w479.y w479.r w479.cap) (P33.root 2) :=
  Night6836Tree.sound w479 pick479 2 t10037 _ (by decide +kernel)
theorem cov479_3 : PA.Covered 3 (OZ.Valid 3 w479.low w479.t w479.y w479.r w479.cap) (P33.root 3) :=
  Night6836Tree.sound w479 pick479 3 t564 _ (by decide +kernel)
theorem cov479_4 : PA.Covered 4 (OZ.Valid 4 w479.low w479.t w479.y w479.r w479.cap) (P33.root 4) :=
  Night6836Tree.sound w479 pick479 4 t565 _ (by decide +kernel)
theorem cov479_5 : PA.Covered 5 (OZ.Valid 5 w479.low w479.t w479.y w479.r w479.cap) (P33.root 5) :=
  Night6836Tree.sound w479 pick479 5 t566 _ (by decide +kernel)
theorem cov479_6 : PA.Covered 6 (OZ.Valid 6 w479.low w479.t w479.y w479.r w479.cap) (P33.root 6) :=
  Night6836Tree.sound w479 pick479 6 t567 _ (by decide +kernel)
theorem cov479_7 : PA.Covered 7 (OZ.Valid 7 w479.low w479.t w479.y w479.r w479.cap) (P33.root 7) :=
  Night6836Tree.sound w479 pick479 7 t2134 _ (by decide +kernel)
theorem window479 : P33.WindowCount w479 := by
  apply P33.window_count w479 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov479_1
  · exact cov479_2
  · exact cov479_3
  · exact cov479_4
  · exact cov479_5
  · exact cov479_6
  · exact cov479_7
end ProximityPrize.SubmissionLower.Night6836Bank
