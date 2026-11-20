/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT03
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w480 : P33.Window := ⟨8,34,7591,7553,244831023630579396,19124,18000,5000000,81920000000⟩
def h480_0 : Height w480 := ⟨19124,18000,by decide +kernel⟩
def h480_1 : Height w480 := ⟨23169,15000,by decide +kernel⟩
def h480_2 : Height w480 := ⟨29480,12000,by decide +kernel⟩
def h480_3 : Height w480 := ⟨43485,9000,by decide +kernel⟩
def pick480 (cl : ℕ) : Height w480 := if cl<49 then (if cl<2 then (h480_0) else (h480_1)) else (if cl<1021 then (h480_2) else (h480_3))
private theorem k480_1_0 : check w480 pick480 1 t10158 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k480_1_1 : check w480 pick480 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k480_1_2 : check w480 pick480 1 t10159 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w480 pick480 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10158 t9991 k480_1_0 k480_1_1
private theorem k480_1_3 : check w480 pick480 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k480_1_4 : check w480 pick480 1 t10160 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w480 pick480 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10159 t10023 k480_1_2 k480_1_3
private theorem k480_1_5 : check w480 pick480 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k480_1_6 : check w480 pick480 1 t10179 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k480_1_7 : check w480 pick480 1 t10180 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w480 pick480 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t10179 k480_1_5 k480_1_6
private theorem k480_1_8 : check w480 pick480 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k480_1_9 : check w480 pick480 1 t10183 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k480_1_10 : check w480 pick480 1 t10184 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w480 pick480 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10183 k480_1_8 k480_1_9
private theorem k480_1_11 : check w480 pick480 1 t10185 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w480 pick480 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t10180 t10184 k480_1_7 k480_1_10
private theorem k480_1_12 : check w480 pick480 1 t10186 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w480 pick480 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10160 t10185 k480_1_4 k480_1_11
theorem cov480_1 : PA.Covered 1 (OZ.Valid 1 w480.low w480.t w480.y w480.r w480.cap) (P33.root 1) :=
  Night6836Tree.sound w480 pick480 1 t10186 _ k480_1_12
private theorem k480_2_0 : check w480 pick480 2 t10189 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k480_2_1 : check w480 pick480 2 t10192 ⟨2,7,4,16,2,52,85,450⟩ = true := by decide +kernel
private theorem k480_2_2 : check w480 pick480 2 t10193 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w480 pick480 2 ⟨2,7,4,16,0,52,0,450⟩ 3 84 t10189 t10192 k480_2_0 k480_2_1
theorem cov480_2 : PA.Covered 2 (OZ.Valid 2 w480.low w480.t w480.y w480.r w480.cap) (P33.root 2) :=
  Night6836Tree.sound w480 pick480 2 t10193 _ k480_2_2
theorem cov480_3 : PA.Covered 3 (OZ.Valid 3 w480.low w480.t w480.y w480.r w480.cap) (P33.root 3) :=
  Night6836Tree.sound w480 pick480 3 t564 _ (by decide +kernel)
theorem cov480_4 : PA.Covered 4 (OZ.Valid 4 w480.low w480.t w480.y w480.r w480.cap) (P33.root 4) :=
  Night6836Tree.sound w480 pick480 4 t565 _ (by decide +kernel)
theorem cov480_5 : PA.Covered 5 (OZ.Valid 5 w480.low w480.t w480.y w480.r w480.cap) (P33.root 5) :=
  Night6836Tree.sound w480 pick480 5 t566 _ (by decide +kernel)
theorem cov480_6 : PA.Covered 6 (OZ.Valid 6 w480.low w480.t w480.y w480.r w480.cap) (P33.root 6) :=
  Night6836Tree.sound w480 pick480 6 t567 _ (by decide +kernel)
theorem cov480_7 : PA.Covered 7 (OZ.Valid 7 w480.low w480.t w480.y w480.r w480.cap) (P33.root 7) :=
  Night6836Tree.sound w480 pick480 7 t568 _ (by decide +kernel)
theorem window480 : P33.WindowCount w480 := by
  apply P33.window_count w480 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov480_1
  · exact cov480_2
  · exact cov480_3
  · exact cov480_4
  · exact cov480_5
  · exact cov480_6
  · exact cov480_7
def w481 : P33.Window := ⟨8,35,4634,3635,196752264386515675,44605,35000,5000000,81920000000⟩
def h481_0 : Height w481 := ⟨44605,35000,by decide +kernel⟩
def h481_1 : Height w481 := ⟨50468,31000,by decide +kernel⟩
def h481_2 : Height w481 := ⟨58243,27000,by decide +kernel⟩
def h481_3 : Height w481 := ⟨69810,23000,by decide +kernel⟩
def pick481 (cl : ℕ) : Height w481 := if cl<36 then (if cl<5 then (h481_0) else (h481_1)) else (if cl<260 then (h481_2) else (h481_3))
private theorem k481_1_0 : check w481 pick481 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k481_1_1 : check w481 pick481 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k481_1_2 : check w481 pick481 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w481 pick481 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k481_1_0 k481_1_1
private theorem k481_1_3 : check w481 pick481 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k481_1_4 : check w481 pick481 1 t10042 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w481 pick481 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10023 k481_1_2 k481_1_3
private theorem k481_1_5 : check w481 pick481 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k481_1_6 : check w481 pick481 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k481_1_7 : check w481 pick481 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w481 pick481 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k481_1_5 k481_1_6
private theorem k481_1_8 : check w481 pick481 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k481_1_9 : check w481 pick481 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k481_1_10 : check w481 pick481 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w481 pick481 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k481_1_8 k481_1_9
private theorem k481_1_11 : check w481 pick481 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w481 pick481 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k481_1_7 k481_1_10
private theorem k481_1_12 : check w481 pick481 1 t10043 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w481 pick481 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10042 t10007 k481_1_4 k481_1_11
theorem cov481_1 : PA.Covered 1 (OZ.Valid 1 w481.low w481.t w481.y w481.r w481.cap) (P33.root 1) :=
  Night6836Tree.sound w481 pick481 1 t10043 _ k481_1_12
theorem cov481_2 : PA.Covered 2 (OZ.Valid 2 w481.low w481.t w481.y w481.r w481.cap) (P33.root 2) :=
  Night6836Tree.sound w481 pick481 2 t10216 _ (by decide +kernel)
theorem cov481_3 : PA.Covered 3 (OZ.Valid 3 w481.low w481.t w481.y w481.r w481.cap) (P33.root 3) :=
  Night6836Tree.sound w481 pick481 3 t564 _ (by decide +kernel)
theorem cov481_4 : PA.Covered 4 (OZ.Valid 4 w481.low w481.t w481.y w481.r w481.cap) (P33.root 4) :=
  Night6836Tree.sound w481 pick481 4 t565 _ (by decide +kernel)
theorem cov481_5 : PA.Covered 5 (OZ.Valid 5 w481.low w481.t w481.y w481.r w481.cap) (P33.root 5) :=
  Night6836Tree.sound w481 pick481 5 t566 _ (by decide +kernel)
theorem cov481_6 : PA.Covered 6 (OZ.Valid 6 w481.low w481.t w481.y w481.r w481.cap) (P33.root 6) :=
  Night6836Tree.sound w481 pick481 6 t567 _ (by decide +kernel)
theorem cov481_7 : PA.Covered 7 (OZ.Valid 7 w481.low w481.t w481.y w481.r w481.cap) (P33.root 7) :=
  Night6836Tree.sound w481 pick481 7 t2134 _ (by decide +kernel)
theorem window481 : P33.WindowCount w481 := by
  apply P33.window_count w481 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov481_1
  · exact cov481_2
  · exact cov481_3
  · exact cov481_4
  · exact cov481_5
  · exact cov481_6
  · exact cov481_7
def w482 : P33.Window := ⟨8,35,5434,4435,195722179085441518,38905,27000,5000000,81920000000⟩
def h482_0 : Height w482 := ⟨38905,27000,by decide +kernel⟩
def h482_1 : Height w482 := ⟨45860,23000,by decide +kernel⟩
def h482_2 : Height w482 := ⟨56741,19000,by decide +kernel⟩
def pick482 (cl : ℕ) : Height w482 := if cl<32 then (h482_0) else (if cl<202 then (h482_1) else (h482_2))
private theorem k482_1_0 : check w482 pick482 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k482_1_1 : check w482 pick482 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k482_1_2 : check w482 pick482 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w482 pick482 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k482_1_0 k482_1_1
private theorem k482_1_3 : check w482 pick482 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k482_1_4 : check w482 pick482 1 t10042 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w482 pick482 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10023 k482_1_2 k482_1_3
private theorem k482_1_5 : check w482 pick482 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k482_1_6 : check w482 pick482 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k482_1_7 : check w482 pick482 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w482 pick482 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k482_1_5 k482_1_6
private theorem k482_1_8 : check w482 pick482 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k482_1_9 : check w482 pick482 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k482_1_10 : check w482 pick482 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w482 pick482 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k482_1_8 k482_1_9
private theorem k482_1_11 : check w482 pick482 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w482 pick482 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k482_1_7 k482_1_10
private theorem k482_1_12 : check w482 pick482 1 t10043 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w482 pick482 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10042 t10007 k482_1_4 k482_1_11
theorem cov482_1 : PA.Covered 1 (OZ.Valid 1 w482.low w482.t w482.y w482.r w482.cap) (P33.root 1) :=
  Night6836Tree.sound w482 pick482 1 t10043 _ k482_1_12
theorem cov482_2 : PA.Covered 2 (OZ.Valid 2 w482.low w482.t w482.y w482.r w482.cap) (P33.root 2) :=
  Night6836Tree.sound w482 pick482 2 t10037 _ (by decide +kernel)
theorem cov482_3 : PA.Covered 3 (OZ.Valid 3 w482.low w482.t w482.y w482.r w482.cap) (P33.root 3) :=
  Night6836Tree.sound w482 pick482 3 t564 _ (by decide +kernel)
theorem cov482_4 : PA.Covered 4 (OZ.Valid 4 w482.low w482.t w482.y w482.r w482.cap) (P33.root 4) :=
  Night6836Tree.sound w482 pick482 4 t565 _ (by decide +kernel)
theorem cov482_5 : PA.Covered 5 (OZ.Valid 5 w482.low w482.t w482.y w482.r w482.cap) (P33.root 5) :=
  Night6836Tree.sound w482 pick482 5 t566 _ (by decide +kernel)
theorem cov482_6 : PA.Covered 6 (OZ.Valid 6 w482.low w482.t w482.y w482.r w482.cap) (P33.root 6) :=
  Night6836Tree.sound w482 pick482 6 t567 _ (by decide +kernel)
theorem cov482_7 : PA.Covered 7 (OZ.Valid 7 w482.low w482.t w482.y w482.r w482.cap) (P33.root 7) :=
  Night6836Tree.sound w482 pick482 7 t2134 _ (by decide +kernel)
theorem window482 : P33.WindowCount w482 := by
  apply P33.window_count w482 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov482_1
  · exact cov482_2
  · exact cov482_3
  · exact cov482_4
  · exact cov482_5
  · exact cov482_6
  · exact cov482_7
def w483 : P33.Window := ⟨8,35,7552,7514,244870882960709231,20274,18000,5000000,81920000000⟩
def h483_0 : Height w483 := ⟨20274,18000,by decide +kernel⟩
def h483_1 : Height w483 := ⟨24444,15000,by decide +kernel⟩
def h483_2 : Height w483 := ⟨31000,12000,by decide +kernel⟩
def h483_3 : Height w483 := ⟨45695,9000,by decide +kernel⟩
def pick483 (cl : ℕ) : Height w483 := if cl<62 then (if cl<4 then (h483_0) else (h483_1)) else (if cl<1002 then (h483_2) else (h483_3))
private theorem k483_1_0 : check w483 pick483 1 t10217 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k483_1_1 : check w483 pick483 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k483_1_2 : check w483 pick483 1 t10218 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w483 pick483 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10217 t10040 k483_1_0 k483_1_1
private theorem k483_1_3 : check w483 pick483 1 t10223 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k483_1_4 : check w483 pick483 1 t10225 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k483_1_5 : check w483 pick483 1 t10226 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w483 pick483 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10223 t10225 k483_1_3 k483_1_4
private theorem k483_1_6 : check w483 pick483 1 t10227 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w483 pick483 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10218 t10226 k483_1_2 k483_1_5
private theorem k483_1_7 : check w483 pick483 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k483_1_8 : check w483 pick483 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k483_1_9 : check w483 pick483 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w483 pick483 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k483_1_7 k483_1_8
private theorem k483_1_10 : check w483 pick483 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k483_1_11 : check w483 pick483 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k483_1_12 : check w483 pick483 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w483 pick483 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k483_1_10 k483_1_11
private theorem k483_1_13 : check w483 pick483 1 t10228 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w483 pick483 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t10065 k483_1_9 k483_1_12
private theorem k483_1_14 : check w483 pick483 1 t10229 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w483 pick483 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10227 t10228 k483_1_6 k483_1_13
theorem cov483_1 : PA.Covered 1 (OZ.Valid 1 w483.low w483.t w483.y w483.r w483.cap) (P33.root 1) :=
  Night6836Tree.sound w483 pick483 1 t10229 _ k483_1_14
private theorem k483_2_0 : check w483 pick483 2 t10189 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k483_2_1 : check w483 pick483 2 t10192 ⟨2,7,4,16,2,52,85,450⟩ = true := by decide +kernel
private theorem k483_2_2 : check w483 pick483 2 t10193 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w483 pick483 2 ⟨2,7,4,16,0,52,0,450⟩ 3 84 t10189 t10192 k483_2_0 k483_2_1
theorem cov483_2 : PA.Covered 2 (OZ.Valid 2 w483.low w483.t w483.y w483.r w483.cap) (P33.root 2) :=
  Night6836Tree.sound w483 pick483 2 t10193 _ k483_2_2
theorem cov483_3 : PA.Covered 3 (OZ.Valid 3 w483.low w483.t w483.y w483.r w483.cap) (P33.root 3) :=
  Night6836Tree.sound w483 pick483 3 t564 _ (by decide +kernel)
theorem cov483_4 : PA.Covered 4 (OZ.Valid 4 w483.low w483.t w483.y w483.r w483.cap) (P33.root 4) :=
  Night6836Tree.sound w483 pick483 4 t565 _ (by decide +kernel)
theorem cov483_5 : PA.Covered 5 (OZ.Valid 5 w483.low w483.t w483.y w483.r w483.cap) (P33.root 5) :=
  Night6836Tree.sound w483 pick483 5 t566 _ (by decide +kernel)
theorem cov483_6 : PA.Covered 6 (OZ.Valid 6 w483.low w483.t w483.y w483.r w483.cap) (P33.root 6) :=
  Night6836Tree.sound w483 pick483 6 t567 _ (by decide +kernel)
theorem cov483_7 : PA.Covered 7 (OZ.Valid 7 w483.low w483.t w483.y w483.r w483.cap) (P33.root 7) :=
  Night6836Tree.sound w483 pick483 7 t568 _ (by decide +kernel)
theorem window483 : P33.WindowCount w483 := by
  apply P33.window_count w483 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov483_1
  · exact cov483_2
  · exact cov483_3
  · exact cov483_4
  · exact cov483_5
  · exact cov483_6
  · exact cov483_7
def w484 : P33.Window := ⟨8,36,5435,4436,199658052839168747,35313,31000,5000000,81920000000⟩
def h484_0 : Height w484 := ⟨35313,31000,by decide +kernel⟩
def h484_1 : Height w484 := ⟨40573,27000,by decide +kernel⟩
def h484_2 : Height w484 := ⟨47682,23000,by decide +kernel⟩
def h484_3 : Height w484 := ⟨58836,19000,by decide +kernel⟩
def pick484 (cl : ℕ) : Height w484 := if cl<32 then (if cl<2 then (h484_0) else (h484_1)) else (if cl<221 then (h484_2) else (h484_3))
private theorem k484_1_0 : check w484 pick484 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k484_1_1 : check w484 pick484 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k484_1_2 : check w484 pick484 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w484 pick484 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k484_1_0 k484_1_1
private theorem k484_1_3 : check w484 pick484 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k484_1_4 : check w484 pick484 1 t10042 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w484 pick484 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10023 k484_1_2 k484_1_3
private theorem k484_1_5 : check w484 pick484 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k484_1_6 : check w484 pick484 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k484_1_7 : check w484 pick484 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w484 pick484 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k484_1_5 k484_1_6
private theorem k484_1_8 : check w484 pick484 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k484_1_9 : check w484 pick484 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k484_1_10 : check w484 pick484 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w484 pick484 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k484_1_8 k484_1_9
private theorem k484_1_11 : check w484 pick484 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w484 pick484 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k484_1_7 k484_1_10
private theorem k484_1_12 : check w484 pick484 1 t10043 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w484 pick484 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10042 t10007 k484_1_4 k484_1_11
theorem cov484_1 : PA.Covered 1 (OZ.Valid 1 w484.low w484.t w484.y w484.r w484.cap) (P33.root 1) :=
  Night6836Tree.sound w484 pick484 1 t10043 _ k484_1_12
theorem cov484_2 : PA.Covered 2 (OZ.Valid 2 w484.low w484.t w484.y w484.r w484.cap) (P33.root 2) :=
  Night6836Tree.sound w484 pick484 2 t10037 _ (by decide +kernel)
theorem cov484_3 : PA.Covered 3 (OZ.Valid 3 w484.low w484.t w484.y w484.r w484.cap) (P33.root 3) :=
  Night6836Tree.sound w484 pick484 3 t564 _ (by decide +kernel)
theorem cov484_4 : PA.Covered 4 (OZ.Valid 4 w484.low w484.t w484.y w484.r w484.cap) (P33.root 4) :=
  Night6836Tree.sound w484 pick484 4 t565 _ (by decide +kernel)
theorem cov484_5 : PA.Covered 5 (OZ.Valid 5 w484.low w484.t w484.y w484.r w484.cap) (P33.root 5) :=
  Night6836Tree.sound w484 pick484 5 t566 _ (by decide +kernel)
theorem cov484_6 : PA.Covered 6 (OZ.Valid 6 w484.low w484.t w484.y w484.r w484.cap) (P33.root 6) :=
  Night6836Tree.sound w484 pick484 6 t567 _ (by decide +kernel)
theorem cov484_7 : PA.Covered 7 (OZ.Valid 7 w484.low w484.t w484.y w484.r w484.cap) (P33.root 7) :=
  Night6836Tree.sound w484 pick484 7 t2134 _ (by decide +kernel)
theorem window484 : P33.WindowCount w484 := by
  apply P33.window_count w484 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov484_1
  · exact cov484_2
  · exact cov484_3
  · exact cov484_4
  · exact cov484_5
  · exact cov484_6
  · exact cov484_7
def w485 : P33.Window := ⟨8,36,7513,7333,240039365143510950,22286,18000,5000000,81920000000⟩
def h485_0 : Height w485 := ⟨22286,18000,by decide +kernel⟩
def h485_1 : Height w485 := ⟨26748,15000,by decide +kernel⟩
def h485_2 : Height w485 := ⟨33908,12000,by decide +kernel⟩
def h485_3 : Height w485 := ⟨50500,9000,by decide +kernel⟩
def pick485 (cl : ℕ) : Height w485 := if cl<102 then (if cl<5 then (h485_0) else (h485_1)) else (if cl<1021 then (h485_2) else (h485_3))
private theorem k485_1_0 : check w485 pick485 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k485_1_1 : check w485 pick485 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k485_1_2 : check w485 pick485 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w485 pick485 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k485_1_0 k485_1_1
private theorem k485_1_3 : check w485 pick485 1 t10054 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k485_1_4 : check w485 pick485 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k485_1_5 : check w485 pick485 1 t10059 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w485 pick485 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10054 t10058 k485_1_3 k485_1_4
private theorem k485_1_6 : check w485 pick485 1 t10235 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w485 pick485 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10059 k485_1_2 k485_1_5
private theorem k485_1_7 : check w485 pick485 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k485_1_8 : check w485 pick485 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k485_1_9 : check w485 pick485 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w485 pick485 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k485_1_7 k485_1_8
private theorem k485_1_10 : check w485 pick485 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k485_1_11 : check w485 pick485 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k485_1_12 : check w485 pick485 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w485 pick485 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k485_1_10 k485_1_11
private theorem k485_1_13 : check w485 pick485 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w485 pick485 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k485_1_9 k485_1_12
private theorem k485_1_14 : check w485 pick485 1 t10236 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w485 pick485 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10235 t10066 k485_1_6 k485_1_13
theorem cov485_1 : PA.Covered 1 (OZ.Valid 1 w485.low w485.t w485.y w485.r w485.cap) (P33.root 1) :=
  Night6836Tree.sound w485 pick485 1 t10236 _ k485_1_14
private theorem k485_2_0 : check w485 pick485 2 t10189 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k485_2_1 : check w485 pick485 2 t10239 ⟨2,7,4,16,2,52,85,450⟩ = true := by decide +kernel
private theorem k485_2_2 : check w485 pick485 2 t10240 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w485 pick485 2 ⟨2,7,4,16,0,52,0,450⟩ 3 84 t10189 t10239 k485_2_0 k485_2_1
theorem cov485_2 : PA.Covered 2 (OZ.Valid 2 w485.low w485.t w485.y w485.r w485.cap) (P33.root 2) :=
  Night6836Tree.sound w485 pick485 2 t10240 _ k485_2_2
theorem cov485_3 : PA.Covered 3 (OZ.Valid 3 w485.low w485.t w485.y w485.r w485.cap) (P33.root 3) :=
  Night6836Tree.sound w485 pick485 3 t564 _ (by decide +kernel)
theorem cov485_4 : PA.Covered 4 (OZ.Valid 4 w485.low w485.t w485.y w485.r w485.cap) (P33.root 4) :=
  Night6836Tree.sound w485 pick485 4 t565 _ (by decide +kernel)
theorem cov485_5 : PA.Covered 5 (OZ.Valid 5 w485.low w485.t w485.y w485.r w485.cap) (P33.root 5) :=
  Night6836Tree.sound w485 pick485 5 t566 _ (by decide +kernel)
theorem cov485_6 : PA.Covered 6 (OZ.Valid 6 w485.low w485.t w485.y w485.r w485.cap) (P33.root 6) :=
  Night6836Tree.sound w485 pick485 6 t567 _ (by decide +kernel)
theorem cov485_7 : PA.Covered 7 (OZ.Valid 7 w485.low w485.t w485.y w485.r w485.cap) (P33.root 7) :=
  Night6836Tree.sound w485 pick485 7 t568 _ (by decide +kernel)
theorem window485 : P33.WindowCount w485 := by
  apply P33.window_count w485 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov485_1
  · exact cov485_2
  · exact cov485_3
  · exact cov485_4
  · exact cov485_5
  · exact cov485_6
  · exact cov485_7
def w486 : P33.Window := ⟨8,37,7472,7428,244063871280048779,22674,18000,5000000,81920000000⟩
def h486_0 : Height w486 := ⟨22674,18000,by decide +kernel⟩
def h486_1 : Height w486 := ⟨27114,15000,by decide +kernel⟩
def h486_2 : Height w486 := ⟨34202,12000,by decide +kernel⟩
def h486_3 : Height w486 := ⟨50425,9000,by decide +kernel⟩
def pick486 (cl : ℕ) : Height w486 := if cl<98 then (if cl<5 then (h486_0) else (h486_1)) else (if cl<1021 then (h486_2) else (h486_3))
private theorem k486_1_0 : check w486 pick486 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k486_1_1 : check w486 pick486 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k486_1_2 : check w486 pick486 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w486 pick486 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k486_1_0 k486_1_1
private theorem k486_1_3 : check w486 pick486 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k486_1_4 : check w486 pick486 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k486_1_5 : check w486 pick486 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w486 pick486 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k486_1_3 k486_1_4
private theorem k486_1_6 : check w486 pick486 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w486 pick486 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k486_1_2 k486_1_5
private theorem k486_1_7 : check w486 pick486 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k486_1_8 : check w486 pick486 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k486_1_9 : check w486 pick486 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w486 pick486 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k486_1_7 k486_1_8
private theorem k486_1_10 : check w486 pick486 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k486_1_11 : check w486 pick486 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k486_1_12 : check w486 pick486 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w486 pick486 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k486_1_10 k486_1_11
private theorem k486_1_13 : check w486 pick486 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w486 pick486 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k486_1_9 k486_1_12
private theorem k486_1_14 : check w486 pick486 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w486 pick486 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k486_1_6 k486_1_13
theorem cov486_1 : PA.Covered 1 (OZ.Valid 1 w486.low w486.t w486.y w486.r w486.cap) (P33.root 1) :=
  Night6836Tree.sound w486 pick486 1 t10243 _ k486_1_14
private theorem k486_2_0 : check w486 pick486 2 t10189 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k486_2_1 : check w486 pick486 2 t10239 ⟨2,7,4,16,2,52,85,450⟩ = true := by decide +kernel
private theorem k486_2_2 : check w486 pick486 2 t10240 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w486 pick486 2 ⟨2,7,4,16,0,52,0,450⟩ 3 84 t10189 t10239 k486_2_0 k486_2_1
theorem cov486_2 : PA.Covered 2 (OZ.Valid 2 w486.low w486.t w486.y w486.r w486.cap) (P33.root 2) :=
  Night6836Tree.sound w486 pick486 2 t10240 _ k486_2_2
theorem cov486_3 : PA.Covered 3 (OZ.Valid 3 w486.low w486.t w486.y w486.r w486.cap) (P33.root 3) :=
  Night6836Tree.sound w486 pick486 3 t564 _ (by decide +kernel)
theorem cov486_4 : PA.Covered 4 (OZ.Valid 4 w486.low w486.t w486.y w486.r w486.cap) (P33.root 4) :=
  Night6836Tree.sound w486 pick486 4 t565 _ (by decide +kernel)
theorem cov486_5 : PA.Covered 5 (OZ.Valid 5 w486.low w486.t w486.y w486.r w486.cap) (P33.root 5) :=
  Night6836Tree.sound w486 pick486 5 t566 _ (by decide +kernel)
theorem cov486_6 : PA.Covered 6 (OZ.Valid 6 w486.low w486.t w486.y w486.r w486.cap) (P33.root 6) :=
  Night6836Tree.sound w486 pick486 6 t567 _ (by decide +kernel)
theorem cov486_7 : PA.Covered 7 (OZ.Valid 7 w486.low w486.t w486.y w486.r w486.cap) (P33.root 7) :=
  Night6836Tree.sound w486 pick486 7 t568 _ (by decide +kernel)
theorem window486 : P33.WindowCount w486 := by
  apply P33.window_count w486 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov486_1
  · exact cov486_2
  · exact cov486_3
  · exact cov486_4
  · exact cov486_5
  · exact cov486_6
  · exact cov486_7
def w487 : P33.Window := ⟨8,38,5437,4438,201675960250502626,38448,31000,5000000,81920000000⟩
def h487_0 : Height w487 := ⟨38448,31000,by decide +kernel⟩
def h487_1 : Height w487 := ⟨43904,27000,by decide +kernel⟩
def h487_2 : Height w487 := ⟨51320,23000,by decide +kernel⟩
def h487_3 : Height w487 := ⟨63018,19000,by decide +kernel⟩
def pick487 (cl : ℕ) : Height w487 := if cl<32 then (if cl<2 then (h487_0) else (h487_1)) else (if cl<264 then (h487_2) else (h487_3))
private theorem k487_1_0 : check w487 pick487 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k487_1_1 : check w487 pick487 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k487_1_2 : check w487 pick487 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w487 pick487 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k487_1_0 k487_1_1
private theorem k487_1_3 : check w487 pick487 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k487_1_4 : check w487 pick487 1 t10042 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w487 pick487 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10023 k487_1_2 k487_1_3
private theorem k487_1_5 : check w487 pick487 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k487_1_6 : check w487 pick487 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k487_1_7 : check w487 pick487 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w487 pick487 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k487_1_5 k487_1_6
private theorem k487_1_8 : check w487 pick487 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k487_1_9 : check w487 pick487 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k487_1_10 : check w487 pick487 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w487 pick487 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k487_1_8 k487_1_9
private theorem k487_1_11 : check w487 pick487 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w487 pick487 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k487_1_7 k487_1_10
private theorem k487_1_12 : check w487 pick487 1 t10043 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w487 pick487 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10042 t10007 k487_1_4 k487_1_11
theorem cov487_1 : PA.Covered 1 (OZ.Valid 1 w487.low w487.t w487.y w487.r w487.cap) (P33.root 1) :=
  Night6836Tree.sound w487 pick487 1 t10043 _ k487_1_12
private theorem k487_2_0 : check w487 pick487 2 t10244 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k487_2_1 : check w487 pick487 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k487_2_2 : check w487 pick487 2 t10245 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w487 pick487 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t10244 t9133 k487_2_0 k487_2_1
theorem cov487_2 : PA.Covered 2 (OZ.Valid 2 w487.low w487.t w487.y w487.r w487.cap) (P33.root 2) :=
  Night6836Tree.sound w487 pick487 2 t10245 _ k487_2_2
theorem cov487_3 : PA.Covered 3 (OZ.Valid 3 w487.low w487.t w487.y w487.r w487.cap) (P33.root 3) :=
  Night6836Tree.sound w487 pick487 3 t564 _ (by decide +kernel)
theorem cov487_4 : PA.Covered 4 (OZ.Valid 4 w487.low w487.t w487.y w487.r w487.cap) (P33.root 4) :=
  Night6836Tree.sound w487 pick487 4 t565 _ (by decide +kernel)
theorem cov487_5 : PA.Covered 5 (OZ.Valid 5 w487.low w487.t w487.y w487.r w487.cap) (P33.root 5) :=
  Night6836Tree.sound w487 pick487 5 t566 _ (by decide +kernel)
theorem cov487_6 : PA.Covered 6 (OZ.Valid 6 w487.low w487.t w487.y w487.r w487.cap) (P33.root 6) :=
  Night6836Tree.sound w487 pick487 6 t567 _ (by decide +kernel)
theorem cov487_7 : PA.Covered 7 (OZ.Valid 7 w487.low w487.t w487.y w487.r w487.cap) (P33.root 7) :=
  Night6836Tree.sound w487 pick487 7 t2134 _ (by decide +kernel)
theorem window487 : P33.WindowCount w487 := by
  apply P33.window_count w487 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov487_1
  · exact cov487_2
  · exact cov487_3
  · exact cov487_4
  · exact cov487_5
  · exact cov487_6
  · exact cov487_7
def w488 : P33.Window := ⟨8,38,7332,6383,243598432675763428,27430,21000,5000000,81920000000⟩
def h488_0 : Height w488 := ⟨27430,21000,by decide +kernel⟩
def h488_1 : Height w488 := ⟨31805,18000,by decide +kernel⟩
def h488_2 : Height w488 := ⟨38140,15000,by decide +kernel⟩
def h488_3 : Height w488 := ⟨49477,12000,by decide +kernel⟩
def pick488 (cl : ℕ) : Height w488 := if cl<49 then (if cl<5 then (h488_0) else (h488_1)) else (if cl<853 then (h488_2) else (h488_3))
private theorem k488_1_0 : check w488 pick488 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k488_1_1 : check w488 pick488 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k488_1_2 : check w488 pick488 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w488 pick488 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k488_1_0 k488_1_1
private theorem k488_1_3 : check w488 pick488 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k488_1_4 : check w488 pick488 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k488_1_5 : check w488 pick488 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w488 pick488 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k488_1_3 k488_1_4
private theorem k488_1_6 : check w488 pick488 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w488 pick488 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k488_1_2 k488_1_5
private theorem k488_1_7 : check w488 pick488 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k488_1_8 : check w488 pick488 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k488_1_9 : check w488 pick488 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w488 pick488 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k488_1_7 k488_1_8
private theorem k488_1_10 : check w488 pick488 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k488_1_11 : check w488 pick488 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k488_1_12 : check w488 pick488 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w488 pick488 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k488_1_10 k488_1_11
private theorem k488_1_13 : check w488 pick488 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w488 pick488 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k488_1_9 k488_1_12
private theorem k488_1_14 : check w488 pick488 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w488 pick488 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k488_1_6 k488_1_13
theorem cov488_1 : PA.Covered 1 (OZ.Valid 1 w488.low w488.t w488.y w488.r w488.cap) (P33.root 1) :=
  Night6836Tree.sound w488 pick488 1 t10243 _ k488_1_14
private theorem k488_2_0 : check w488 pick488 2 t10248 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k488_2_1 : check w488 pick488 2 t10239 ⟨2,7,4,16,2,52,85,450⟩ = true := by decide +kernel
private theorem k488_2_2 : check w488 pick488 2 t10249 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w488 pick488 2 ⟨2,7,4,16,0,52,0,450⟩ 3 84 t10248 t10239 k488_2_0 k488_2_1
theorem cov488_2 : PA.Covered 2 (OZ.Valid 2 w488.low w488.t w488.y w488.r w488.cap) (P33.root 2) :=
  Night6836Tree.sound w488 pick488 2 t10249 _ k488_2_2
theorem cov488_3 : PA.Covered 3 (OZ.Valid 3 w488.low w488.t w488.y w488.r w488.cap) (P33.root 3) :=
  Night6836Tree.sound w488 pick488 3 t564 _ (by decide +kernel)
theorem cov488_4 : PA.Covered 4 (OZ.Valid 4 w488.low w488.t w488.y w488.r w488.cap) (P33.root 4) :=
  Night6836Tree.sound w488 pick488 4 t565 _ (by decide +kernel)
theorem cov488_5 : PA.Covered 5 (OZ.Valid 5 w488.low w488.t w488.y w488.r w488.cap) (P33.root 5) :=
  Night6836Tree.sound w488 pick488 5 t566 _ (by decide +kernel)
theorem cov488_6 : PA.Covered 6 (OZ.Valid 6 w488.low w488.t w488.y w488.r w488.cap) (P33.root 6) :=
  Night6836Tree.sound w488 pick488 6 t567 _ (by decide +kernel)
theorem cov488_7 : PA.Covered 7 (OZ.Valid 7 w488.low w488.t w488.y w488.r w488.cap) (P33.root 7) :=
  Night6836Tree.sound w488 pick488 7 t568 _ (by decide +kernel)
theorem window488 : P33.WindowCount w488 := by
  apply P33.window_count w488 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov488_1
  · exact cov488_2
  · exact cov488_3
  · exact cov488_4
  · exact cov488_5
  · exact cov488_6
  · exact cov488_7
def w489 : P33.Window := ⟨8,38,7427,7382,245344019791064242,23923,18000,5000000,81920000000⟩
def h489_0 : Height w489 := ⟨23923,18000,by decide +kernel⟩
def h489_1 : Height w489 := ⟨28507,15000,by decide +kernel⟩
def h489_2 : Height w489 := ⟨35884,12000,by decide +kernel⟩
def pick489 (cl : ℕ) : Height w489 := if cl<6 then (h489_0) else (if cl<117 then (h489_1) else (h489_2))
private theorem k489_1_0 : check w489 pick489 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k489_1_1 : check w489 pick489 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k489_1_2 : check w489 pick489 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w489 pick489 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k489_1_0 k489_1_1
private theorem k489_1_3 : check w489 pick489 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k489_1_4 : check w489 pick489 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k489_1_5 : check w489 pick489 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w489 pick489 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k489_1_3 k489_1_4
private theorem k489_1_6 : check w489 pick489 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w489 pick489 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k489_1_2 k489_1_5
private theorem k489_1_7 : check w489 pick489 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k489_1_8 : check w489 pick489 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k489_1_9 : check w489 pick489 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w489 pick489 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k489_1_7 k489_1_8
private theorem k489_1_10 : check w489 pick489 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k489_1_11 : check w489 pick489 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k489_1_12 : check w489 pick489 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w489 pick489 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k489_1_10 k489_1_11
private theorem k489_1_13 : check w489 pick489 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w489 pick489 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k489_1_9 k489_1_12
private theorem k489_1_14 : check w489 pick489 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w489 pick489 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k489_1_6 k489_1_13
theorem cov489_1 : PA.Covered 1 (OZ.Valid 1 w489.low w489.t w489.y w489.r w489.cap) (P33.root 1) :=
  Night6836Tree.sound w489 pick489 1 t10243 _ k489_1_14
private theorem k489_2_0 : check w489 pick489 2 t10251 ⟨2,7,4,16,2,52,2,63⟩ = true := by decide +kernel
private theorem k489_2_1 : check w489 pick489 2 t10254 ⟨2,7,4,16,2,52,64,91⟩ = true := by decide +kernel
private theorem k489_2_2 : check w489 pick489 2 t10255 ⟨2,7,4,16,2,52,2,91⟩ = true := glue w489 pick489 2 ⟨2,7,4,16,2,52,2,91⟩ 3 63 t10251 t10254 k489_2_0 k489_2_1
private theorem k489_2_3 : check w489 pick489 2 t10263 ⟨2,7,4,16,2,52,92,450⟩ = true := by decide +kernel
private theorem k489_2_4 : check w489 pick489 2 t10264 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w489 pick489 2 ⟨2,7,4,16,0,52,0,450⟩ 3 91 t10255 t10263 k489_2_2 k489_2_3
theorem cov489_2 : PA.Covered 2 (OZ.Valid 2 w489.low w489.t w489.y w489.r w489.cap) (P33.root 2) :=
  Night6836Tree.sound w489 pick489 2 t10264 _ k489_2_4
theorem cov489_3 : PA.Covered 3 (OZ.Valid 3 w489.low w489.t w489.y w489.r w489.cap) (P33.root 3) :=
  Night6836Tree.sound w489 pick489 3 t564 _ (by decide +kernel)
theorem cov489_4 : PA.Covered 4 (OZ.Valid 4 w489.low w489.t w489.y w489.r w489.cap) (P33.root 4) :=
  Night6836Tree.sound w489 pick489 4 t565 _ (by decide +kernel)
theorem cov489_5 : PA.Covered 5 (OZ.Valid 5 w489.low w489.t w489.y w489.r w489.cap) (P33.root 5) :=
  Night6836Tree.sound w489 pick489 5 t566 _ (by decide +kernel)
theorem cov489_6 : PA.Covered 6 (OZ.Valid 6 w489.low w489.t w489.y w489.r w489.cap) (P33.root 6) :=
  Night6836Tree.sound w489 pick489 6 t567 _ (by decide +kernel)
theorem cov489_7 : PA.Covered 7 (OZ.Valid 7 w489.low w489.t w489.y w489.r w489.cap) (P33.root 7) :=
  Night6836Tree.sound w489 pick489 7 t568 _ (by decide +kernel)
theorem window489 : P33.WindowCount w489 := by
  apply P33.window_count w489 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov489_1
  · exact cov489_2
  · exact cov489_3
  · exact cov489_4
  · exact cov489_5
  · exact cov489_6
  · exact cov489_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w490 : P33.Window := ⟨8,39,5438,4439,203424451993211678,40014,31000,5000000,81920000000⟩
def h490_0 : Height w490 := ⟨40014,31000,by decide +kernel⟩
def h490_1 : Height w490 := ⟨45568,27000,by decide +kernel⟩
def h490_2 : Height w490 := ⟨53137,23000,by decide +kernel⟩
def h490_3 : Height w490 := ⟨65105,19000,by decide +kernel⟩
def pick490 (cl : ℕ) : Height w490 := if cl<32 then (if cl<4 then (h490_0) else (h490_1)) else (if cl<279 then (h490_2) else (h490_3))
private theorem k490_1_0 : check w490 pick490 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k490_1_1 : check w490 pick490 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k490_1_2 : check w490 pick490 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w490 pick490 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k490_1_0 k490_1_1
private theorem k490_1_3 : check w490 pick490 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k490_1_4 : check w490 pick490 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w490 pick490 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k490_1_2 k490_1_3
private theorem k490_1_5 : check w490 pick490 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k490_1_6 : check w490 pick490 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k490_1_7 : check w490 pick490 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w490 pick490 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k490_1_5 k490_1_6
private theorem k490_1_8 : check w490 pick490 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k490_1_9 : check w490 pick490 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k490_1_10 : check w490 pick490 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w490 pick490 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k490_1_8 k490_1_9
private theorem k490_1_11 : check w490 pick490 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w490 pick490 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k490_1_7 k490_1_10
private theorem k490_1_12 : check w490 pick490 1 t10267 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w490 pick490 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10007 k490_1_4 k490_1_11
theorem cov490_1 : PA.Covered 1 (OZ.Valid 1 w490.low w490.t w490.y w490.r w490.cap) (P33.root 1) :=
  Night6836Tree.sound w490 pick490 1 t10267 _ k490_1_12
private theorem k490_2_0 : check w490 pick490 2 t10269 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k490_2_1 : check w490 pick490 2 t10273 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k490_2_2 : check w490 pick490 2 t10274 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w490 pick490 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10269 t10273 k490_2_0 k490_2_1
theorem cov490_2 : PA.Covered 2 (OZ.Valid 2 w490.low w490.t w490.y w490.r w490.cap) (P33.root 2) :=
  Night6836Tree.sound w490 pick490 2 t10274 _ k490_2_2
theorem cov490_3 : PA.Covered 3 (OZ.Valid 3 w490.low w490.t w490.y w490.r w490.cap) (P33.root 3) :=
  Night6836Tree.sound w490 pick490 3 t564 _ (by decide +kernel)
theorem cov490_4 : PA.Covered 4 (OZ.Valid 4 w490.low w490.t w490.y w490.r w490.cap) (P33.root 4) :=
  Night6836Tree.sound w490 pick490 4 t565 _ (by decide +kernel)
theorem cov490_5 : PA.Covered 5 (OZ.Valid 5 w490.low w490.t w490.y w490.r w490.cap) (P33.root 5) :=
  Night6836Tree.sound w490 pick490 5 t566 _ (by decide +kernel)
theorem cov490_6 : PA.Covered 6 (OZ.Valid 6 w490.low w490.t w490.y w490.r w490.cap) (P33.root 6) :=
  Night6836Tree.sound w490 pick490 6 t567 _ (by decide +kernel)
theorem cov490_7 : PA.Covered 7 (OZ.Valid 7 w490.low w490.t w490.y w490.r w490.cap) (P33.root 7) :=
  Night6836Tree.sound w490 pick490 7 t2134 _ (by decide +kernel)
theorem window490 : P33.WindowCount w490 := by
  apply P33.window_count w490 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov490_1
  · exact cov490_2
  · exact cov490_3
  · exact cov490_4
  · exact cov490_5
  · exact cov490_6
  · exact cov490_7
def w491 : P33.Window := ⟨8,39,7381,7336,245325777105811246,25195,18000,5000000,81920000000⟩
def h491_0 : Height w491 := ⟨25195,18000,by decide +kernel⟩
def h491_1 : Height w491 := ⟨29928,15000,by decide +kernel⟩
def h491_2 : Height w491 := ⟨37604,12000,by decide +kernel⟩
def pick491 (cl : ℕ) : Height w491 := if cl<10 then (h491_0) else (if cl<157 then (h491_1) else (h491_2))
private theorem k491_1_0 : check w491 pick491 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k491_1_1 : check w491 pick491 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k491_1_2 : check w491 pick491 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w491 pick491 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k491_1_0 k491_1_1
private theorem k491_1_3 : check w491 pick491 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k491_1_4 : check w491 pick491 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k491_1_5 : check w491 pick491 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w491 pick491 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k491_1_3 k491_1_4
private theorem k491_1_6 : check w491 pick491 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w491 pick491 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k491_1_2 k491_1_5
private theorem k491_1_7 : check w491 pick491 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k491_1_8 : check w491 pick491 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k491_1_9 : check w491 pick491 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w491 pick491 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k491_1_7 k491_1_8
private theorem k491_1_10 : check w491 pick491 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k491_1_11 : check w491 pick491 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k491_1_12 : check w491 pick491 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w491 pick491 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k491_1_10 k491_1_11
private theorem k491_1_13 : check w491 pick491 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w491 pick491 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k491_1_9 k491_1_12
private theorem k491_1_14 : check w491 pick491 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w491 pick491 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k491_1_6 k491_1_13
theorem cov491_1 : PA.Covered 1 (OZ.Valid 1 w491.low w491.t w491.y w491.r w491.cap) (P33.root 1) :=
  Night6836Tree.sound w491 pick491 1 t10243 _ k491_1_14
private theorem k491_2_0 : check w491 pick491 2 t10300 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k491_2_1 : check w491 pick491 2 t10328 ⟨2,7,4,16,2,52,71,98⟩ = true := by decide +kernel
private theorem k491_2_2 : check w491 pick491 2 t10329 ⟨2,7,4,16,2,52,2,98⟩ = true := glue w491 pick491 2 ⟨2,7,4,16,2,52,2,98⟩ 3 70 t10300 t10328 k491_2_0 k491_2_1
private theorem k491_2_3 : check w491 pick491 2 t10336 ⟨2,7,4,16,2,52,99,193⟩ = true := by decide +kernel
private theorem k491_2_4 : check w491 pick491 2 t10349 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k491_2_5 : check w491 pick491 2 t10350 ⟨2,7,4,16,2,52,99,450⟩ = true := glue w491 pick491 2 ⟨2,7,4,16,2,52,99,450⟩ 3 193 t10336 t10349 k491_2_3 k491_2_4
private theorem k491_2_6 : check w491 pick491 2 t10351 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w491 pick491 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t10329 t10350 k491_2_2 k491_2_5
theorem cov491_2 : PA.Covered 2 (OZ.Valid 2 w491.low w491.t w491.y w491.r w491.cap) (P33.root 2) :=
  Night6836Tree.sound w491 pick491 2 t10351 _ k491_2_6
theorem cov491_3 : PA.Covered 3 (OZ.Valid 3 w491.low w491.t w491.y w491.r w491.cap) (P33.root 3) :=
  Night6836Tree.sound w491 pick491 3 t564 _ (by decide +kernel)
theorem cov491_4 : PA.Covered 4 (OZ.Valid 4 w491.low w491.t w491.y w491.r w491.cap) (P33.root 4) :=
  Night6836Tree.sound w491 pick491 4 t565 _ (by decide +kernel)
theorem cov491_5 : PA.Covered 5 (OZ.Valid 5 w491.low w491.t w491.y w491.r w491.cap) (P33.root 5) :=
  Night6836Tree.sound w491 pick491 5 t566 _ (by decide +kernel)
theorem cov491_6 : PA.Covered 6 (OZ.Valid 6 w491.low w491.t w491.y w491.r w491.cap) (P33.root 6) :=
  Night6836Tree.sound w491 pick491 6 t567 _ (by decide +kernel)
theorem cov491_7 : PA.Covered 7 (OZ.Valid 7 w491.low w491.t w491.y w491.r w491.cap) (P33.root 7) :=
  Night6836Tree.sound w491 pick491 7 t568 _ (by decide +kernel)
theorem window491 : P33.WindowCount w491 := by
  apply P33.window_count w491 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov491_1
  · exact cov491_2
  · exact cov491_3
  · exact cov491_4
  · exact cov491_5
  · exact cov491_6
  · exact cov491_7
def w492 : P33.Window := ⟨8,40,4639,3640,191056179113178770,49256,39000,5000000,81920000000⟩
def h492_0 : Height w492 := ⟨49256,39000,by decide +kernel⟩
def h492_1 : Height w492 := ⟨54447,35000,by decide +kernel⟩
def h492_2 : Height w492 := ⟨60903,31000,by decide +kernel⟩
def h492_3 : Height w492 := ⟨69559,27000,by decide +kernel⟩
def h492_4 : Height w492 := ⟨82570,23000,by decide +kernel⟩
def pick492 (cl : ℕ) : Height w492 := if cl<13 then (if cl<2 then (h492_0) else (h492_1)) else (if cl<62 then (h492_2) else (if cl<388 then (h492_3) else (h492_4)))
private theorem k492_1_0 : check w492 pick492 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k492_1_1 : check w492 pick492 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k492_1_2 : check w492 pick492 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w492 pick492 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k492_1_0 k492_1_1
private theorem k492_1_3 : check w492 pick492 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k492_1_4 : check w492 pick492 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w492 pick492 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k492_1_2 k492_1_3
private theorem k492_1_5 : check w492 pick492 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k492_1_6 : check w492 pick492 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k492_1_7 : check w492 pick492 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w492 pick492 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k492_1_5 k492_1_6
private theorem k492_1_8 : check w492 pick492 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k492_1_9 : check w492 pick492 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k492_1_10 : check w492 pick492 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w492 pick492 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k492_1_8 k492_1_9
private theorem k492_1_11 : check w492 pick492 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w492 pick492 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k492_1_7 k492_1_10
private theorem k492_1_12 : check w492 pick492 1 t10267 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w492 pick492 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10007 k492_1_4 k492_1_11
theorem cov492_1 : PA.Covered 1 (OZ.Valid 1 w492.low w492.t w492.y w492.r w492.cap) (P33.root 1) :=
  Night6836Tree.sound w492 pick492 1 t10267 _ k492_1_12
theorem cov492_2 : PA.Covered 2 (OZ.Valid 2 w492.low w492.t w492.y w492.r w492.cap) (P33.root 2) :=
  Night6836Tree.sound w492 pick492 2 t10037 _ (by decide +kernel)
theorem cov492_3 : PA.Covered 3 (OZ.Valid 3 w492.low w492.t w492.y w492.r w492.cap) (P33.root 3) :=
  Night6836Tree.sound w492 pick492 3 t564 _ (by decide +kernel)
theorem cov492_4 : PA.Covered 4 (OZ.Valid 4 w492.low w492.t w492.y w492.r w492.cap) (P33.root 4) :=
  Night6836Tree.sound w492 pick492 4 t565 _ (by decide +kernel)
theorem cov492_5 : PA.Covered 5 (OZ.Valid 5 w492.low w492.t w492.y w492.r w492.cap) (P33.root 5) :=
  Night6836Tree.sound w492 pick492 5 t566 _ (by decide +kernel)
theorem cov492_6 : PA.Covered 6 (OZ.Valid 6 w492.low w492.t w492.y w492.r w492.cap) (P33.root 6) :=
  Night6836Tree.sound w492 pick492 6 t567 _ (by decide +kernel)
theorem cov492_7 : PA.Covered 7 (OZ.Valid 7 w492.low w492.t w492.y w492.r w492.cap) (P33.root 7) :=
  Night6836Tree.sound w492 pick492 7 t2134 _ (by decide +kernel)
theorem window492 : P33.WindowCount w492 := by
  apply P33.window_count w492 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov492_1
  · exact cov492_2
  · exact cov492_3
  · exact cov492_4
  · exact cov492_5
  · exact cov492_6
  · exact cov492_7
def w493 : P33.Window := ⟨8,40,7335,7290,245373163864928295,26489,18000,5000000,81920000000⟩
def h493_0 : Height w493 := ⟨26489,18000,by decide +kernel⟩
def h493_1 : Height w493 := ⟨31377,15000,by decide +kernel⟩
def h493_2 : Height w493 := ⟨39363,12000,by decide +kernel⟩
def pick493 (cl : ℕ) : Height w493 := if cl<13 then (h493_0) else (if cl<181 then (h493_1) else (h493_2))
private theorem k493_1_0 : check w493 pick493 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k493_1_1 : check w493 pick493 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k493_1_2 : check w493 pick493 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w493 pick493 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k493_1_0 k493_1_1
private theorem k493_1_3 : check w493 pick493 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k493_1_4 : check w493 pick493 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k493_1_5 : check w493 pick493 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w493 pick493 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k493_1_3 k493_1_4
private theorem k493_1_6 : check w493 pick493 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w493 pick493 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k493_1_2 k493_1_5
private theorem k493_1_7 : check w493 pick493 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k493_1_8 : check w493 pick493 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k493_1_9 : check w493 pick493 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w493 pick493 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k493_1_7 k493_1_8
private theorem k493_1_10 : check w493 pick493 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k493_1_11 : check w493 pick493 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k493_1_12 : check w493 pick493 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w493 pick493 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k493_1_10 k493_1_11
private theorem k493_1_13 : check w493 pick493 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w493 pick493 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k493_1_9 k493_1_12
private theorem k493_1_14 : check w493 pick493 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w493 pick493 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k493_1_6 k493_1_13
theorem cov493_1 : PA.Covered 1 (OZ.Valid 1 w493.low w493.t w493.y w493.r w493.cap) (P33.root 1) :=
  Night6836Tree.sound w493 pick493 1 t10243 _ k493_1_14
private theorem k493_2_0 : check w493 pick493 2 t10300 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k493_2_1 : check w493 pick493 2 t10312 ⟨2,7,4,16,2,52,71,84⟩ = true := by decide +kernel
private theorem k493_2_2 : check w493 pick493 2 t10382 ⟨2,7,4,16,2,52,85,111⟩ = true := by decide +kernel
private theorem k493_2_3 : check w493 pick493 2 t10383 ⟨2,7,4,16,2,52,71,111⟩ = true := glue w493 pick493 2 ⟨2,7,4,16,2,52,71,111⟩ 3 84 t10312 t10382 k493_2_1 k493_2_2
private theorem k493_2_4 : check w493 pick493 2 t10384 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w493 pick493 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10300 t10383 k493_2_0 k493_2_3
private theorem k493_2_5 : check w493 pick493 2 t10398 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k493_2_6 : check w493 pick493 2 t4155 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k493_2_7 : check w493 pick493 2 t10399 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w493 pick493 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10398 t4155 k493_2_5 k493_2_6
private theorem k493_2_8 : check w493 pick493 2 t10400 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w493 pick493 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10384 t10399 k493_2_4 k493_2_7
theorem cov493_2 : PA.Covered 2 (OZ.Valid 2 w493.low w493.t w493.y w493.r w493.cap) (P33.root 2) :=
  Night6836Tree.sound w493 pick493 2 t10400 _ k493_2_8
theorem cov493_3 : PA.Covered 3 (OZ.Valid 3 w493.low w493.t w493.y w493.r w493.cap) (P33.root 3) :=
  Night6836Tree.sound w493 pick493 3 t564 _ (by decide +kernel)
theorem cov493_4 : PA.Covered 4 (OZ.Valid 4 w493.low w493.t w493.y w493.r w493.cap) (P33.root 4) :=
  Night6836Tree.sound w493 pick493 4 t565 _ (by decide +kernel)
theorem cov493_5 : PA.Covered 5 (OZ.Valid 5 w493.low w493.t w493.y w493.r w493.cap) (P33.root 5) :=
  Night6836Tree.sound w493 pick493 5 t566 _ (by decide +kernel)
theorem cov493_6 : PA.Covered 6 (OZ.Valid 6 w493.low w493.t w493.y w493.r w493.cap) (P33.root 6) :=
  Night6836Tree.sound w493 pick493 6 t567 _ (by decide +kernel)
theorem cov493_7 : PA.Covered 7 (OZ.Valid 7 w493.low w493.t w493.y w493.r w493.cap) (P33.root 7) :=
  Night6836Tree.sound w493 pick493 7 t568 _ (by decide +kernel)
theorem window493 : P33.WindowCount w493 := by
  apply P33.window_count w493 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov493_1
  · exact cov493_2
  · exact cov493_3
  · exact cov493_4
  · exact cov493_5
  · exact cov493_6
  · exact cov493_7
def w494 : P33.Window := ⟨8,41,5740,4741,203912772441506611,43173,27000,5000000,81920000000⟩
def h494_0 : Height w494 := ⟨43173,27000,by decide +kernel⟩
def h494_1 : Height w494 := ⟨49984,23000,by decide +kernel⟩
def h494_2 : Height w494 := ⟨60398,19000,by decide +kernel⟩
def h494_3 : Height w494 := ⟨80846,15000,by decide +kernel⟩
def pick494 (cl : ℕ) : Height w494 := if cl<159 then (if cl<16 then (h494_0) else (h494_1)) else (if cl<1008 then (h494_2) else (h494_3))
private theorem k494_1_0 : check w494 pick494 1 t5078 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k494_1_1 : check w494 pick494 1 t10410 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k494_1_2 : check w494 pick494 1 t10411 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w494 pick494 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5078 t10410 k494_1_0 k494_1_1
private theorem k494_1_3 : check w494 pick494 1 t10417 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k494_1_4 : check w494 pick494 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k494_1_5 : check w494 pick494 1 t10418 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w494 pick494 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10417 t9606 k494_1_3 k494_1_4
private theorem k494_1_6 : check w494 pick494 1 t10419 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w494 pick494 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10411 t10418 k494_1_2 k494_1_5
private theorem k494_1_7 : check w494 pick494 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k494_1_8 : check w494 pick494 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k494_1_9 : check w494 pick494 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w494 pick494 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k494_1_7 k494_1_8
private theorem k494_1_10 : check w494 pick494 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k494_1_11 : check w494 pick494 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k494_1_12 : check w494 pick494 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w494 pick494 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k494_1_10 k494_1_11
private theorem k494_1_13 : check w494 pick494 1 t10228 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w494 pick494 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t10065 k494_1_9 k494_1_12
private theorem k494_1_14 : check w494 pick494 1 t10420 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w494 pick494 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10419 t10228 k494_1_6 k494_1_13
theorem cov494_1 : PA.Covered 1 (OZ.Valid 1 w494.low w494.t w494.y w494.r w494.cap) (P33.root 1) :=
  Night6836Tree.sound w494 pick494 1 t10420 _ k494_1_14
private theorem k494_2_0 : check w494 pick494 2 t10108 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k494_2_1 : check w494 pick494 2 t10421 ⟨2,7,4,16,2,52,71,98⟩ = true := by decide +kernel
private theorem k494_2_2 : check w494 pick494 2 t10422 ⟨2,7,4,16,2,52,2,98⟩ = true := glue w494 pick494 2 ⟨2,7,4,16,2,52,2,98⟩ 3 70 t10108 t10421 k494_2_0 k494_2_1
private theorem k494_2_3 : check w494 pick494 2 t10432 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k494_2_4 : check w494 pick494 2 t10433 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w494 pick494 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t10422 t10432 k494_2_2 k494_2_3
theorem cov494_2 : PA.Covered 2 (OZ.Valid 2 w494.low w494.t w494.y w494.r w494.cap) (P33.root 2) :=
  Night6836Tree.sound w494 pick494 2 t10433 _ k494_2_4
theorem cov494_3 : PA.Covered 3 (OZ.Valid 3 w494.low w494.t w494.y w494.r w494.cap) (P33.root 3) :=
  Night6836Tree.sound w494 pick494 3 t564 _ (by decide +kernel)
theorem cov494_4 : PA.Covered 4 (OZ.Valid 4 w494.low w494.t w494.y w494.r w494.cap) (P33.root 4) :=
  Night6836Tree.sound w494 pick494 4 t565 _ (by decide +kernel)
theorem cov494_5 : PA.Covered 5 (OZ.Valid 5 w494.low w494.t w494.y w494.r w494.cap) (P33.root 5) :=
  Night6836Tree.sound w494 pick494 5 t566 _ (by decide +kernel)
theorem cov494_6 : PA.Covered 6 (OZ.Valid 6 w494.low w494.t w494.y w494.r w494.cap) (P33.root 6) :=
  Night6836Tree.sound w494 pick494 6 t567 _ (by decide +kernel)
theorem cov494_7 : PA.Covered 7 (OZ.Valid 7 w494.low w494.t w494.y w494.r w494.cap) (P33.root 7) :=
  Night6836Tree.sound w494 pick494 7 t2134 _ (by decide +kernel)
theorem window494 : P33.WindowCount w494 := by
  apply P33.window_count w494 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov494_1
  · exact cov494_2
  · exact cov494_3
  · exact cov494_4
  · exact cov494_5
  · exact cov494_6
  · exact cov494_7
def w495 : P33.Window := ⟨8,41,7289,7242,245511424820592925,27821,18000,5000000,81920000000⟩
def h495_0 : Height w495 := ⟨27821,18000,by decide +kernel⟩
def h495_1 : Height w495 := ⟨32872,15000,by decide +kernel⟩
def h495_2 : Height w495 := ⟨41187,12000,by decide +kernel⟩
def pick495 (cl : ℕ) : Height w495 := if cl<14 then (h495_0) else (if cl<213 then (h495_1) else (h495_2))
private theorem k495_1_0 : check w495 pick495 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k495_1_1 : check w495 pick495 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k495_1_2 : check w495 pick495 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w495 pick495 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k495_1_0 k495_1_1
private theorem k495_1_3 : check w495 pick495 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k495_1_4 : check w495 pick495 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k495_1_5 : check w495 pick495 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w495 pick495 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k495_1_3 k495_1_4
private theorem k495_1_6 : check w495 pick495 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w495 pick495 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k495_1_2 k495_1_5
private theorem k495_1_7 : check w495 pick495 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k495_1_8 : check w495 pick495 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k495_1_9 : check w495 pick495 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w495 pick495 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k495_1_7 k495_1_8
private theorem k495_1_10 : check w495 pick495 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k495_1_11 : check w495 pick495 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k495_1_12 : check w495 pick495 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w495 pick495 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k495_1_10 k495_1_11
private theorem k495_1_13 : check w495 pick495 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w495 pick495 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k495_1_9 k495_1_12
private theorem k495_1_14 : check w495 pick495 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w495 pick495 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k495_1_6 k495_1_13
theorem cov495_1 : PA.Covered 1 (OZ.Valid 1 w495.low w495.t w495.y w495.r w495.cap) (P33.root 1) :=
  Night6836Tree.sound w495 pick495 1 t10243 _ k495_1_14
private theorem k495_2_0 : check w495 pick495 2 t10300 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k495_2_1 : check w495 pick495 2 t10312 ⟨2,7,4,16,2,52,71,84⟩ = true := by decide +kernel
private theorem k495_2_2 : check w495 pick495 2 t10382 ⟨2,7,4,16,2,52,85,111⟩ = true := by decide +kernel
private theorem k495_2_3 : check w495 pick495 2 t10383 ⟨2,7,4,16,2,52,71,111⟩ = true := glue w495 pick495 2 ⟨2,7,4,16,2,52,71,111⟩ 3 84 t10312 t10382 k495_2_1 k495_2_2
private theorem k495_2_4 : check w495 pick495 2 t10384 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w495 pick495 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10300 t10383 k495_2_0 k495_2_3
private theorem k495_2_5 : check w495 pick495 2 t10437 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k495_2_6 : check w495 pick495 2 t4155 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k495_2_7 : check w495 pick495 2 t10438 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w495 pick495 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10437 t4155 k495_2_5 k495_2_6
private theorem k495_2_8 : check w495 pick495 2 t10439 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w495 pick495 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10384 t10438 k495_2_4 k495_2_7
theorem cov495_2 : PA.Covered 2 (OZ.Valid 2 w495.low w495.t w495.y w495.r w495.cap) (P33.root 2) :=
  Night6836Tree.sound w495 pick495 2 t10439 _ k495_2_8
theorem cov495_3 : PA.Covered 3 (OZ.Valid 3 w495.low w495.t w495.y w495.r w495.cap) (P33.root 3) :=
  Night6836Tree.sound w495 pick495 3 t564 _ (by decide +kernel)
theorem cov495_4 : PA.Covered 4 (OZ.Valid 4 w495.low w495.t w495.y w495.r w495.cap) (P33.root 4) :=
  Night6836Tree.sound w495 pick495 4 t565 _ (by decide +kernel)
theorem cov495_5 : PA.Covered 5 (OZ.Valid 5 w495.low w495.t w495.y w495.r w495.cap) (P33.root 5) :=
  Night6836Tree.sound w495 pick495 5 t566 _ (by decide +kernel)
theorem cov495_6 : PA.Covered 6 (OZ.Valid 6 w495.low w495.t w495.y w495.r w495.cap) (P33.root 6) :=
  Night6836Tree.sound w495 pick495 6 t567 _ (by decide +kernel)
theorem cov495_7 : PA.Covered 7 (OZ.Valid 7 w495.low w495.t w495.y w495.r w495.cap) (P33.root 7) :=
  Night6836Tree.sound w495 pick495 7 t568 _ (by decide +kernel)
theorem window495 : P33.WindowCount w495 := by
  apply P33.window_count w495 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov495_1
  · exact cov495_2
  · exact cov495_3
  · exact cov495_4
  · exact cov495_5
  · exact cov495_6
  · exact cov495_7
def w496 : P33.Window := ⟨8,42,7241,7194,240784690374815317,29178,18000,5000000,81920000000⟩
def h496_0 : Height w496 := ⟨29178,18000,by decide +kernel⟩
def h496_1 : Height w496 := ⟨34398,15000,by decide +kernel⟩
def h496_2 : Height w496 := ⟨43055,12000,by decide +kernel⟩
def pick496 (cl : ℕ) : Height w496 := if cl<25 then (h496_0) else (if cl<260 then (h496_1) else (h496_2))
private theorem k496_1_0 : check w496 pick496 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k496_1_1 : check w496 pick496 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k496_1_2 : check w496 pick496 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w496 pick496 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k496_1_0 k496_1_1
private theorem k496_1_3 : check w496 pick496 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k496_1_4 : check w496 pick496 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k496_1_5 : check w496 pick496 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w496 pick496 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k496_1_3 k496_1_4
private theorem k496_1_6 : check w496 pick496 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w496 pick496 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k496_1_2 k496_1_5
private theorem k496_1_7 : check w496 pick496 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k496_1_8 : check w496 pick496 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k496_1_9 : check w496 pick496 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w496 pick496 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k496_1_7 k496_1_8
private theorem k496_1_10 : check w496 pick496 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k496_1_11 : check w496 pick496 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k496_1_12 : check w496 pick496 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w496 pick496 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k496_1_10 k496_1_11
private theorem k496_1_13 : check w496 pick496 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w496 pick496 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k496_1_9 k496_1_12
private theorem k496_1_14 : check w496 pick496 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w496 pick496 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k496_1_6 k496_1_13
theorem cov496_1 : PA.Covered 1 (OZ.Valid 1 w496.low w496.t w496.y w496.r w496.cap) (P33.root 1) :=
  Night6836Tree.sound w496 pick496 1 t10243 _ k496_1_14
private theorem k496_2_0 : check w496 pick496 2 t10300 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k496_2_1 : check w496 pick496 2 t10312 ⟨2,7,4,16,2,52,71,84⟩ = true := by decide +kernel
private theorem k496_2_2 : check w496 pick496 2 t10382 ⟨2,7,4,16,2,52,85,111⟩ = true := by decide +kernel
private theorem k496_2_3 : check w496 pick496 2 t10383 ⟨2,7,4,16,2,52,71,111⟩ = true := glue w496 pick496 2 ⟨2,7,4,16,2,52,71,111⟩ 3 84 t10312 t10382 k496_2_1 k496_2_2
private theorem k496_2_4 : check w496 pick496 2 t10384 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w496 pick496 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10300 t10383 k496_2_0 k496_2_3
private theorem k496_2_5 : check w496 pick496 2 t10446 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k496_2_6 : check w496 pick496 2 t4155 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k496_2_7 : check w496 pick496 2 t10447 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w496 pick496 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10446 t4155 k496_2_5 k496_2_6
private theorem k496_2_8 : check w496 pick496 2 t10448 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w496 pick496 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10384 t10447 k496_2_4 k496_2_7
theorem cov496_2 : PA.Covered 2 (OZ.Valid 2 w496.low w496.t w496.y w496.r w496.cap) (P33.root 2) :=
  Night6836Tree.sound w496 pick496 2 t10448 _ k496_2_8
theorem cov496_3 : PA.Covered 3 (OZ.Valid 3 w496.low w496.t w496.y w496.r w496.cap) (P33.root 3) :=
  Night6836Tree.sound w496 pick496 3 t564 _ (by decide +kernel)
theorem cov496_4 : PA.Covered 4 (OZ.Valid 4 w496.low w496.t w496.y w496.r w496.cap) (P33.root 4) :=
  Night6836Tree.sound w496 pick496 4 t565 _ (by decide +kernel)
theorem cov496_5 : PA.Covered 5 (OZ.Valid 5 w496.low w496.t w496.y w496.r w496.cap) (P33.root 5) :=
  Night6836Tree.sound w496 pick496 5 t566 _ (by decide +kernel)
theorem cov496_6 : PA.Covered 6 (OZ.Valid 6 w496.low w496.t w496.y w496.r w496.cap) (P33.root 6) :=
  Night6836Tree.sound w496 pick496 6 t567 _ (by decide +kernel)
theorem cov496_7 : PA.Covered 7 (OZ.Valid 7 w496.low w496.t w496.y w496.r w496.cap) (P33.root 7) :=
  Night6836Tree.sound w496 pick496 7 t568 _ (by decide +kernel)
theorem window496 : P33.WindowCount w496 := by
  apply P33.window_count w496 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov496_1
  · exact cov496_2
  · exact cov496_3
  · exact cov496_4
  · exact cov496_5
  · exact cov496_6
  · exact cov496_7
def w497 : P33.Window := ⟨8,43,5042,4043,203732567432591148,49642,35000,5000000,81920000000⟩
def h497_0 : Height w497 := ⟨49642,35000,by decide +kernel⟩
def h497_1 : Height w497 := ⟨55198,31000,by decide +kernel⟩
def h497_2 : Height w497 := ⟨62402,27000,by decide +kernel⟩
def h497_3 : Height w497 := ⟨72742,23000,by decide +kernel⟩
def h497_4 : Height w497 := ⟨90249,19000,by decide +kernel⟩
def pick497 (cl : ℕ) : Height w497 := if cl<32 then (if cl<4 then (h497_0) else (h497_1)) else (if cl<157 then (h497_2) else (if cl<989 then (h497_3) else (h497_4)))
private theorem k497_1_0 : check w497 pick497 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k497_1_1 : check w497 pick497 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k497_1_2 : check w497 pick497 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w497 pick497 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k497_1_0 k497_1_1
private theorem k497_1_3 : check w497 pick497 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k497_1_4 : check w497 pick497 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w497 pick497 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k497_1_2 k497_1_3
private theorem k497_1_5 : check w497 pick497 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k497_1_6 : check w497 pick497 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k497_1_7 : check w497 pick497 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w497 pick497 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k497_1_5 k497_1_6
private theorem k497_1_8 : check w497 pick497 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k497_1_9 : check w497 pick497 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k497_1_10 : check w497 pick497 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w497 pick497 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k497_1_8 k497_1_9
private theorem k497_1_11 : check w497 pick497 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w497 pick497 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k497_1_7 k497_1_10
private theorem k497_1_12 : check w497 pick497 1 t10267 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w497 pick497 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10007 k497_1_4 k497_1_11
theorem cov497_1 : PA.Covered 1 (OZ.Valid 1 w497.low w497.t w497.y w497.r w497.cap) (P33.root 1) :=
  Night6836Tree.sound w497 pick497 1 t10267 _ k497_1_12
private theorem k497_2_0 : check w497 pick497 2 t10269 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k497_2_1 : check w497 pick497 2 t10450 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k497_2_2 : check w497 pick497 2 t10451 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w497 pick497 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10269 t10450 k497_2_0 k497_2_1
theorem cov497_2 : PA.Covered 2 (OZ.Valid 2 w497.low w497.t w497.y w497.r w497.cap) (P33.root 2) :=
  Night6836Tree.sound w497 pick497 2 t10451 _ k497_2_2
theorem cov497_3 : PA.Covered 3 (OZ.Valid 3 w497.low w497.t w497.y w497.r w497.cap) (P33.root 3) :=
  Night6836Tree.sound w497 pick497 3 t564 _ (by decide +kernel)
theorem cov497_4 : PA.Covered 4 (OZ.Valid 4 w497.low w497.t w497.y w497.r w497.cap) (P33.root 4) :=
  Night6836Tree.sound w497 pick497 4 t565 _ (by decide +kernel)
theorem cov497_5 : PA.Covered 5 (OZ.Valid 5 w497.low w497.t w497.y w497.r w497.cap) (P33.root 5) :=
  Night6836Tree.sound w497 pick497 5 t566 _ (by decide +kernel)
theorem cov497_6 : PA.Covered 6 (OZ.Valid 6 w497.low w497.t w497.y w497.r w497.cap) (P33.root 6) :=
  Night6836Tree.sound w497 pick497 6 t567 _ (by decide +kernel)
theorem cov497_7 : PA.Covered 7 (OZ.Valid 7 w497.low w497.t w497.y w497.r w497.cap) (P33.root 7) :=
  Night6836Tree.sound w497 pick497 7 t2134 _ (by decide +kernel)
theorem window497 : P33.WindowCount w497 := by
  apply P33.window_count w497 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov497_1
  · exact cov497_2
  · exact cov497_3
  · exact cov497_4
  · exact cov497_5
  · exact cov497_6
  · exact cov497_7
def w498 : P33.Window := ⟨8,43,6167,5218,244037135011552670,38629,27000,5000000,81920000000⟩
def h498_0 : Height w498 := ⟨38629,27000,by decide +kernel⟩
def h498_1 : Height w498 := ⟨42824,24000,by decide +kernel⟩
def h498_2 : Height w498 := ⟨48222,21000,by decide +kernel⟩
def h498_3 : Height w498 := ⟨55861,18000,by decide +kernel⟩
def pick498 (cl : ℕ) : Height w498 := if cl<32 then (if cl<4 then (h498_0) else (h498_1)) else (if cl<157 then (h498_2) else (h498_3))
private theorem k498_1_0 : check w498 pick498 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k498_1_1 : check w498 pick498 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k498_1_2 : check w498 pick498 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w498 pick498 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k498_1_0 k498_1_1
private theorem k498_1_3 : check w498 pick498 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k498_1_4 : check w498 pick498 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w498 pick498 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k498_1_2 k498_1_3
private theorem k498_1_5 : check w498 pick498 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k498_1_6 : check w498 pick498 1 t6211 ⟨1,7,2,16,1,52,173,206⟩ = true := by decide +kernel
private theorem k498_1_7 : check w498 pick498 1 t6212 ⟨1,7,2,16,1,52,139,206⟩ = true := glue w498 pick498 1 ⟨1,7,2,16,1,52,139,206⟩ 3 172 t2459 t6211 k498_1_5 k498_1_6
private theorem k498_1_8 : check w498 pick498 1 t6410 ⟨1,7,2,16,1,52,207,247⟩ = true := by decide +kernel
private theorem k498_1_9 : check w498 pick498 1 t10452 ⟨1,7,2,16,1,52,248,450⟩ = true := by decide +kernel
private theorem k498_1_10 : check w498 pick498 1 t10453 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w498 pick498 1 ⟨1,7,2,16,1,52,207,450⟩ 3 247 t6410 t10452 k498_1_8 k498_1_9
private theorem k498_1_11 : check w498 pick498 1 t10454 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w498 pick498 1 ⟨1,7,2,16,1,52,139,450⟩ 3 206 t6212 t10453 k498_1_7 k498_1_10
private theorem k498_1_12 : check w498 pick498 1 t10455 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w498 pick498 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10454 k498_1_4 k498_1_11
theorem cov498_1 : PA.Covered 1 (OZ.Valid 1 w498.low w498.t w498.y w498.r w498.cap) (P33.root 1) :=
  Night6836Tree.sound w498 pick498 1 t10455 _ k498_1_12
private theorem k498_2_0 : check w498 pick498 2 t10244 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k498_2_1 : check w498 pick498 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k498_2_2 : check w498 pick498 2 t10245 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w498 pick498 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t10244 t9133 k498_2_0 k498_2_1
theorem cov498_2 : PA.Covered 2 (OZ.Valid 2 w498.low w498.t w498.y w498.r w498.cap) (P33.root 2) :=
  Night6836Tree.sound w498 pick498 2 t10245 _ k498_2_2
theorem cov498_3 : PA.Covered 3 (OZ.Valid 3 w498.low w498.t w498.y w498.r w498.cap) (P33.root 3) :=
  Night6836Tree.sound w498 pick498 3 t564 _ (by decide +kernel)
theorem cov498_4 : PA.Covered 4 (OZ.Valid 4 w498.low w498.t w498.y w498.r w498.cap) (P33.root 4) :=
  Night6836Tree.sound w498 pick498 4 t565 _ (by decide +kernel)
theorem cov498_5 : PA.Covered 5 (OZ.Valid 5 w498.low w498.t w498.y w498.r w498.cap) (P33.root 5) :=
  Night6836Tree.sound w498 pick498 5 t566 _ (by decide +kernel)
theorem cov498_6 : PA.Covered 6 (OZ.Valid 6 w498.low w498.t w498.y w498.r w498.cap) (P33.root 6) :=
  Night6836Tree.sound w498 pick498 6 t567 _ (by decide +kernel)
theorem cov498_7 : PA.Covered 7 (OZ.Valid 7 w498.low w498.t w498.y w498.r w498.cap) (P33.root 7) :=
  Night6836Tree.sound w498 pick498 7 t2134 _ (by decide +kernel)
theorem window498 : P33.WindowCount w498 := by
  apply P33.window_count w498 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov498_1
  · exact cov498_2
  · exact cov498_3
  · exact cov498_4
  · exact cov498_5
  · exact cov498_6
  · exact cov498_7
def w499 : P33.Window := ⟨8,43,7193,7046,243880356389712382,27402,21000,5000000,81920000000⟩
def h499_0 : Height w499 := ⟨27402,21000,by decide +kernel⟩
def h499_1 : Height w499 := ⟨31380,18000,by decide +kernel⟩
def h499_2 : Height w499 := ⟨36945,15000,by decide +kernel⟩
def h499_3 : Height w499 := ⟨46331,12000,by decide +kernel⟩
def pick499 (cl : ℕ) : Height w499 := if cl<27 then (if cl<2 then (h499_0) else (h499_1)) else (if cl<302 then (h499_2) else (h499_3))
private theorem k499_1_0 : check w499 pick499 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k499_1_1 : check w499 pick499 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k499_1_2 : check w499 pick499 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w499 pick499 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k499_1_0 k499_1_1
private theorem k499_1_3 : check w499 pick499 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k499_1_4 : check w499 pick499 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k499_1_5 : check w499 pick499 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w499 pick499 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k499_1_3 k499_1_4
private theorem k499_1_6 : check w499 pick499 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w499 pick499 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k499_1_2 k499_1_5
private theorem k499_1_7 : check w499 pick499 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k499_1_8 : check w499 pick499 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k499_1_9 : check w499 pick499 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w499 pick499 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k499_1_7 k499_1_8
private theorem k499_1_10 : check w499 pick499 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k499_1_11 : check w499 pick499 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k499_1_12 : check w499 pick499 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w499 pick499 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k499_1_10 k499_1_11
private theorem k499_1_13 : check w499 pick499 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w499 pick499 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k499_1_9 k499_1_12
private theorem k499_1_14 : check w499 pick499 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w499 pick499 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k499_1_6 k499_1_13
theorem cov499_1 : PA.Covered 1 (OZ.Valid 1 w499.low w499.t w499.y w499.r w499.cap) (P33.root 1) :=
  Night6836Tree.sound w499 pick499 1 t10243 _ k499_1_14
private theorem k499_2_0 : check w499 pick499 2 t10300 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k499_2_1 : check w499 pick499 2 t10312 ⟨2,7,4,16,2,52,71,84⟩ = true := by decide +kernel
private theorem k499_2_2 : check w499 pick499 2 t10382 ⟨2,7,4,16,2,52,85,111⟩ = true := by decide +kernel
private theorem k499_2_3 : check w499 pick499 2 t10383 ⟨2,7,4,16,2,52,71,111⟩ = true := glue w499 pick499 2 ⟨2,7,4,16,2,52,71,111⟩ 3 84 t10312 t10382 k499_2_1 k499_2_2
private theorem k499_2_4 : check w499 pick499 2 t10384 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w499 pick499 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10300 t10383 k499_2_0 k499_2_3
private theorem k499_2_5 : check w499 pick499 2 t10446 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k499_2_6 : check w499 pick499 2 t6001 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k499_2_7 : check w499 pick499 2 t10456 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w499 pick499 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10446 t6001 k499_2_5 k499_2_6
private theorem k499_2_8 : check w499 pick499 2 t10457 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w499 pick499 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10384 t10456 k499_2_4 k499_2_7
theorem cov499_2 : PA.Covered 2 (OZ.Valid 2 w499.low w499.t w499.y w499.r w499.cap) (P33.root 2) :=
  Night6836Tree.sound w499 pick499 2 t10457 _ k499_2_8
theorem cov499_3 : PA.Covered 3 (OZ.Valid 3 w499.low w499.t w499.y w499.r w499.cap) (P33.root 3) :=
  Night6836Tree.sound w499 pick499 3 t564 _ (by decide +kernel)
theorem cov499_4 : PA.Covered 4 (OZ.Valid 4 w499.low w499.t w499.y w499.r w499.cap) (P33.root 4) :=
  Night6836Tree.sound w499 pick499 4 t565 _ (by decide +kernel)
theorem cov499_5 : PA.Covered 5 (OZ.Valid 5 w499.low w499.t w499.y w499.r w499.cap) (P33.root 5) :=
  Night6836Tree.sound w499 pick499 5 t566 _ (by decide +kernel)
theorem cov499_6 : PA.Covered 6 (OZ.Valid 6 w499.low w499.t w499.y w499.r w499.cap) (P33.root 6) :=
  Night6836Tree.sound w499 pick499 6 t567 _ (by decide +kernel)
theorem cov499_7 : PA.Covered 7 (OZ.Valid 7 w499.low w499.t w499.y w499.r w499.cap) (P33.root 7) :=
  Night6836Tree.sound w499 pick499 7 t568 _ (by decide +kernel)
theorem window499 : P33.WindowCount w499 := by
  apply P33.window_count w499 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov499_1
  · exact cov499_2
  · exact cov499_3
  · exact cov499_4
  · exact cov499_5
  · exact cov499_6
  · exact cov499_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w500 : P33.Window := ⟨8,44,5043,4044,203754810627291551,51335,35000,5000000,81920000000⟩
def h500_0 : Height w500 := ⟨51335,35000,by decide +kernel⟩
def h500_1 : Height w500 := ⟨56979,31000,by decide +kernel⟩
def h500_2 : Height w500 := ⟨64310,27000,by decide +kernel⟩
def h500_3 : Height w500 := ⟨74851,23000,by decide +kernel⟩
def h500_4 : Height w500 := ⟨92727,19000,by decide +kernel⟩
def pick500 (cl : ℕ) : Height w500 := if cl<32 then (if cl<4 then (h500_0) else (h500_1)) else (if cl<172 then (h500_2) else (if cl<989 then (h500_3) else (h500_4)))
private theorem k500_1_0 : check w500 pick500 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k500_1_1 : check w500 pick500 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k500_1_2 : check w500 pick500 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w500 pick500 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k500_1_0 k500_1_1
private theorem k500_1_3 : check w500 pick500 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k500_1_4 : check w500 pick500 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w500 pick500 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k500_1_2 k500_1_3
private theorem k500_1_5 : check w500 pick500 1 t10460 ⟨1,7,2,16,1,52,139,179⟩ = true := by decide +kernel
private theorem k500_1_6 : check w500 pick500 1 t10461 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k500_1_7 : check w500 pick500 1 t10462 ⟨1,7,2,16,1,52,139,206⟩ = true := glue w500 pick500 1 ⟨1,7,2,16,1,52,139,206⟩ 3 179 t10460 t10461 k500_1_5 k500_1_6
private theorem k500_1_8 : check w500 pick500 1 t2385 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k500_1_9 : check w500 pick500 1 t10463 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k500_1_10 : check w500 pick500 1 t10464 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w500 pick500 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t2385 t10463 k500_1_8 k500_1_9
private theorem k500_1_11 : check w500 pick500 1 t10465 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w500 pick500 1 ⟨1,7,2,16,1,52,139,450⟩ 3 206 t10462 t10464 k500_1_7 k500_1_10
private theorem k500_1_12 : check w500 pick500 1 t10466 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w500 pick500 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10465 k500_1_4 k500_1_11
theorem cov500_1 : PA.Covered 1 (OZ.Valid 1 w500.low w500.t w500.y w500.r w500.cap) (P33.root 1) :=
  Night6836Tree.sound w500 pick500 1 t10466 _ k500_1_12
private theorem k500_2_0 : check w500 pick500 2 t10468 ⟨2,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k500_2_1 : check w500 pick500 2 t10470 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k500_2_2 : check w500 pick500 2 t10471 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w500 pick500 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t10468 t10470 k500_2_0 k500_2_1
theorem cov500_2 : PA.Covered 2 (OZ.Valid 2 w500.low w500.t w500.y w500.r w500.cap) (P33.root 2) :=
  Night6836Tree.sound w500 pick500 2 t10471 _ k500_2_2
theorem cov500_3 : PA.Covered 3 (OZ.Valid 3 w500.low w500.t w500.y w500.r w500.cap) (P33.root 3) :=
  Night6836Tree.sound w500 pick500 3 t564 _ (by decide +kernel)
theorem cov500_4 : PA.Covered 4 (OZ.Valid 4 w500.low w500.t w500.y w500.r w500.cap) (P33.root 4) :=
  Night6836Tree.sound w500 pick500 4 t565 _ (by decide +kernel)
theorem cov500_5 : PA.Covered 5 (OZ.Valid 5 w500.low w500.t w500.y w500.r w500.cap) (P33.root 5) :=
  Night6836Tree.sound w500 pick500 5 t566 _ (by decide +kernel)
theorem cov500_6 : PA.Covered 6 (OZ.Valid 6 w500.low w500.t w500.y w500.r w500.cap) (P33.root 6) :=
  Night6836Tree.sound w500 pick500 6 t567 _ (by decide +kernel)
theorem cov500_7 : PA.Covered 7 (OZ.Valid 7 w500.low w500.t w500.y w500.r w500.cap) (P33.root 7) :=
  Night6836Tree.sound w500 pick500 7 t2134 _ (by decide +kernel)
theorem window500 : P33.WindowCount w500 := by
  apply P33.window_count w500 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov500_1
  · exact cov500_2
  · exact cov500_3
  · exact cov500_4
  · exact cov500_5
  · exact cov500_6
  · exact cov500_7
def w501 : P33.Window := ⟨8,44,7144,7096,246258844773551776,27998,21000,5000000,81920000000⟩
def h501_0 : Height w501 := ⟨27998,21000,by decide +kernel⟩
def h501_1 : Height w501 := ⟨31990,18000,by decide +kernel⟩
def h501_2 : Height w501 := ⟨37569,15000,by decide +kernel⟩
def h501_3 : Height w501 := ⟨46959,12000,by decide +kernel⟩
def pick501 (cl : ℕ) : Height w501 := if cl<27 then (if cl<2 then (h501_0) else (h501_1)) else (if cl<302 then (h501_2) else (h501_3))
private theorem k501_1_0 : check w501 pick501 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k501_1_1 : check w501 pick501 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k501_1_2 : check w501 pick501 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w501 pick501 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k501_1_0 k501_1_1
private theorem k501_1_3 : check w501 pick501 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k501_1_4 : check w501 pick501 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k501_1_5 : check w501 pick501 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w501 pick501 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k501_1_3 k501_1_4
private theorem k501_1_6 : check w501 pick501 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w501 pick501 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k501_1_2 k501_1_5
private theorem k501_1_7 : check w501 pick501 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k501_1_8 : check w501 pick501 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k501_1_9 : check w501 pick501 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w501 pick501 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k501_1_7 k501_1_8
private theorem k501_1_10 : check w501 pick501 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k501_1_11 : check w501 pick501 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k501_1_12 : check w501 pick501 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w501 pick501 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k501_1_10 k501_1_11
private theorem k501_1_13 : check w501 pick501 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w501 pick501 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k501_1_9 k501_1_12
private theorem k501_1_14 : check w501 pick501 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w501 pick501 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k501_1_6 k501_1_13
theorem cov501_1 : PA.Covered 1 (OZ.Valid 1 w501.low w501.t w501.y w501.r w501.cap) (P33.root 1) :=
  Night6836Tree.sound w501 pick501 1 t10243 _ k501_1_14
private theorem k501_2_0 : check w501 pick501 2 t10489 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k501_2_1 : check w501 pick501 2 t10312 ⟨2,7,4,16,2,52,71,84⟩ = true := by decide +kernel
private theorem k501_2_2 : check w501 pick501 2 t10382 ⟨2,7,4,16,2,52,85,111⟩ = true := by decide +kernel
private theorem k501_2_3 : check w501 pick501 2 t10383 ⟨2,7,4,16,2,52,71,111⟩ = true := glue w501 pick501 2 ⟨2,7,4,16,2,52,71,111⟩ 3 84 t10312 t10382 k501_2_1 k501_2_2
private theorem k501_2_4 : check w501 pick501 2 t10490 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w501 pick501 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10489 t10383 k501_2_0 k501_2_3
private theorem k501_2_5 : check w501 pick501 2 t10446 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k501_2_6 : check w501 pick501 2 t10492 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k501_2_7 : check w501 pick501 2 t10493 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w501 pick501 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10446 t10492 k501_2_5 k501_2_6
private theorem k501_2_8 : check w501 pick501 2 t10494 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w501 pick501 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10490 t10493 k501_2_4 k501_2_7
theorem cov501_2 : PA.Covered 2 (OZ.Valid 2 w501.low w501.t w501.y w501.r w501.cap) (P33.root 2) :=
  Night6836Tree.sound w501 pick501 2 t10494 _ k501_2_8
theorem cov501_3 : PA.Covered 3 (OZ.Valid 3 w501.low w501.t w501.y w501.r w501.cap) (P33.root 3) :=
  Night6836Tree.sound w501 pick501 3 t564 _ (by decide +kernel)
theorem cov501_4 : PA.Covered 4 (OZ.Valid 4 w501.low w501.t w501.y w501.r w501.cap) (P33.root 4) :=
  Night6836Tree.sound w501 pick501 4 t565 _ (by decide +kernel)
theorem cov501_5 : PA.Covered 5 (OZ.Valid 5 w501.low w501.t w501.y w501.r w501.cap) (P33.root 5) :=
  Night6836Tree.sound w501 pick501 5 t566 _ (by decide +kernel)
theorem cov501_6 : PA.Covered 6 (OZ.Valid 6 w501.low w501.t w501.y w501.r w501.cap) (P33.root 6) :=
  Night6836Tree.sound w501 pick501 6 t567 _ (by decide +kernel)
theorem cov501_7 : PA.Covered 7 (OZ.Valid 7 w501.low w501.t w501.y w501.r w501.cap) (P33.root 7) :=
  Night6836Tree.sound w501 pick501 7 t568 _ (by decide +kernel)
theorem window501 : P33.WindowCount w501 := by
  apply P33.window_count w501 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov501_1
  · exact cov501_2
  · exact cov501_3
  · exact cov501_4
  · exact cov501_5
  · exact cov501_6
  · exact cov501_7
def w502 : P33.Window := ⟨8,45,5044,4045,203620696659023818,53027,35000,5000000,81920000000⟩
def h502_0 : Height w502 := ⟨53027,35000,by decide +kernel⟩
def h502_1 : Height w502 := ⟨58758,31000,by decide +kernel⟩
def h502_2 : Height w502 := ⟨66216,27000,by decide +kernel⟩
def h502_3 : Height w502 := ⟨76958,23000,by decide +kernel⟩
def h502_4 : Height w502 := ⟨95202,19000,by decide +kernel⟩
def pick502 (cl : ℕ) : Height w502 := if cl<32 then (if cl<4 then (h502_0) else (h502_1)) else (if cl<192 then (h502_2) else (if cl<989 then (h502_3) else (h502_4)))
private theorem k502_1_0 : check w502 pick502 1 t9154 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k502_1_1 : check w502 pick502 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k502_1_2 : check w502 pick502 1 t10495 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w502 pick502 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t9154 t10040 k502_1_0 k502_1_1
private theorem k502_1_3 : check w502 pick502 1 t10500 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k502_1_4 : check w502 pick502 1 t10501 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w502 pick502 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10495 t10500 k502_1_2 k502_1_3
private theorem k502_1_5 : check w502 pick502 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k502_1_6 : check w502 pick502 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k502_1_7 : check w502 pick502 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w502 pick502 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k502_1_5 k502_1_6
private theorem k502_1_8 : check w502 pick502 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k502_1_9 : check w502 pick502 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k502_1_10 : check w502 pick502 1 t10502 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w502 pick502 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10064 k502_1_8 k502_1_9
private theorem k502_1_11 : check w502 pick502 1 t10503 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w502 pick502 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t10502 k502_1_7 k502_1_10
private theorem k502_1_12 : check w502 pick502 1 t10504 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w502 pick502 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10501 t10503 k502_1_4 k502_1_11
theorem cov502_1 : PA.Covered 1 (OZ.Valid 1 w502.low w502.t w502.y w502.r w502.cap) (P33.root 1) :=
  Night6836Tree.sound w502 pick502 1 t10504 _ k502_1_12
private theorem k502_2_0 : check w502 pick502 2 t10108 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k502_2_1 : check w502 pick502 2 t10149 ⟨2,7,4,16,2,52,71,91⟩ = true := by decide +kernel
private theorem k502_2_2 : check w502 pick502 2 t10150 ⟨2,7,4,16,2,52,2,91⟩ = true := glue w502 pick502 2 ⟨2,7,4,16,2,52,2,91⟩ 3 70 t10108 t10149 k502_2_0 k502_2_1
private theorem k502_2_3 : check w502 pick502 2 t10507 ⟨2,7,4,16,2,52,92,450⟩ = true := by decide +kernel
private theorem k502_2_4 : check w502 pick502 2 t10508 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w502 pick502 2 ⟨2,7,4,16,0,52,0,450⟩ 3 91 t10150 t10507 k502_2_2 k502_2_3
theorem cov502_2 : PA.Covered 2 (OZ.Valid 2 w502.low w502.t w502.y w502.r w502.cap) (P33.root 2) :=
  Night6836Tree.sound w502 pick502 2 t10508 _ k502_2_4
theorem cov502_3 : PA.Covered 3 (OZ.Valid 3 w502.low w502.t w502.y w502.r w502.cap) (P33.root 3) :=
  Night6836Tree.sound w502 pick502 3 t564 _ (by decide +kernel)
theorem cov502_4 : PA.Covered 4 (OZ.Valid 4 w502.low w502.t w502.y w502.r w502.cap) (P33.root 4) :=
  Night6836Tree.sound w502 pick502 4 t565 _ (by decide +kernel)
theorem cov502_5 : PA.Covered 5 (OZ.Valid 5 w502.low w502.t w502.y w502.r w502.cap) (P33.root 5) :=
  Night6836Tree.sound w502 pick502 5 t566 _ (by decide +kernel)
theorem cov502_6 : PA.Covered 6 (OZ.Valid 6 w502.low w502.t w502.y w502.r w502.cap) (P33.root 6) :=
  Night6836Tree.sound w502 pick502 6 t567 _ (by decide +kernel)
theorem cov502_7 : PA.Covered 7 (OZ.Valid 7 w502.low w502.t w502.y w502.r w502.cap) (P33.root 7) :=
  Night6836Tree.sound w502 pick502 7 t2134 _ (by decide +kernel)
theorem window502 : P33.WindowCount w502 := by
  apply P33.window_count w502 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov502_1
  · exact cov502_2
  · exact cov502_3
  · exact cov502_4
  · exact cov502_5
  · exact cov502_6
  · exact cov502_7
def w503 : P33.Window := ⟨8,45,7095,7046,246340614979200022,29343,21000,5000000,81920000000⟩
def h503_0 : Height w503 := ⟨29343,21000,by decide +kernel⟩
def h503_1 : Height w503 := ⟨33447,18000,by decide +kernel⟩
def h503_2 : Height w503 := ⟨39218,15000,by decide +kernel⟩
def h503_3 : Height w503 := ⟨49002,12000,by decide +kernel⟩
def pick503 (cl : ℕ) : Height w503 := if cl<32 then (if cl<3 then (h503_0) else (h503_1)) else (if cl<394 then (h503_2) else (h503_3))
private theorem k503_1_0 : check w503 pick503 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k503_1_1 : check w503 pick503 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k503_1_2 : check w503 pick503 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w503 pick503 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k503_1_0 k503_1_1
private theorem k503_1_3 : check w503 pick503 1 t10511 ⟨1,7,2,16,1,20,77,138⟩ = true := by decide +kernel
private theorem k503_1_4 : check w503 pick503 1 t10514 ⟨1,7,2,16,21,52,77,138⟩ = true := by decide +kernel
private theorem k503_1_5 : check w503 pick503 1 t10515 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w503 pick503 1 ⟨1,7,2,16,1,52,77,138⟩ 2 20 t10511 t10514 k503_1_3 k503_1_4
private theorem k503_1_6 : check w503 pick503 1 t10516 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w503 pick503 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t10234 t10515 k503_1_2 k503_1_5
private theorem k503_1_7 : check w503 pick503 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k503_1_8 : check w503 pick503 1 t3371 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k503_1_9 : check w503 pick503 1 t3372 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w503 pick503 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t3199 t3371 k503_1_7 k503_1_8
private theorem k503_1_10 : check w503 pick503 1 t10519 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k503_1_11 : check w503 pick503 1 t10521 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k503_1_12 : check w503 pick503 1 t10522 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w503 pick503 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t10519 t10521 k503_1_10 k503_1_11
private theorem k503_1_13 : check w503 pick503 1 t10523 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w503 pick503 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t3372 t10522 k503_1_9 k503_1_12
private theorem k503_1_14 : check w503 pick503 1 t10524 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w503 pick503 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10516 t10523 k503_1_6 k503_1_13
theorem cov503_1 : PA.Covered 1 (OZ.Valid 1 w503.low w503.t w503.y w503.r w503.cap) (P33.root 1) :=
  Night6836Tree.sound w503 pick503 1 t10524 _ k503_1_14
private theorem k503_2_0 : check w503 pick503 2 t10489 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k503_2_1 : check w503 pick503 2 t10312 ⟨2,7,4,16,2,52,71,84⟩ = true := by decide +kernel
private theorem k503_2_2 : check w503 pick503 2 t10382 ⟨2,7,4,16,2,52,85,111⟩ = true := by decide +kernel
private theorem k503_2_3 : check w503 pick503 2 t10383 ⟨2,7,4,16,2,52,71,111⟩ = true := glue w503 pick503 2 ⟨2,7,4,16,2,52,71,111⟩ 3 84 t10312 t10382 k503_2_1 k503_2_2
private theorem k503_2_4 : check w503 pick503 2 t10490 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w503 pick503 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10489 t10383 k503_2_0 k503_2_3
private theorem k503_2_5 : check w503 pick503 2 t10532 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k503_2_6 : check w503 pick503 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k503_2_7 : check w503 pick503 2 t10533 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w503 pick503 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10532 t9411 k503_2_5 k503_2_6
private theorem k503_2_8 : check w503 pick503 2 t10534 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w503 pick503 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10490 t10533 k503_2_4 k503_2_7
theorem cov503_2 : PA.Covered 2 (OZ.Valid 2 w503.low w503.t w503.y w503.r w503.cap) (P33.root 2) :=
  Night6836Tree.sound w503 pick503 2 t10534 _ k503_2_8
theorem cov503_3 : PA.Covered 3 (OZ.Valid 3 w503.low w503.t w503.y w503.r w503.cap) (P33.root 3) :=
  Night6836Tree.sound w503 pick503 3 t564 _ (by decide +kernel)
theorem cov503_4 : PA.Covered 4 (OZ.Valid 4 w503.low w503.t w503.y w503.r w503.cap) (P33.root 4) :=
  Night6836Tree.sound w503 pick503 4 t565 _ (by decide +kernel)
theorem cov503_5 : PA.Covered 5 (OZ.Valid 5 w503.low w503.t w503.y w503.r w503.cap) (P33.root 5) :=
  Night6836Tree.sound w503 pick503 5 t566 _ (by decide +kernel)
theorem cov503_6 : PA.Covered 6 (OZ.Valid 6 w503.low w503.t w503.y w503.r w503.cap) (P33.root 6) :=
  Night6836Tree.sound w503 pick503 6 t567 _ (by decide +kernel)
theorem cov503_7 : PA.Covered 7 (OZ.Valid 7 w503.low w503.t w503.y w503.r w503.cap) (P33.root 7) :=
  Night6836Tree.sound w503 pick503 7 t568 _ (by decide +kernel)
theorem window503 : P33.WindowCount w503 := by
  apply P33.window_count w503 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov503_1
  · exact cov503_2
  · exact cov503_3
  · exact cov503_4
  · exact cov503_5
  · exact cov503_6
  · exact cov503_7
def w504 : P33.Window := ⟨8,46,6182,5233,244679856335724996,42407,27000,5000000,81920000000⟩
def h504_0 : Height w504 := ⟨42407,27000,by decide +kernel⟩
def h504_1 : Height w504 := ⟨46782,24000,by decide +kernel⟩
def h504_2 : Height w504 := ⟨52440,21000,by decide +kernel⟩
def h504_3 : Height w504 := ⟨60480,18000,by decide +kernel⟩
def h504_4 : Height w504 := ⟨73764,15000,by decide +kernel⟩
def pick504 (cl : ℕ) : Height w504 := if cl<32 then (if cl<5 then (h504_0) else (h504_1)) else (if cl<192 then (h504_2) else (if cl<989 then (h504_3) else (h504_4)))
private theorem k504_1_0 : check w504 pick504 1 t10535 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k504_1_1 : check w504 pick504 1 t10552 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k504_1_2 : check w504 pick504 1 t10553 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w504 pick504 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10535 t10552 k504_1_0 k504_1_1
private theorem k504_1_3 : check w504 pick504 1 t10566 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k504_1_4 : check w504 pick504 1 t10572 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k504_1_5 : check w504 pick504 1 t10573 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w504 pick504 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t10566 t10572 k504_1_3 k504_1_4
private theorem k504_1_6 : check w504 pick504 1 t10574 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w504 pick504 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t10553 t10573 k504_1_2 k504_1_5
private theorem k504_1_7 : check w504 pick504 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k504_1_8 : check w504 pick504 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k504_1_9 : check w504 pick504 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w504 pick504 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k504_1_7 k504_1_8
private theorem k504_1_10 : check w504 pick504 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k504_1_11 : check w504 pick504 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k504_1_12 : check w504 pick504 1 t10502 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w504 pick504 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10064 k504_1_10 k504_1_11
private theorem k504_1_13 : check w504 pick504 1 t10503 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w504 pick504 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t10502 k504_1_9 k504_1_12
private theorem k504_1_14 : check w504 pick504 1 t10575 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w504 pick504 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10574 t10503 k504_1_6 k504_1_13
theorem cov504_1 : PA.Covered 1 (OZ.Valid 1 w504.low w504.t w504.y w504.r w504.cap) (P33.root 1) :=
  Night6836Tree.sound w504 pick504 1 t10575 _ k504_1_14
private theorem k504_2_0 : check w504 pick504 2 t10189 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k504_2_1 : check w504 pick504 2 t10578 ⟨2,7,4,16,2,52,85,450⟩ = true := by decide +kernel
private theorem k504_2_2 : check w504 pick504 2 t10579 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w504 pick504 2 ⟨2,7,4,16,0,52,0,450⟩ 3 84 t10189 t10578 k504_2_0 k504_2_1
theorem cov504_2 : PA.Covered 2 (OZ.Valid 2 w504.low w504.t w504.y w504.r w504.cap) (P33.root 2) :=
  Night6836Tree.sound w504 pick504 2 t10579 _ k504_2_2
theorem cov504_3 : PA.Covered 3 (OZ.Valid 3 w504.low w504.t w504.y w504.r w504.cap) (P33.root 3) :=
  Night6836Tree.sound w504 pick504 3 t564 _ (by decide +kernel)
theorem cov504_4 : PA.Covered 4 (OZ.Valid 4 w504.low w504.t w504.y w504.r w504.cap) (P33.root 4) :=
  Night6836Tree.sound w504 pick504 4 t565 _ (by decide +kernel)
theorem cov504_5 : PA.Covered 5 (OZ.Valid 5 w504.low w504.t w504.y w504.r w504.cap) (P33.root 5) :=
  Night6836Tree.sound w504 pick504 5 t566 _ (by decide +kernel)
theorem cov504_6 : PA.Covered 6 (OZ.Valid 6 w504.low w504.t w504.y w504.r w504.cap) (P33.root 6) :=
  Night6836Tree.sound w504 pick504 6 t567 _ (by decide +kernel)
theorem cov504_7 : PA.Covered 7 (OZ.Valid 7 w504.low w504.t w504.y w504.r w504.cap) (P33.root 7) :=
  Night6836Tree.sound w504 pick504 7 t2134 _ (by decide +kernel)
theorem window504 : P33.WindowCount w504 := by
  apply P33.window_count w504 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov504_1
  · exact cov504_2
  · exact cov504_3
  · exact cov504_4
  · exact cov504_5
  · exact cov504_6
  · exact cov504_7
def w505 : P33.Window := ⟨8,47,6985,6926,246476931371865210,32279,21000,5000000,81920000000⟩
def h505_0 : Height w505 := ⟨32279,21000,by decide +kernel⟩
def h505_1 : Height w505 := ⟨36645,18000,by decide +kernel⟩
def h505_2 : Height w505 := ⟨42863,15000,by decide +kernel⟩
def h505_3 : Height w505 := ⟨53579,12000,by decide +kernel⟩
def pick505 (cl : ℕ) : Height w505 := if cl<44 then (if cl<5 then (h505_0) else (h505_1)) else (if cl<765 then (h505_2) else (h505_3))
private theorem k505_1_0 : check w505 pick505 1 t10580 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k505_1_1 : check w505 pick505 1 t10588 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k505_1_2 : check w505 pick505 1 t10589 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w505 pick505 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10580 t10588 k505_1_0 k505_1_1
private theorem k505_1_3 : check w505 pick505 1 t10594 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k505_1_4 : check w505 pick505 1 t9760 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k505_1_5 : check w505 pick505 1 t10595 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w505 pick505 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10594 t9760 k505_1_3 k505_1_4
private theorem k505_1_6 : check w505 pick505 1 t10596 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w505 pick505 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10589 t10595 k505_1_2 k505_1_5
private theorem k505_1_7 : check w505 pick505 1 t10607 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k505_1_8 : check w505 pick505 1 t10613 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k505_1_9 : check w505 pick505 1 t10614 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w505 pick505 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t10607 t10613 k505_1_7 k505_1_8
private theorem k505_1_10 : check w505 pick505 1 t6332 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k505_1_11 : check w505 pick505 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k505_1_12 : check w505 pick505 1 t10617 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w505 pick505 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t6332 t10616 k505_1_10 k505_1_11
private theorem k505_1_13 : check w505 pick505 1 t10618 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w505 pick505 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t10614 t10617 k505_1_9 k505_1_12
private theorem k505_1_14 : check w505 pick505 1 t10619 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w505 pick505 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10596 t10618 k505_1_6 k505_1_13
theorem cov505_1 : PA.Covered 1 (OZ.Valid 1 w505.low w505.t w505.y w505.r w505.cap) (P33.root 1) :=
  Night6836Tree.sound w505 pick505 1 t10619 _ k505_1_14
private theorem k505_2_0 : check w505 pick505 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k505_2_1 : check w505 pick505 2 t10645 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k505_2_2 : check w505 pick505 2 t10646 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w505 pick505 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10645 k505_2_0 k505_2_1
private theorem k505_2_3 : check w505 pick505 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k505_2_4 : check w505 pick505 2 t10652 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k505_2_5 : check w505 pick505 2 t10653 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w505 pick505 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t10652 k505_2_3 k505_2_4
private theorem k505_2_6 : check w505 pick505 2 t10654 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w505 pick505 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10646 t10653 k505_2_2 k505_2_5
theorem cov505_2 : PA.Covered 2 (OZ.Valid 2 w505.low w505.t w505.y w505.r w505.cap) (P33.root 2) :=
  Night6836Tree.sound w505 pick505 2 t10654 _ k505_2_6
theorem cov505_3 : PA.Covered 3 (OZ.Valid 3 w505.low w505.t w505.y w505.r w505.cap) (P33.root 3) :=
  Night6836Tree.sound w505 pick505 3 t564 _ (by decide +kernel)
theorem cov505_4 : PA.Covered 4 (OZ.Valid 4 w505.low w505.t w505.y w505.r w505.cap) (P33.root 4) :=
  Night6836Tree.sound w505 pick505 4 t565 _ (by decide +kernel)
theorem cov505_5 : PA.Covered 5 (OZ.Valid 5 w505.low w505.t w505.y w505.r w505.cap) (P33.root 5) :=
  Night6836Tree.sound w505 pick505 5 t566 _ (by decide +kernel)
theorem cov505_6 : PA.Covered 6 (OZ.Valid 6 w505.low w505.t w505.y w505.r w505.cap) (P33.root 6) :=
  Night6836Tree.sound w505 pick505 6 t567 _ (by decide +kernel)
theorem cov505_7 : PA.Covered 7 (OZ.Valid 7 w505.low w505.t w505.y w505.r w505.cap) (P33.root 7) :=
  Night6836Tree.sound w505 pick505 7 t568 _ (by decide +kernel)
theorem window505 : P33.WindowCount w505 := by
  apply P33.window_count w505 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov505_1
  · exact cov505_2
  · exact cov505_3
  · exact cov505_4
  · exact cov505_5
  · exact cov505_6
  · exact cov505_7
def w506 : P33.Window := ⟨8,48,6297,5348,236281377059141611,43328,27000,5000000,81920000000⟩
def h506_0 : Height w506 := ⟨43328,27000,by decide +kernel⟩
def h506_1 : Height w506 := ⟨47659,24000,by decide +kernel⟩
def h506_2 : Height w506 := ⟨53237,21000,by decide +kernel⟩
def h506_3 : Height w506 := ⟨61118,18000,by decide +kernel⟩
def h506_4 : Height w506 := ⟨74005,15000,by decide +kernel⟩
def pick506 (cl : ℕ) : Height w506 := if cl<27 then (if cl<5 then (h506_0) else (h506_1)) else (if cl<166 then (h506_2) else (if cl<961 then (h506_3) else (h506_4)))
private theorem k506_1_0 : check w506 pick506 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k506_1_1 : check w506 pick506 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k506_1_2 : check w506 pick506 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w506 pick506 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k506_1_0 k506_1_1
private theorem k506_1_3 : check w506 pick506 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k506_1_4 : check w506 pick506 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k506_1_5 : check w506 pick506 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w506 pick506 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k506_1_3 k506_1_4
private theorem k506_1_6 : check w506 pick506 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w506 pick506 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k506_1_2 k506_1_5
private theorem k506_1_7 : check w506 pick506 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k506_1_8 : check w506 pick506 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k506_1_9 : check w506 pick506 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w506 pick506 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k506_1_7 k506_1_8
private theorem k506_1_10 : check w506 pick506 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k506_1_11 : check w506 pick506 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k506_1_12 : check w506 pick506 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w506 pick506 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k506_1_10 k506_1_11
private theorem k506_1_13 : check w506 pick506 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w506 pick506 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k506_1_9 k506_1_12
private theorem k506_1_14 : check w506 pick506 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w506 pick506 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k506_1_6 k506_1_13
theorem cov506_1 : PA.Covered 1 (OZ.Valid 1 w506.low w506.t w506.y w506.r w506.cap) (P33.root 1) :=
  Night6836Tree.sound w506 pick506 1 t10243 _ k506_1_14
private theorem k506_2_0 : check w506 pick506 2 t10300 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k506_2_1 : check w506 pick506 2 t10312 ⟨2,7,4,16,2,52,71,84⟩ = true := by decide +kernel
private theorem k506_2_2 : check w506 pick506 2 t10382 ⟨2,7,4,16,2,52,85,111⟩ = true := by decide +kernel
private theorem k506_2_3 : check w506 pick506 2 t10383 ⟨2,7,4,16,2,52,71,111⟩ = true := glue w506 pick506 2 ⟨2,7,4,16,2,52,71,111⟩ 3 84 t10312 t10382 k506_2_1 k506_2_2
private theorem k506_2_4 : check w506 pick506 2 t10384 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w506 pick506 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10300 t10383 k506_2_0 k506_2_3
private theorem k506_2_5 : check w506 pick506 2 t10446 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k506_2_6 : check w506 pick506 2 t4902 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k506_2_7 : check w506 pick506 2 t10655 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w506 pick506 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10446 t4902 k506_2_5 k506_2_6
private theorem k506_2_8 : check w506 pick506 2 t10656 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w506 pick506 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10384 t10655 k506_2_4 k506_2_7
theorem cov506_2 : PA.Covered 2 (OZ.Valid 2 w506.low w506.t w506.y w506.r w506.cap) (P33.root 2) :=
  Night6836Tree.sound w506 pick506 2 t10656 _ k506_2_8
theorem cov506_3 : PA.Covered 3 (OZ.Valid 3 w506.low w506.t w506.y w506.r w506.cap) (P33.root 3) :=
  Night6836Tree.sound w506 pick506 3 t564 _ (by decide +kernel)
theorem cov506_4 : PA.Covered 4 (OZ.Valid 4 w506.low w506.t w506.y w506.r w506.cap) (P33.root 4) :=
  Night6836Tree.sound w506 pick506 4 t565 _ (by decide +kernel)
theorem cov506_5 : PA.Covered 5 (OZ.Valid 5 w506.low w506.t w506.y w506.r w506.cap) (P33.root 5) :=
  Night6836Tree.sound w506 pick506 5 t566 _ (by decide +kernel)
theorem cov506_6 : PA.Covered 6 (OZ.Valid 6 w506.low w506.t w506.y w506.r w506.cap) (P33.root 6) :=
  Night6836Tree.sound w506 pick506 6 t567 _ (by decide +kernel)
theorem cov506_7 : PA.Covered 7 (OZ.Valid 7 w506.low w506.t w506.y w506.r w506.cap) (P33.root 7) :=
  Night6836Tree.sound w506 pick506 7 t2134 _ (by decide +kernel)
theorem window506 : P33.WindowCount w506 := by
  apply P33.window_count w506 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov506_1
  · exact cov506_2
  · exact cov506_3
  · exact cov506_4
  · exact cov506_5
  · exact cov506_6
  · exact cov506_7
def w507 : P33.Window := ⟨8,48,6925,6734,246322706508849223,35008,21000,5000000,81920000000⟩
def h507_0 : Height w507 := ⟨35008,21000,by decide +kernel⟩
def h507_1 : Height w507 := ⟨39685,18000,by decide +kernel⟩
def h507_2 : Height w507 := ⟨46449,15000,by decide +kernel⟩
def h507_3 : Height w507 := ⟨58360,12000,by decide +kernel⟩
def pick507 (cl : ℕ) : Height w507 := if cl<75 then (if cl<10 then (h507_0) else (h507_1)) else (if cl<925 then (h507_2) else (h507_3))
private theorem k507_1_0 : check w507 pick507 1 t10659 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k507_1_1 : check w507 pick507 1 t10661 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k507_1_2 : check w507 pick507 1 t10662 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w507 pick507 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10659 t10661 k507_1_0 k507_1_1
private theorem k507_1_3 : check w507 pick507 1 t10594 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k507_1_4 : check w507 pick507 1 t10664 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k507_1_5 : check w507 pick507 1 t10665 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w507 pick507 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10594 t10664 k507_1_3 k507_1_4
private theorem k507_1_6 : check w507 pick507 1 t10666 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w507 pick507 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10662 t10665 k507_1_2 k507_1_5
private theorem k507_1_7 : check w507 pick507 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k507_1_8 : check w507 pick507 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k507_1_9 : check w507 pick507 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w507 pick507 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k507_1_7 k507_1_8
private theorem k507_1_10 : check w507 pick507 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k507_1_11 : check w507 pick507 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k507_1_12 : check w507 pick507 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w507 pick507 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k507_1_10 k507_1_11
private theorem k507_1_13 : check w507 pick507 1 t10668 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w507 pick507 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t10667 k507_1_9 k507_1_12
private theorem k507_1_14 : check w507 pick507 1 t10669 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w507 pick507 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10666 t10668 k507_1_6 k507_1_13
theorem cov507_1 : PA.Covered 1 (OZ.Valid 1 w507.low w507.t w507.y w507.r w507.cap) (P33.root 1) :=
  Night6836Tree.sound w507 pick507 1 t10669 _ k507_1_14
private theorem k507_2_0 : check w507 pick507 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k507_2_1 : check w507 pick507 2 t10645 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k507_2_2 : check w507 pick507 2 t10646 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w507 pick507 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10645 k507_2_0 k507_2_1
private theorem k507_2_3 : check w507 pick507 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k507_2_4 : check w507 pick507 2 t10652 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k507_2_5 : check w507 pick507 2 t10653 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w507 pick507 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t10652 k507_2_3 k507_2_4
private theorem k507_2_6 : check w507 pick507 2 t10654 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w507 pick507 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10646 t10653 k507_2_2 k507_2_5
theorem cov507_2 : PA.Covered 2 (OZ.Valid 2 w507.low w507.t w507.y w507.r w507.cap) (P33.root 2) :=
  Night6836Tree.sound w507 pick507 2 t10654 _ k507_2_6
theorem cov507_3 : PA.Covered 3 (OZ.Valid 3 w507.low w507.t w507.y w507.r w507.cap) (P33.root 3) :=
  Night6836Tree.sound w507 pick507 3 t564 _ (by decide +kernel)
theorem cov507_4 : PA.Covered 4 (OZ.Valid 4 w507.low w507.t w507.y w507.r w507.cap) (P33.root 4) :=
  Night6836Tree.sound w507 pick507 4 t565 _ (by decide +kernel)
theorem cov507_5 : PA.Covered 5 (OZ.Valid 5 w507.low w507.t w507.y w507.r w507.cap) (P33.root 5) :=
  Night6836Tree.sound w507 pick507 5 t566 _ (by decide +kernel)
theorem cov507_6 : PA.Covered 6 (OZ.Valid 6 w507.low w507.t w507.y w507.r w507.cap) (P33.root 6) :=
  Night6836Tree.sound w507 pick507 6 t567 _ (by decide +kernel)
theorem cov507_7 : PA.Covered 7 (OZ.Valid 7 w507.low w507.t w507.y w507.r w507.cap) (P33.root 7) :=
  Night6836Tree.sound w507 pick507 7 t568 _ (by decide +kernel)
theorem window507 : P33.WindowCount w507 := by
  apply P33.window_count w507 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov507_1
  · exact cov507_2
  · exact cov507_3
  · exact cov507_4
  · exact cov507_5
  · exact cov507_6
  · exact cov507_7
def w508 : P33.Window := ⟨8,49,6382,5433,242328560604495812,43370,27000,5000000,81920000000⟩
def h508_0 : Height w508 := ⟨43370,27000,by decide +kernel⟩
def h508_1 : Height w508 := ⟨47640,24000,by decide +kernel⟩
def h508_2 : Height w508 := ⟨53120,21000,by decide +kernel⟩
def h508_3 : Height w508 := ⟨60821,18000,by decide +kernel⟩
def h508_4 : Height w508 := ⟨73318,15000,by decide +kernel⟩
def pick508 (cl : ℕ) : Height w508 := if cl<25 then (if cl<4 then (h508_0) else (h508_1)) else (if cl<157 then (h508_2) else (if cl<961 then (h508_3) else (h508_4)))
private theorem k508_1_0 : check w508 pick508 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k508_1_1 : check w508 pick508 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k508_1_2 : check w508 pick508 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w508 pick508 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k508_1_0 k508_1_1
private theorem k508_1_3 : check w508 pick508 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k508_1_4 : check w508 pick508 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k508_1_5 : check w508 pick508 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w508 pick508 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k508_1_3 k508_1_4
private theorem k508_1_6 : check w508 pick508 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w508 pick508 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k508_1_2 k508_1_5
private theorem k508_1_7 : check w508 pick508 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k508_1_8 : check w508 pick508 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k508_1_9 : check w508 pick508 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w508 pick508 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k508_1_7 k508_1_8
private theorem k508_1_10 : check w508 pick508 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k508_1_11 : check w508 pick508 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k508_1_12 : check w508 pick508 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w508 pick508 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k508_1_10 k508_1_11
private theorem k508_1_13 : check w508 pick508 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w508 pick508 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k508_1_9 k508_1_12
private theorem k508_1_14 : check w508 pick508 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w508 pick508 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k508_1_6 k508_1_13
theorem cov508_1 : PA.Covered 1 (OZ.Valid 1 w508.low w508.t w508.y w508.r w508.cap) (P33.root 1) :=
  Night6836Tree.sound w508 pick508 1 t10243 _ k508_1_14
private theorem k508_2_0 : check w508 pick508 2 t10300 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k508_2_1 : check w508 pick508 2 t10312 ⟨2,7,4,16,2,52,71,84⟩ = true := by decide +kernel
private theorem k508_2_2 : check w508 pick508 2 t10382 ⟨2,7,4,16,2,52,85,111⟩ = true := by decide +kernel
private theorem k508_2_3 : check w508 pick508 2 t10383 ⟨2,7,4,16,2,52,71,111⟩ = true := glue w508 pick508 2 ⟨2,7,4,16,2,52,71,111⟩ 3 84 t10312 t10382 k508_2_1 k508_2_2
private theorem k508_2_4 : check w508 pick508 2 t10384 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w508 pick508 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10300 t10383 k508_2_0 k508_2_3
private theorem k508_2_5 : check w508 pick508 2 t10446 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k508_2_6 : check w508 pick508 2 t9638 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k508_2_7 : check w508 pick508 2 t10670 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w508 pick508 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10446 t9638 k508_2_5 k508_2_6
private theorem k508_2_8 : check w508 pick508 2 t10671 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w508 pick508 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10384 t10670 k508_2_4 k508_2_7
theorem cov508_2 : PA.Covered 2 (OZ.Valid 2 w508.low w508.t w508.y w508.r w508.cap) (P33.root 2) :=
  Night6836Tree.sound w508 pick508 2 t10671 _ k508_2_8
theorem cov508_3 : PA.Covered 3 (OZ.Valid 3 w508.low w508.t w508.y w508.r w508.cap) (P33.root 3) :=
  Night6836Tree.sound w508 pick508 3 t564 _ (by decide +kernel)
theorem cov508_4 : PA.Covered 4 (OZ.Valid 4 w508.low w508.t w508.y w508.r w508.cap) (P33.root 4) :=
  Night6836Tree.sound w508 pick508 4 t565 _ (by decide +kernel)
theorem cov508_5 : PA.Covered 5 (OZ.Valid 5 w508.low w508.t w508.y w508.r w508.cap) (P33.root 5) :=
  Night6836Tree.sound w508 pick508 5 t566 _ (by decide +kernel)
theorem cov508_6 : PA.Covered 6 (OZ.Valid 6 w508.low w508.t w508.y w508.r w508.cap) (P33.root 6) :=
  Night6836Tree.sound w508 pick508 6 t567 _ (by decide +kernel)
theorem cov508_7 : PA.Covered 7 (OZ.Valid 7 w508.low w508.t w508.y w508.r w508.cap) (P33.root 7) :=
  Night6836Tree.sound w508 pick508 7 t2134 _ (by decide +kernel)
theorem window508 : P33.WindowCount w508 := by
  apply P33.window_count w508 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov508_1
  · exact cov508_2
  · exact cov508_3
  · exact cov508_4
  · exact cov508_5
  · exact cov508_6
  · exact cov508_7
def w509 : P33.Window := ⟨8,49,6864,6803,246846025421879597,35387,21000,5000000,81920000000⟩
def h509_0 : Height w509 := ⟨35387,21000,by decide +kernel⟩
def h509_1 : Height w509 := ⟨40041,18000,by decide +kernel⟩
def h509_2 : Height w509 := ⟨46756,15000,by decide +kernel⟩
def h509_3 : Height w509 := ⟨58520,12000,by decide +kernel⟩
def pick509 (cl : ℕ) : Height w509 := if cl<73 then (if cl<6 then (h509_0) else (h509_1)) else (if cl<925 then (h509_2) else (h509_3))
private theorem k509_1_0 : check w509 pick509 1 t10659 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k509_1_1 : check w509 pick509 1 t10661 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k509_1_2 : check w509 pick509 1 t10662 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w509 pick509 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10659 t10661 k509_1_0 k509_1_1
private theorem k509_1_3 : check w509 pick509 1 t10674 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k509_1_4 : check w509 pick509 1 t10664 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k509_1_5 : check w509 pick509 1 t10675 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w509 pick509 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10674 t10664 k509_1_3 k509_1_4
private theorem k509_1_6 : check w509 pick509 1 t10676 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w509 pick509 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10662 t10675 k509_1_2 k509_1_5
private theorem k509_1_7 : check w509 pick509 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k509_1_8 : check w509 pick509 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k509_1_9 : check w509 pick509 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w509 pick509 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k509_1_7 k509_1_8
private theorem k509_1_10 : check w509 pick509 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k509_1_11 : check w509 pick509 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k509_1_12 : check w509 pick509 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w509 pick509 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k509_1_10 k509_1_11
private theorem k509_1_13 : check w509 pick509 1 t10668 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w509 pick509 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t10667 k509_1_9 k509_1_12
private theorem k509_1_14 : check w509 pick509 1 t10677 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w509 pick509 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10676 t10668 k509_1_6 k509_1_13
theorem cov509_1 : PA.Covered 1 (OZ.Valid 1 w509.low w509.t w509.y w509.r w509.cap) (P33.root 1) :=
  Night6836Tree.sound w509 pick509 1 t10677 _ k509_1_14
private theorem k509_2_0 : check w509 pick509 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k509_2_1 : check w509 pick509 2 t10645 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k509_2_2 : check w509 pick509 2 t10646 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w509 pick509 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10645 k509_2_0 k509_2_1
private theorem k509_2_3 : check w509 pick509 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k509_2_4 : check w509 pick509 2 t10652 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k509_2_5 : check w509 pick509 2 t10653 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w509 pick509 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t10652 k509_2_3 k509_2_4
private theorem k509_2_6 : check w509 pick509 2 t10654 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w509 pick509 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10646 t10653 k509_2_2 k509_2_5
theorem cov509_2 : PA.Covered 2 (OZ.Valid 2 w509.low w509.t w509.y w509.r w509.cap) (P33.root 2) :=
  Night6836Tree.sound w509 pick509 2 t10654 _ k509_2_6
theorem cov509_3 : PA.Covered 3 (OZ.Valid 3 w509.low w509.t w509.y w509.r w509.cap) (P33.root 3) :=
  Night6836Tree.sound w509 pick509 3 t564 _ (by decide +kernel)
theorem cov509_4 : PA.Covered 4 (OZ.Valid 4 w509.low w509.t w509.y w509.r w509.cap) (P33.root 4) :=
  Night6836Tree.sound w509 pick509 4 t565 _ (by decide +kernel)
theorem cov509_5 : PA.Covered 5 (OZ.Valid 5 w509.low w509.t w509.y w509.r w509.cap) (P33.root 5) :=
  Night6836Tree.sound w509 pick509 5 t566 _ (by decide +kernel)
theorem cov509_6 : PA.Covered 6 (OZ.Valid 6 w509.low w509.t w509.y w509.r w509.cap) (P33.root 6) :=
  Night6836Tree.sound w509 pick509 6 t567 _ (by decide +kernel)
theorem cov509_7 : PA.Covered 7 (OZ.Valid 7 w509.low w509.t w509.y w509.r w509.cap) (P33.root 7) :=
  Night6836Tree.sound w509 pick509 7 t568 _ (by decide +kernel)
theorem window509 : P33.WindowCount w509 := by
  apply P33.window_count w509 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov509_1
  · exact cov509_2
  · exact cov509_3
  · exact cov509_4
  · exact cov509_5
  · exact cov509_6
  · exact cov509_7
end ProximityPrize.SubmissionLower.Night6836Bank
