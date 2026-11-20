/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT02
import ProximityPrize.SubmissionLower.Night6836SharedT03
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w390 : P33.Window := ⟨6,62,4773,4352,237712200279069050,72850,30000,5000000,81920000000⟩
def h390_0 : Height w390 := ⟨72850,30000,by decide +kernel⟩
def h390_1 : Height w390 := ⟨77320,27000,by decide +kernel⟩
def h390_2 : Height w390 := ⟨82824,24000,by decide +kernel⟩
def h390_3 : Height w390 := ⟨90014,21000,by decide +kernel⟩
def h390_4 : Height w390 := ⟨100233,18000,by decide +kernel⟩
def pick390 (cl : ℕ) : Height w390 := if cl<32 then (if cl<5 then (h390_0) else (h390_1)) else (if cl<105 then (h390_2) else (if cl<594 then (h390_3) else (h390_4)))
private theorem k390_1_0 : check w390 pick390 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k390_1_1 : check w390 pick390 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k390_1_2 : check w390 pick390 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w390 pick390 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k390_1_0 k390_1_1
private theorem k390_1_3 : check w390 pick390 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k390_1_4 : check w390 pick390 1 t9115 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k390_1_5 : check w390 pick390 1 t9516 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w390 pick390 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9115 k390_1_3 k390_1_4
private theorem k390_1_6 : check w390 pick390 1 t9517 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w390 pick390 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9516 k390_1_2 k390_1_5
private theorem k390_1_7 : check w390 pick390 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k390_1_8 : check w390 pick390 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k390_1_9 : check w390 pick390 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w390 pick390 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k390_1_7 k390_1_8
private theorem k390_1_10 : check w390 pick390 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k390_1_11 : check w390 pick390 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k390_1_12 : check w390 pick390 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w390 pick390 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k390_1_10 k390_1_11
private theorem k390_1_13 : check w390 pick390 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w390 pick390 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k390_1_9 k390_1_12
private theorem k390_1_14 : check w390 pick390 1 t9518 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w390 pick390 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9517 t9097 k390_1_6 k390_1_13
theorem cov390_1 : PA.Covered 1 (OZ.Valid 1 w390.low w390.t w390.y w390.r w390.cap) (P33.root 1) :=
  Night6836Tree.sound w390 pick390 1 t9518 _ k390_1_14
theorem cov390_2 : PA.Covered 2 (OZ.Valid 2 w390.low w390.t w390.y w390.r w390.cap) (P33.root 2) :=
  Night6836Tree.sound w390 pick390 2 t9132 _ (by decide +kernel)
theorem cov390_3 : PA.Covered 3 (OZ.Valid 3 w390.low w390.t w390.y w390.r w390.cap) (P33.root 3) :=
  Night6836Tree.sound w390 pick390 3 t564 _ (by decide +kernel)
theorem cov390_4 : PA.Covered 4 (OZ.Valid 4 w390.low w390.t w390.y w390.r w390.cap) (P33.root 4) :=
  Night6836Tree.sound w390 pick390 4 t565 _ (by decide +kernel)
theorem cov390_5 : PA.Covered 5 (OZ.Valid 5 w390.low w390.t w390.y w390.r w390.cap) (P33.root 5) :=
  Night6836Tree.sound w390 pick390 5 t566 _ (by decide +kernel)
theorem cov390_6 : PA.Covered 6 (OZ.Valid 6 w390.low w390.t w390.y w390.r w390.cap) (P33.root 6) :=
  Night6836Tree.sound w390 pick390 6 t567 _ (by decide +kernel)
theorem cov390_7 : PA.Covered 7 (OZ.Valid 7 w390.low w390.t w390.y w390.r w390.cap) (P33.root 7) :=
  Night6836Tree.sound w390 pick390 7 t2134 _ (by decide +kernel)
theorem window390 : P33.WindowCount w390 := by
  apply P33.window_count w390 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov390_1
  · exact cov390_2
  · exact cov390_3
  · exact cov390_4
  · exact cov390_5
  · exact cov390_6
  · exact cov390_7
def w391 : P33.Window := ⟨6,63,4351,3914,242047748248461960,79212,36000,5000000,81920000000⟩
def h391_0 : Height w391 := ⟨79212,36000,by decide +kernel⟩
def h391_1 : Height w391 := ⟨83128,33000,by decide +kernel⟩
def h391_2 : Height w391 := ⟨87688,30000,by decide +kernel⟩
def h391_3 : Height w391 := ⟨93189,27000,by decide +kernel⟩
def h391_4 : Height w391 := ⟨100143,24000,by decide +kernel⟩
def h391_5 : Height w391 := ⟨109515,21000,by decide +kernel⟩
def pick391 (cl : ℕ) : Height w391 := if cl<32 then (if cl<2 then (h391_0) else (if cl<6 then (h391_1) else (h391_2))) else (if cl<92 then (h391_3) else (if cl<302 then (h391_4) else (h391_5)))
private theorem k391_1_0 : check w391 pick391 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k391_1_1 : check w391 pick391 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k391_1_2 : check w391 pick391 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w391 pick391 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k391_1_0 k391_1_1
private theorem k391_1_3 : check w391 pick391 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k391_1_4 : check w391 pick391 1 t9115 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k391_1_5 : check w391 pick391 1 t9516 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w391 pick391 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9115 k391_1_3 k391_1_4
private theorem k391_1_6 : check w391 pick391 1 t9517 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w391 pick391 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9516 k391_1_2 k391_1_5
private theorem k391_1_7 : check w391 pick391 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k391_1_8 : check w391 pick391 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k391_1_9 : check w391 pick391 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w391 pick391 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k391_1_7 k391_1_8
private theorem k391_1_10 : check w391 pick391 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k391_1_11 : check w391 pick391 1 t5274 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k391_1_12 : check w391 pick391 1 t9519 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w391 pick391 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t5274 k391_1_10 k391_1_11
private theorem k391_1_13 : check w391 pick391 1 t9520 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w391 pick391 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9519 k391_1_9 k391_1_12
private theorem k391_1_14 : check w391 pick391 1 t9521 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w391 pick391 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9517 t9520 k391_1_6 k391_1_13
theorem cov391_1 : PA.Covered 1 (OZ.Valid 1 w391.low w391.t w391.y w391.r w391.cap) (P33.root 1) :=
  Night6836Tree.sound w391 pick391 1 t9521 _ k391_1_14
theorem cov391_2 : PA.Covered 2 (OZ.Valid 2 w391.low w391.t w391.y w391.r w391.cap) (P33.root 2) :=
  Night6836Tree.sound w391 pick391 2 t6109 _ (by decide +kernel)
theorem cov391_3 : PA.Covered 3 (OZ.Valid 3 w391.low w391.t w391.y w391.r w391.cap) (P33.root 3) :=
  Night6836Tree.sound w391 pick391 3 t564 _ (by decide +kernel)
theorem cov391_4 : PA.Covered 4 (OZ.Valid 4 w391.low w391.t w391.y w391.r w391.cap) (P33.root 4) :=
  Night6836Tree.sound w391 pick391 4 t565 _ (by decide +kernel)
theorem cov391_5 : PA.Covered 5 (OZ.Valid 5 w391.low w391.t w391.y w391.r w391.cap) (P33.root 5) :=
  Night6836Tree.sound w391 pick391 5 t566 _ (by decide +kernel)
theorem cov391_6 : PA.Covered 6 (OZ.Valid 6 w391.low w391.t w391.y w391.r w391.cap) (P33.root 6) :=
  Night6836Tree.sound w391 pick391 6 t567 _ (by decide +kernel)
theorem cov391_7 : PA.Covered 7 (OZ.Valid 7 w391.low w391.t w391.y w391.r w391.cap) (P33.root 7) :=
  Night6836Tree.sound w391 pick391 7 t2134 _ (by decide +kernel)
theorem window391 : P33.WindowCount w391 := by
  apply P33.window_count w391 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov391_1
  · exact cov391_2
  · exact cov391_3
  · exact cov391_4
  · exact cov391_5
  · exact cov391_6
  · exact cov391_7
def w392 : P33.Window := ⟨6,64,3913,3461,239063326284164740,93559,39000,5000000,81920000000⟩
def h392_0 : Height w392 := ⟨93559,39000,by decide +kernel⟩
def h392_1 : Height w392 := ⟨97770,36000,by decide +kernel⟩
def h392_2 : Height w392 := ⟨102644,33000,by decide +kernel⟩
def h392_3 : Height w392 := ⟨108456,30000,by decide +kernel⟩
def h392_4 : Height w392 := ⟨115661,27000,by decide +kernel⟩
def h392_5 : Height w392 := ⟨125063,24000,by decide +kernel⟩
def pick392 (cl : ℕ) : Height w392 := if cl<32 then (if cl<4 then (h392_0) else (if cl<13 then (h392_1) else (h392_2))) else (if cl<105 then (h392_3) else (if cl<312 then (h392_4) else (h392_5)))
private theorem k392_1_0 : check w392 pick392 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k392_1_1 : check w392 pick392 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k392_1_2 : check w392 pick392 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w392 pick392 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k392_1_0 k392_1_1
private theorem k392_1_3 : check w392 pick392 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k392_1_4 : check w392 pick392 1 t9115 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k392_1_5 : check w392 pick392 1 t9516 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w392 pick392 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9115 k392_1_3 k392_1_4
private theorem k392_1_6 : check w392 pick392 1 t9517 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w392 pick392 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9516 k392_1_2 k392_1_5
private theorem k392_1_7 : check w392 pick392 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k392_1_8 : check w392 pick392 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k392_1_9 : check w392 pick392 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w392 pick392 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k392_1_7 k392_1_8
private theorem k392_1_10 : check w392 pick392 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k392_1_11 : check w392 pick392 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w392 pick392 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k392_1_9 k392_1_10
private theorem k392_1_12 : check w392 pick392 1 t9522 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w392 pick392 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9517 t5276 k392_1_6 k392_1_11
theorem cov392_1 : PA.Covered 1 (OZ.Valid 1 w392.low w392.t w392.y w392.r w392.cap) (P33.root 1) :=
  Night6836Tree.sound w392 pick392 1 t9522 _ k392_1_12
theorem cov392_2 : PA.Covered 2 (OZ.Valid 2 w392.low w392.t w392.y w392.r w392.cap) (P33.root 2) :=
  Night6836Tree.sound w392 pick392 2 t6109 _ (by decide +kernel)
theorem cov392_3 : PA.Covered 3 (OZ.Valid 3 w392.low w392.t w392.y w392.r w392.cap) (P33.root 3) :=
  Night6836Tree.sound w392 pick392 3 t564 _ (by decide +kernel)
theorem cov392_4 : PA.Covered 4 (OZ.Valid 4 w392.low w392.t w392.y w392.r w392.cap) (P33.root 4) :=
  Night6836Tree.sound w392 pick392 4 t565 _ (by decide +kernel)
theorem cov392_5 : PA.Covered 5 (OZ.Valid 5 w392.low w392.t w392.y w392.r w392.cap) (P33.root 5) :=
  Night6836Tree.sound w392 pick392 5 t566 _ (by decide +kernel)
theorem cov392_6 : PA.Covered 6 (OZ.Valid 6 w392.low w392.t w392.y w392.r w392.cap) (P33.root 6) :=
  Night6836Tree.sound w392 pick392 6 t567 _ (by decide +kernel)
theorem cov392_7 : PA.Covered 7 (OZ.Valid 7 w392.low w392.t w392.y w392.r w392.cap) (P33.root 7) :=
  Night6836Tree.sound w392 pick392 7 t2134 _ (by decide +kernel)
theorem window392 : P33.WindowCount w392 := by
  apply P33.window_count w392 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov392_1
  · exact cov392_2
  · exact cov392_3
  · exact cov392_4
  · exact cov392_5
  · exact cov392_6
  · exact cov392_7
def w393 : P33.Window := ⟨6,65,3460,2993,214860856141515895,110408,45000,5000000,81920000000⟩
def h393_0 : Height w393 := ⟨110408,45000,by decide +kernel⟩
def h393_1 : Height w393 := ⟨114630,42000,by decide +kernel⟩
def h393_2 : Height w393 := ⟨119410,39000,by decide +kernel⟩
def h393_3 : Height w393 := ⟨124939,36000,by decide +kernel⟩
def h393_4 : Height w393 := ⟨131505,33000,by decide +kernel⟩
def h393_5 : Height w393 := ⟨139568,30000,by decide +kernel⟩
def h393_6 : Height w393 := ⟨149902,27000,by decide +kernel⟩
def pick393 (cl : ℕ) : Height w393 := if cl<32 then (if cl<4 then (h393_0) else (if cl<10 then (h393_1) else (h393_2))) else (if cl<195 then (if cl<62 then (h393_3) else (h393_4)) else (if cl<644 then (h393_5) else (h393_6)))
private theorem k393_1_0 : check w393 pick393 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k393_1_1 : check w393 pick393 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k393_1_2 : check w393 pick393 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w393 pick393 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k393_1_0 k393_1_1
private theorem k393_1_3 : check w393 pick393 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k393_1_4 : check w393 pick393 1 t9115 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k393_1_5 : check w393 pick393 1 t9516 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w393 pick393 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9115 k393_1_3 k393_1_4
private theorem k393_1_6 : check w393 pick393 1 t9517 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w393 pick393 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9516 k393_1_2 k393_1_5
private theorem k393_1_7 : check w393 pick393 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k393_1_8 : check w393 pick393 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k393_1_9 : check w393 pick393 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w393 pick393 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k393_1_7 k393_1_8
private theorem k393_1_10 : check w393 pick393 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k393_1_11 : check w393 pick393 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w393 pick393 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k393_1_9 k393_1_10
private theorem k393_1_12 : check w393 pick393 1 t9522 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w393 pick393 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9517 t5276 k393_1_6 k393_1_11
theorem cov393_1 : PA.Covered 1 (OZ.Valid 1 w393.low w393.t w393.y w393.r w393.cap) (P33.root 1) :=
  Night6836Tree.sound w393 pick393 1 t9522 _ k393_1_12
theorem cov393_2 : PA.Covered 2 (OZ.Valid 2 w393.low w393.t w393.y w393.r w393.cap) (P33.root 2) :=
  Night6836Tree.sound w393 pick393 2 t6560 _ (by decide +kernel)
theorem cov393_3 : PA.Covered 3 (OZ.Valid 3 w393.low w393.t w393.y w393.r w393.cap) (P33.root 3) :=
  Night6836Tree.sound w393 pick393 3 t564 _ (by decide +kernel)
theorem cov393_4 : PA.Covered 4 (OZ.Valid 4 w393.low w393.t w393.y w393.r w393.cap) (P33.root 4) :=
  Night6836Tree.sound w393 pick393 4 t565 _ (by decide +kernel)
theorem cov393_5 : PA.Covered 5 (OZ.Valid 5 w393.low w393.t w393.y w393.r w393.cap) (P33.root 5) :=
  Night6836Tree.sound w393 pick393 5 t566 _ (by decide +kernel)
theorem cov393_6 : PA.Covered 6 (OZ.Valid 6 w393.low w393.t w393.y w393.r w393.cap) (P33.root 6) :=
  Night6836Tree.sound w393 pick393 6 t567 _ (by decide +kernel)
theorem cov393_7 : PA.Covered 7 (OZ.Valid 7 w393.low w393.t w393.y w393.r w393.cap) (P33.root 7) :=
  Night6836Tree.sound w393 pick393 7 t2134 _ (by decide +kernel)
theorem window393 : P33.WindowCount w393 := by
  apply P33.window_count w393 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov393_1
  · exact cov393_2
  · exact cov393_3
  · exact cov393_4
  · exact cov393_5
  · exact cov393_6
  · exact cov393_7
def w394 : P33.Window := ⟨6,66,2992,2729,198768131966588192,121240,51000,5000000,81920000000⟩
def h394_0 : Height w394 := ⟨121240,51000,by decide +kernel⟩
def h394_1 : Height w394 := ⟨125249,48000,by decide +kernel⟩
def h394_2 : Height w394 := ⟨129696,45000,by decide +kernel⟩
def h394_3 : Height w394 := ⟨134707,42000,by decide +kernel⟩
def h394_4 : Height w394 := ⟨140459,39000,by decide +kernel⟩
def h394_5 : Height w394 := ⟨147216,36000,by decide +kernel⟩
def h394_6 : Height w394 := ⟨155380,33000,by decide +kernel⟩
def h394_7 : Height w394 := ⟨165601,30000,by decide +kernel⟩
def pick394 (cl : ℕ) : Height w394 := if cl<32 then (if cl<5 then (if cl<2 then (h394_0) else (h394_1)) else (if cl<16 then (h394_2) else (h394_3))) else (if cl<202 then (if cl<83 then (h394_4) else (h394_5)) else (if cl<594 then (h394_6) else (h394_7)))
private theorem k394_1_0 : check w394 pick394 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k394_1_1 : check w394 pick394 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k394_1_2 : check w394 pick394 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w394 pick394 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k394_1_0 k394_1_1
private theorem k394_1_3 : check w394 pick394 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k394_1_4 : check w394 pick394 1 t9115 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k394_1_5 : check w394 pick394 1 t9516 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w394 pick394 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9115 k394_1_3 k394_1_4
private theorem k394_1_6 : check w394 pick394 1 t9517 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w394 pick394 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9516 k394_1_2 k394_1_5
private theorem k394_1_7 : check w394 pick394 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k394_1_8 : check w394 pick394 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k394_1_9 : check w394 pick394 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w394 pick394 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k394_1_7 k394_1_8
private theorem k394_1_10 : check w394 pick394 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k394_1_11 : check w394 pick394 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w394 pick394 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k394_1_9 k394_1_10
private theorem k394_1_12 : check w394 pick394 1 t9522 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w394 pick394 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9517 t5276 k394_1_6 k394_1_11
theorem cov394_1 : PA.Covered 1 (OZ.Valid 1 w394.low w394.t w394.y w394.r w394.cap) (P33.root 1) :=
  Night6836Tree.sound w394 pick394 1 t9522 _ k394_1_12
theorem cov394_2 : PA.Covered 2 (OZ.Valid 2 w394.low w394.t w394.y w394.r w394.cap) (P33.root 2) :=
  Night6836Tree.sound w394 pick394 2 t6560 _ (by decide +kernel)
theorem cov394_3 : PA.Covered 3 (OZ.Valid 3 w394.low w394.t w394.y w394.r w394.cap) (P33.root 3) :=
  Night6836Tree.sound w394 pick394 3 t564 _ (by decide +kernel)
theorem cov394_4 : PA.Covered 4 (OZ.Valid 4 w394.low w394.t w394.y w394.r w394.cap) (P33.root 4) :=
  Night6836Tree.sound w394 pick394 4 t565 _ (by decide +kernel)
theorem cov394_5 : PA.Covered 5 (OZ.Valid 5 w394.low w394.t w394.y w394.r w394.cap) (P33.root 5) :=
  Night6836Tree.sound w394 pick394 5 t566 _ (by decide +kernel)
theorem cov394_6 : PA.Covered 6 (OZ.Valid 6 w394.low w394.t w394.y w394.r w394.cap) (P33.root 6) :=
  Night6836Tree.sound w394 pick394 6 t567 _ (by decide +kernel)
theorem cov394_7 : PA.Covered 7 (OZ.Valid 7 w394.low w394.t w394.y w394.r w394.cap) (P33.root 7) :=
  Night6836Tree.sound w394 pick394 7 t2134 _ (by decide +kernel)
theorem window394 : P33.WindowCount w394 := by
  apply P33.window_count w394 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov394_1
  · exact cov394_2
  · exact cov394_3
  · exact cov394_4
  · exact cov394_5
  · exact cov394_6
  · exact cov394_7
def w395 : P33.Window := ⟨7,22,8153,8120,210517696858066792,11770,12000,5000000,81920000000⟩
def h395_0 : Height w395 := ⟨11770,12000,by decide +kernel⟩
def h395_1 : Height w395 := ⟨17335,9000,by decide +kernel⟩
def pick395 (cl : ℕ) : Height w395 := if cl<32 then (h395_0) else (h395_1)
private theorem k395_1_0 : check w395 pick395 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k395_1_1 : check w395 pick395 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k395_1_2 : check w395 pick395 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w395 pick395 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k395_1_0 k395_1_1
private theorem k395_1_3 : check w395 pick395 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k395_1_4 : check w395 pick395 1 t9528 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k395_1_5 : check w395 pick395 1 t9529 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w395 pick395 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9528 k395_1_3 k395_1_4
private theorem k395_1_6 : check w395 pick395 1 t9530 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w395 pick395 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t9529 k395_1_2 k395_1_5
private theorem k395_1_7 : check w395 pick395 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k395_1_8 : check w395 pick395 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k395_1_9 : check w395 pick395 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w395 pick395 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k395_1_7 k395_1_8
private theorem k395_1_10 : check w395 pick395 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k395_1_11 : check w395 pick395 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k395_1_12 : check w395 pick395 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w395 pick395 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k395_1_10 k395_1_11
private theorem k395_1_13 : check w395 pick395 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w395 pick395 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k395_1_9 k395_1_12
private theorem k395_1_14 : check w395 pick395 1 t9531 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w395 pick395 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9530 t2461 k395_1_6 k395_1_13
theorem cov395_1 : PA.Covered 1 (OZ.Valid 1 w395.low w395.t w395.y w395.r w395.cap) (P33.root 1) :=
  Night6836Tree.sound w395 pick395 1 t9531 _ k395_1_14
theorem cov395_2 : PA.Covered 2 (OZ.Valid 2 w395.low w395.t w395.y w395.r w395.cap) (P33.root 2) :=
  Night6836Tree.sound w395 pick395 2 t2745 _ (by decide +kernel)
theorem cov395_3 : PA.Covered 3 (OZ.Valid 3 w395.low w395.t w395.y w395.r w395.cap) (P33.root 3) :=
  Night6836Tree.sound w395 pick395 3 t564 _ (by decide +kernel)
theorem cov395_4 : PA.Covered 4 (OZ.Valid 4 w395.low w395.t w395.y w395.r w395.cap) (P33.root 4) :=
  Night6836Tree.sound w395 pick395 4 t565 _ (by decide +kernel)
theorem cov395_5 : PA.Covered 5 (OZ.Valid 5 w395.low w395.t w395.y w395.r w395.cap) (P33.root 5) :=
  Night6836Tree.sound w395 pick395 5 t566 _ (by decide +kernel)
theorem cov395_6 : PA.Covered 6 (OZ.Valid 6 w395.low w395.t w395.y w395.r w395.cap) (P33.root 6) :=
  Night6836Tree.sound w395 pick395 6 t567 _ (by decide +kernel)
theorem cov395_7 : PA.Covered 7 (OZ.Valid 7 w395.low w395.t w395.y w395.r w395.cap) (P33.root 7) :=
  Night6836Tree.sound w395 pick395 7 t568 _ (by decide +kernel)
theorem window395 : P33.WindowCount w395 := by
  apply P33.window_count w395 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov395_1
  · exact cov395_2
  · exact cov395_3
  · exact cov395_4
  · exact cov395_5
  · exact cov395_6
  · exact cov395_7
def w396 : P33.Window := ⟨7,24,8123,7124,200630859350905390,13887,15000,5000000,81920000000⟩
def h396_0 : Height w396 := ⟨13887,15000,by decide +kernel⟩
def h396_1 : Height w396 := ⟨20468,11000,by decide +kernel⟩
def pick396 (cl : ℕ) : Height w396 := if cl<12 then (h396_0) else (h396_1)
private theorem k396_1_0 : check w396 pick396 1 t2748 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k396_1_1 : check w396 pick396 1 t2764 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k396_1_2 : check w396 pick396 1 t2765 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w396 pick396 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t2748 t2764 k396_1_0 k396_1_1
private theorem k396_1_3 : check w396 pick396 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k396_1_4 : check w396 pick396 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k396_1_5 : check w396 pick396 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w396 pick396 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k396_1_3 k396_1_4
private theorem k396_1_6 : check w396 pick396 1 t9538 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w396 pick396 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2765 t9537 k396_1_2 k396_1_5
private theorem k396_1_7 : check w396 pick396 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k396_1_8 : check w396 pick396 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k396_1_9 : check w396 pick396 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w396 pick396 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k396_1_7 k396_1_8
private theorem k396_1_10 : check w396 pick396 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k396_1_11 : check w396 pick396 1 t9540 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k396_1_12 : check w396 pick396 1 t9541 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w396 pick396 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9540 k396_1_10 k396_1_11
private theorem k396_1_13 : check w396 pick396 1 t9542 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w396 pick396 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9541 k396_1_9 k396_1_12
private theorem k396_1_14 : check w396 pick396 1 t9543 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w396 pick396 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9538 t9542 k396_1_6 k396_1_13
theorem cov396_1 : PA.Covered 1 (OZ.Valid 1 w396.low w396.t w396.y w396.r w396.cap) (P33.root 1) :=
  Night6836Tree.sound w396 pick396 1 t9543 _ k396_1_14
private theorem k396_2_0 : check w396 pick396 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k396_2_1 : check w396 pick396 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k396_2_2 : check w396 pick396 2 t9544 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w396 pick396 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9135 k396_2_0 k396_2_1
theorem cov396_2 : PA.Covered 2 (OZ.Valid 2 w396.low w396.t w396.y w396.r w396.cap) (P33.root 2) :=
  Night6836Tree.sound w396 pick396 2 t9544 _ k396_2_2
theorem cov396_3 : PA.Covered 3 (OZ.Valid 3 w396.low w396.t w396.y w396.r w396.cap) (P33.root 3) :=
  Night6836Tree.sound w396 pick396 3 t564 _ (by decide +kernel)
theorem cov396_4 : PA.Covered 4 (OZ.Valid 4 w396.low w396.t w396.y w396.r w396.cap) (P33.root 4) :=
  Night6836Tree.sound w396 pick396 4 t565 _ (by decide +kernel)
theorem cov396_5 : PA.Covered 5 (OZ.Valid 5 w396.low w396.t w396.y w396.r w396.cap) (P33.root 5) :=
  Night6836Tree.sound w396 pick396 5 t566 _ (by decide +kernel)
theorem cov396_6 : PA.Covered 6 (OZ.Valid 6 w396.low w396.t w396.y w396.r w396.cap) (P33.root 6) :=
  Night6836Tree.sound w396 pick396 6 t567 _ (by decide +kernel)
theorem cov396_7 : PA.Covered 7 (OZ.Valid 7 w396.low w396.t w396.y w396.r w396.cap) (P33.root 7) :=
  Night6836Tree.sound w396 pick396 7 t568 _ (by decide +kernel)
theorem window396 : P33.WindowCount w396 := by
  apply P33.window_count w396 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov396_1
  · exact cov396_2
  · exact cov396_3
  · exact cov396_4
  · exact cov396_5
  · exact cov396_6
  · exact cov396_7
def w397 : P33.Window := ⟨7,25,8050,8016,218819353436588487,15069,12000,5000000,81920000000⟩
def h397_0 : Height w397 := ⟨15069,12000,by decide +kernel⟩
def h397_1 : Height w397 := ⟨21505,9000,by decide +kernel⟩
def pick397 (cl : ℕ) : Height w397 := if cl<55 then (h397_0) else (h397_1)
private theorem k397_1_0 : check w397 pick397 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k397_1_1 : check w397 pick397 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k397_1_2 : check w397 pick397 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w397 pick397 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k397_1_0 k397_1_1
private theorem k397_1_3 : check w397 pick397 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k397_1_4 : check w397 pick397 1 t9528 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k397_1_5 : check w397 pick397 1 t9529 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w397 pick397 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9528 k397_1_3 k397_1_4
private theorem k397_1_6 : check w397 pick397 1 t9530 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w397 pick397 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t9529 k397_1_2 k397_1_5
private theorem k397_1_7 : check w397 pick397 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k397_1_8 : check w397 pick397 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k397_1_9 : check w397 pick397 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w397 pick397 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k397_1_7 k397_1_8
private theorem k397_1_10 : check w397 pick397 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k397_1_11 : check w397 pick397 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k397_1_12 : check w397 pick397 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w397 pick397 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k397_1_10 k397_1_11
private theorem k397_1_13 : check w397 pick397 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w397 pick397 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k397_1_9 k397_1_12
private theorem k397_1_14 : check w397 pick397 1 t9531 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w397 pick397 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9530 t2461 k397_1_6 k397_1_13
theorem cov397_1 : PA.Covered 1 (OZ.Valid 1 w397.low w397.t w397.y w397.r w397.cap) (P33.root 1) :=
  Night6836Tree.sound w397 pick397 1 t9531 _ k397_1_14
theorem cov397_2 : PA.Covered 2 (OZ.Valid 2 w397.low w397.t w397.y w397.r w397.cap) (P33.root 2) :=
  Night6836Tree.sound w397 pick397 2 t2745 _ (by decide +kernel)
theorem cov397_3 : PA.Covered 3 (OZ.Valid 3 w397.low w397.t w397.y w397.r w397.cap) (P33.root 3) :=
  Night6836Tree.sound w397 pick397 3 t564 _ (by decide +kernel)
theorem cov397_4 : PA.Covered 4 (OZ.Valid 4 w397.low w397.t w397.y w397.r w397.cap) (P33.root 4) :=
  Night6836Tree.sound w397 pick397 4 t565 _ (by decide +kernel)
theorem cov397_5 : PA.Covered 5 (OZ.Valid 5 w397.low w397.t w397.y w397.r w397.cap) (P33.root 5) :=
  Night6836Tree.sound w397 pick397 5 t566 _ (by decide +kernel)
theorem cov397_6 : PA.Covered 6 (OZ.Valid 6 w397.low w397.t w397.y w397.r w397.cap) (P33.root 6) :=
  Night6836Tree.sound w397 pick397 6 t567 _ (by decide +kernel)
theorem cov397_7 : PA.Covered 7 (OZ.Valid 7 w397.low w397.t w397.y w397.r w397.cap) (P33.root 7) :=
  Night6836Tree.sound w397 pick397 7 t568 _ (by decide +kernel)
theorem window397 : P33.WindowCount w397 := by
  apply P33.window_count w397 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov397_1
  · exact cov397_2
  · exact cov397_3
  · exact cov397_4
  · exact cov397_5
  · exact cov397_6
  · exact cov397_7
def w398 : P33.Window := ⟨7,26,8015,7981,223261284803360856,16200,12000,5000000,81920000000⟩
def h398_0 : Height w398 := ⟨16200,12000,by decide +kernel⟩
def h398_1 : Height w398 := ⟨22943,9000,by decide +kernel⟩
def pick398 (cl : ℕ) : Height w398 := if cl<83 then (h398_0) else (h398_1)
private theorem k398_1_0 : check w398 pick398 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k398_1_1 : check w398 pick398 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k398_1_2 : check w398 pick398 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w398 pick398 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k398_1_0 k398_1_1
private theorem k398_1_3 : check w398 pick398 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k398_1_4 : check w398 pick398 1 t9528 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k398_1_5 : check w398 pick398 1 t9529 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w398 pick398 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9528 k398_1_3 k398_1_4
private theorem k398_1_6 : check w398 pick398 1 t9530 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w398 pick398 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t9529 k398_1_2 k398_1_5
private theorem k398_1_7 : check w398 pick398 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k398_1_8 : check w398 pick398 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k398_1_9 : check w398 pick398 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w398 pick398 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k398_1_7 k398_1_8
private theorem k398_1_10 : check w398 pick398 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k398_1_11 : check w398 pick398 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k398_1_12 : check w398 pick398 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w398 pick398 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k398_1_10 k398_1_11
private theorem k398_1_13 : check w398 pick398 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w398 pick398 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k398_1_9 k398_1_12
private theorem k398_1_14 : check w398 pick398 1 t9545 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w398 pick398 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9530 t3549 k398_1_6 k398_1_13
theorem cov398_1 : PA.Covered 1 (OZ.Valid 1 w398.low w398.t w398.y w398.r w398.cap) (P33.root 1) :=
  Night6836Tree.sound w398 pick398 1 t9545 _ k398_1_14
theorem cov398_2 : PA.Covered 2 (OZ.Valid 2 w398.low w398.t w398.y w398.r w398.cap) (P33.root 2) :=
  Night6836Tree.sound w398 pick398 2 t2745 _ (by decide +kernel)
theorem cov398_3 : PA.Covered 3 (OZ.Valid 3 w398.low w398.t w398.y w398.r w398.cap) (P33.root 3) :=
  Night6836Tree.sound w398 pick398 3 t564 _ (by decide +kernel)
theorem cov398_4 : PA.Covered 4 (OZ.Valid 4 w398.low w398.t w398.y w398.r w398.cap) (P33.root 4) :=
  Night6836Tree.sound w398 pick398 4 t565 _ (by decide +kernel)
theorem cov398_5 : PA.Covered 5 (OZ.Valid 5 w398.low w398.t w398.y w398.r w398.cap) (P33.root 5) :=
  Night6836Tree.sound w398 pick398 5 t566 _ (by decide +kernel)
theorem cov398_6 : PA.Covered 6 (OZ.Valid 6 w398.low w398.t w398.y w398.r w398.cap) (P33.root 6) :=
  Night6836Tree.sound w398 pick398 6 t567 _ (by decide +kernel)
theorem cov398_7 : PA.Covered 7 (OZ.Valid 7 w398.low w398.t w398.y w398.r w398.cap) (P33.root 7) :=
  Night6836Tree.sound w398 pick398 7 t568 _ (by decide +kernel)
theorem window398 : P33.WindowCount w398 := by
  apply P33.window_count w398 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov398_1
  · exact cov398_2
  · exact cov398_3
  · exact cov398_4
  · exact cov398_5
  · exact cov398_6
  · exact cov398_7
def w399 : P33.Window := ⟨7,27,7980,7946,227655508402240758,13428,15000,5000000,81920000000⟩
def h399_0 : Height w399 := ⟨13428,15000,by decide +kernel⟩
def h399_1 : Height w399 := ⟨17346,12000,by decide +kernel⟩
def h399_2 : Height w399 := ⟨24405,9000,by decide +kernel⟩
def pick399 (cl : ℕ) : Height w399 := if cl<2 then (h399_0) else (if cl<100 then (h399_1) else (h399_2))
private theorem k399_1_0 : check w399 pick399 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k399_1_1 : check w399 pick399 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k399_1_2 : check w399 pick399 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w399 pick399 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k399_1_0 k399_1_1
private theorem k399_1_3 : check w399 pick399 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k399_1_4 : check w399 pick399 1 t9528 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k399_1_5 : check w399 pick399 1 t9529 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w399 pick399 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9528 k399_1_3 k399_1_4
private theorem k399_1_6 : check w399 pick399 1 t9530 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w399 pick399 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t9529 k399_1_2 k399_1_5
private theorem k399_1_7 : check w399 pick399 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k399_1_8 : check w399 pick399 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k399_1_9 : check w399 pick399 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w399 pick399 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k399_1_7 k399_1_8
private theorem k399_1_10 : check w399 pick399 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k399_1_11 : check w399 pick399 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k399_1_12 : check w399 pick399 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w399 pick399 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k399_1_10 k399_1_11
private theorem k399_1_13 : check w399 pick399 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w399 pick399 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k399_1_9 k399_1_12
private theorem k399_1_14 : check w399 pick399 1 t9545 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w399 pick399 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9530 t3549 k399_1_6 k399_1_13
theorem cov399_1 : PA.Covered 1 (OZ.Valid 1 w399.low w399.t w399.y w399.r w399.cap) (P33.root 1) :=
  Night6836Tree.sound w399 pick399 1 t9545 _ k399_1_14
theorem cov399_2 : PA.Covered 2 (OZ.Valid 2 w399.low w399.t w399.y w399.r w399.cap) (P33.root 2) :=
  Night6836Tree.sound w399 pick399 2 t2745 _ (by decide +kernel)
theorem cov399_3 : PA.Covered 3 (OZ.Valid 3 w399.low w399.t w399.y w399.r w399.cap) (P33.root 3) :=
  Night6836Tree.sound w399 pick399 3 t564 _ (by decide +kernel)
theorem cov399_4 : PA.Covered 4 (OZ.Valid 4 w399.low w399.t w399.y w399.r w399.cap) (P33.root 4) :=
  Night6836Tree.sound w399 pick399 4 t565 _ (by decide +kernel)
theorem cov399_5 : PA.Covered 5 (OZ.Valid 5 w399.low w399.t w399.y w399.r w399.cap) (P33.root 5) :=
  Night6836Tree.sound w399 pick399 5 t566 _ (by decide +kernel)
theorem cov399_6 : PA.Covered 6 (OZ.Valid 6 w399.low w399.t w399.y w399.r w399.cap) (P33.root 6) :=
  Night6836Tree.sound w399 pick399 6 t567 _ (by decide +kernel)
theorem cov399_7 : PA.Covered 7 (OZ.Valid 7 w399.low w399.t w399.y w399.r w399.cap) (P33.root 7) :=
  Night6836Tree.sound w399 pick399 7 t568 _ (by decide +kernel)
theorem window399 : P33.WindowCount w399 := by
  apply P33.window_count w399 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov399_1
  · exact cov399_2
  · exact cov399_3
  · exact cov399_4
  · exact cov399_5
  · exact cov399_6
  · exact cov399_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w400 : P33.Window := ⟨7,28,7945,7910,232002024233228192,14459,15000,5000000,81920000000⟩
def h400_0 : Height w400 := ⟨14459,15000,by decide +kernel⟩
def h400_1 : Height w400 := ⟨18514,12000,by decide +kernel⟩
def h400_2 : Height w400 := ⟨25900,9000,by decide +kernel⟩
def pick400 (cl : ℕ) : Height w400 := if cl<2 then (h400_0) else (if cl<120 then (h400_1) else (h400_2))
private theorem k400_1_0 : check w400 pick400 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k400_1_1 : check w400 pick400 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k400_1_2 : check w400 pick400 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w400 pick400 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k400_1_0 k400_1_1
private theorem k400_1_3 : check w400 pick400 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k400_1_4 : check w400 pick400 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k400_1_5 : check w400 pick400 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w400 pick400 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k400_1_3 k400_1_4
private theorem k400_1_6 : check w400 pick400 1 t9546 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w400 pick400 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9537 k400_1_2 k400_1_5
private theorem k400_1_7 : check w400 pick400 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k400_1_8 : check w400 pick400 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k400_1_9 : check w400 pick400 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w400 pick400 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k400_1_7 k400_1_8
private theorem k400_1_10 : check w400 pick400 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k400_1_11 : check w400 pick400 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k400_1_12 : check w400 pick400 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w400 pick400 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k400_1_10 k400_1_11
private theorem k400_1_13 : check w400 pick400 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w400 pick400 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k400_1_9 k400_1_12
private theorem k400_1_14 : check w400 pick400 1 t9547 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w400 pick400 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9546 t3549 k400_1_6 k400_1_13
theorem cov400_1 : PA.Covered 1 (OZ.Valid 1 w400.low w400.t w400.y w400.r w400.cap) (P33.root 1) :=
  Night6836Tree.sound w400 pick400 1 t9547 _ k400_1_14
theorem cov400_2 : PA.Covered 2 (OZ.Valid 2 w400.low w400.t w400.y w400.r w400.cap) (P33.root 2) :=
  Night6836Tree.sound w400 pick400 2 t2745 _ (by decide +kernel)
theorem cov400_3 : PA.Covered 3 (OZ.Valid 3 w400.low w400.t w400.y w400.r w400.cap) (P33.root 3) :=
  Night6836Tree.sound w400 pick400 3 t564 _ (by decide +kernel)
theorem cov400_4 : PA.Covered 4 (OZ.Valid 4 w400.low w400.t w400.y w400.r w400.cap) (P33.root 4) :=
  Night6836Tree.sound w400 pick400 4 t565 _ (by decide +kernel)
theorem cov400_5 : PA.Covered 5 (OZ.Valid 5 w400.low w400.t w400.y w400.r w400.cap) (P33.root 5) :=
  Night6836Tree.sound w400 pick400 5 t566 _ (by decide +kernel)
theorem cov400_6 : PA.Covered 6 (OZ.Valid 6 w400.low w400.t w400.y w400.r w400.cap) (P33.root 6) :=
  Night6836Tree.sound w400 pick400 6 t567 _ (by decide +kernel)
theorem cov400_7 : PA.Covered 7 (OZ.Valid 7 w400.low w400.t w400.y w400.r w400.cap) (P33.root 7) :=
  Night6836Tree.sound w400 pick400 7 t568 _ (by decide +kernel)
theorem window400 : P33.WindowCount w400 := by
  apply P33.window_count w400 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov400_1
  · exact cov400_2
  · exact cov400_3
  · exact cov400_4
  · exact cov400_5
  · exact cov400_6
  · exact cov400_7
def w401 : P33.Window := ⟨7,29,7909,7873,236271024375073752,15507,15000,5000000,81920000000⟩
def h401_0 : Height w401 := ⟨15507,15000,by decide +kernel⟩
def h401_1 : Height w401 := ⟨19703,12000,by decide +kernel⟩
def h401_2 : Height w401 := ⟨27430,9000,by decide +kernel⟩
def pick401 (cl : ℕ) : Height w401 := if cl<4 then (h401_0) else (if cl<172 then (h401_1) else (h401_2))
private theorem k401_1_0 : check w401 pick401 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k401_1_1 : check w401 pick401 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k401_1_2 : check w401 pick401 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w401 pick401 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k401_1_0 k401_1_1
private theorem k401_1_3 : check w401 pick401 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k401_1_4 : check w401 pick401 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k401_1_5 : check w401 pick401 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w401 pick401 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k401_1_3 k401_1_4
private theorem k401_1_6 : check w401 pick401 1 t9546 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w401 pick401 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9537 k401_1_2 k401_1_5
private theorem k401_1_7 : check w401 pick401 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k401_1_8 : check w401 pick401 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k401_1_9 : check w401 pick401 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w401 pick401 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k401_1_7 k401_1_8
private theorem k401_1_10 : check w401 pick401 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k401_1_11 : check w401 pick401 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k401_1_12 : check w401 pick401 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w401 pick401 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k401_1_10 k401_1_11
private theorem k401_1_13 : check w401 pick401 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w401 pick401 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k401_1_9 k401_1_12
private theorem k401_1_14 : check w401 pick401 1 t9547 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w401 pick401 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9546 t3549 k401_1_6 k401_1_13
theorem cov401_1 : PA.Covered 1 (OZ.Valid 1 w401.low w401.t w401.y w401.r w401.cap) (P33.root 1) :=
  Night6836Tree.sound w401 pick401 1 t9547 _ k401_1_14
theorem cov401_2 : PA.Covered 2 (OZ.Valid 2 w401.low w401.t w401.y w401.r w401.cap) (P33.root 2) :=
  Night6836Tree.sound w401 pick401 2 t2745 _ (by decide +kernel)
theorem cov401_3 : PA.Covered 3 (OZ.Valid 3 w401.low w401.t w401.y w401.r w401.cap) (P33.root 3) :=
  Night6836Tree.sound w401 pick401 3 t564 _ (by decide +kernel)
theorem cov401_4 : PA.Covered 4 (OZ.Valid 4 w401.low w401.t w401.y w401.r w401.cap) (P33.root 4) :=
  Night6836Tree.sound w401 pick401 4 t565 _ (by decide +kernel)
theorem cov401_5 : PA.Covered 5 (OZ.Valid 5 w401.low w401.t w401.y w401.r w401.cap) (P33.root 5) :=
  Night6836Tree.sound w401 pick401 5 t566 _ (by decide +kernel)
theorem cov401_6 : PA.Covered 6 (OZ.Valid 6 w401.low w401.t w401.y w401.r w401.cap) (P33.root 6) :=
  Night6836Tree.sound w401 pick401 6 t567 _ (by decide +kernel)
theorem cov401_7 : PA.Covered 7 (OZ.Valid 7 w401.low w401.t w401.y w401.r w401.cap) (P33.root 7) :=
  Night6836Tree.sound w401 pick401 7 t568 _ (by decide +kernel)
theorem window401 : P33.WindowCount w401 := by
  apply P33.window_count w401 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov401_1
  · exact cov401_2
  · exact cov401_3
  · exact cov401_4
  · exact cov401_5
  · exact cov401_6
  · exact cov401_7
def w402 : P33.Window := ⟨7,30,6829,5830,194668599650684631,23700,19000,5000000,81920000000⟩
def h402_0 : Height w402 := ⟨23700,19000,by decide +kernel⟩
def h402_1 : Height w402 := ⟨30333,15000,by decide +kernel⟩
def h402_2 : Height w402 := ⟨44299,11000,by decide +kernel⟩
def pick402 (cl : ℕ) : Height w402 := if cl<13 then (h402_0) else (if cl<673 then (h402_1) else (h402_2))
private theorem k402_1_0 : check w402 pick402 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k402_1_1 : check w402 pick402 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k402_1_2 : check w402 pick402 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w402 pick402 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k402_1_0 k402_1_1
private theorem k402_1_3 : check w402 pick402 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k402_1_4 : check w402 pick402 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k402_1_5 : check w402 pick402 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w402 pick402 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k402_1_3 k402_1_4
private theorem k402_1_6 : check w402 pick402 1 t9548 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w402 pick402 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t9537 k402_1_2 k402_1_5
private theorem k402_1_7 : check w402 pick402 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k402_1_8 : check w402 pick402 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k402_1_9 : check w402 pick402 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w402 pick402 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k402_1_7 k402_1_8
private theorem k402_1_10 : check w402 pick402 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k402_1_11 : check w402 pick402 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k402_1_12 : check w402 pick402 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w402 pick402 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k402_1_10 k402_1_11
private theorem k402_1_13 : check w402 pick402 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w402 pick402 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k402_1_9 k402_1_12
private theorem k402_1_14 : check w402 pick402 1 t9549 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w402 pick402 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9548 t2461 k402_1_6 k402_1_13
theorem cov402_1 : PA.Covered 1 (OZ.Valid 1 w402.low w402.t w402.y w402.r w402.cap) (P33.root 1) :=
  Night6836Tree.sound w402 pick402 1 t9549 _ k402_1_14
private theorem k402_2_0 : check w402 pick402 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k402_2_1 : check w402 pick402 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k402_2_2 : check w402 pick402 2 t9544 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w402 pick402 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9135 k402_2_0 k402_2_1
theorem cov402_2 : PA.Covered 2 (OZ.Valid 2 w402.low w402.t w402.y w402.r w402.cap) (P33.root 2) :=
  Night6836Tree.sound w402 pick402 2 t9544 _ k402_2_2
theorem cov402_3 : PA.Covered 3 (OZ.Valid 3 w402.low w402.t w402.y w402.r w402.cap) (P33.root 3) :=
  Night6836Tree.sound w402 pick402 3 t564 _ (by decide +kernel)
theorem cov402_4 : PA.Covered 4 (OZ.Valid 4 w402.low w402.t w402.y w402.r w402.cap) (P33.root 4) :=
  Night6836Tree.sound w402 pick402 4 t565 _ (by decide +kernel)
theorem cov402_5 : PA.Covered 5 (OZ.Valid 5 w402.low w402.t w402.y w402.r w402.cap) (P33.root 5) :=
  Night6836Tree.sound w402 pick402 5 t566 _ (by decide +kernel)
theorem cov402_6 : PA.Covered 6 (OZ.Valid 6 w402.low w402.t w402.y w402.r w402.cap) (P33.root 6) :=
  Night6836Tree.sound w402 pick402 6 t567 _ (by decide +kernel)
theorem cov402_7 : PA.Covered 7 (OZ.Valid 7 w402.low w402.t w402.y w402.r w402.cap) (P33.root 7) :=
  Night6836Tree.sound w402 pick402 7 t568 _ (by decide +kernel)
theorem window402 : P33.WindowCount w402 := by
  apply P33.window_count w402 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov402_1
  · exact cov402_2
  · exact cov402_3
  · exact cov402_4
  · exact cov402_5
  · exact cov402_6
  · exact cov402_7
def w403 : P33.Window := ⟨7,30,7872,7837,240460493005901563,16564,15000,5000000,81920000000⟩
def h403_0 : Height w403 := ⟨16564,15000,by decide +kernel⟩
def h403_1 : Height w403 := ⟨20904,12000,by decide +kernel⟩
def h403_2 : Height w403 := ⟨28979,9000,by decide +kernel⟩
def pick403 (cl : ℕ) : Height w403 := if cl<5 then (h403_0) else (if cl<195 then (h403_1) else (h403_2))
private theorem k403_1_0 : check w403 pick403 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k403_1_1 : check w403 pick403 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k403_1_2 : check w403 pick403 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w403 pick403 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k403_1_0 k403_1_1
private theorem k403_1_3 : check w403 pick403 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k403_1_4 : check w403 pick403 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k403_1_5 : check w403 pick403 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w403 pick403 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k403_1_3 k403_1_4
private theorem k403_1_6 : check w403 pick403 1 t9546 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w403 pick403 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9537 k403_1_2 k403_1_5
private theorem k403_1_7 : check w403 pick403 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k403_1_8 : check w403 pick403 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k403_1_9 : check w403 pick403 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w403 pick403 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k403_1_7 k403_1_8
private theorem k403_1_10 : check w403 pick403 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k403_1_11 : check w403 pick403 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k403_1_12 : check w403 pick403 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w403 pick403 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k403_1_10 k403_1_11
private theorem k403_1_13 : check w403 pick403 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w403 pick403 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k403_1_9 k403_1_12
private theorem k403_1_14 : check w403 pick403 1 t9547 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w403 pick403 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9546 t3549 k403_1_6 k403_1_13
theorem cov403_1 : PA.Covered 1 (OZ.Valid 1 w403.low w403.t w403.y w403.r w403.cap) (P33.root 1) :=
  Night6836Tree.sound w403 pick403 1 t9547 _ k403_1_14
theorem cov403_2 : PA.Covered 2 (OZ.Valid 2 w403.low w403.t w403.y w403.r w403.cap) (P33.root 2) :=
  Night6836Tree.sound w403 pick403 2 t2745 _ (by decide +kernel)
theorem cov403_3 : PA.Covered 3 (OZ.Valid 3 w403.low w403.t w403.y w403.r w403.cap) (P33.root 3) :=
  Night6836Tree.sound w403 pick403 3 t564 _ (by decide +kernel)
theorem cov403_4 : PA.Covered 4 (OZ.Valid 4 w403.low w403.t w403.y w403.r w403.cap) (P33.root 4) :=
  Night6836Tree.sound w403 pick403 4 t565 _ (by decide +kernel)
theorem cov403_5 : PA.Covered 5 (OZ.Valid 5 w403.low w403.t w403.y w403.r w403.cap) (P33.root 5) :=
  Night6836Tree.sound w403 pick403 5 t566 _ (by decide +kernel)
theorem cov403_6 : PA.Covered 6 (OZ.Valid 6 w403.low w403.t w403.y w403.r w403.cap) (P33.root 6) :=
  Night6836Tree.sound w403 pick403 6 t567 _ (by decide +kernel)
theorem cov403_7 : PA.Covered 7 (OZ.Valid 7 w403.low w403.t w403.y w403.r w403.cap) (P33.root 7) :=
  Night6836Tree.sound w403 pick403 7 t568 _ (by decide +kernel)
theorem window403 : P33.WindowCount w403 := by
  apply P33.window_count w403 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov403_1
  · exact cov403_2
  · exact cov403_3
  · exact cov403_4
  · exact cov403_5
  · exact cov403_6
  · exact cov403_7
def w404 : P33.Window := ⟨7,31,7836,7800,228649120627285351,17640,15000,5000000,81920000000⟩
def h404_0 : Height w404 := ⟨17640,15000,by decide +kernel⟩
def h404_1 : Height w404 := ⟨22129,12000,by decide +kernel⟩
def h404_2 : Height w404 := ⟨30564,9000,by decide +kernel⟩
def pick404 (cl : ℕ) : Height w404 := if cl<5 then (h404_0) else (if cl<231 then (h404_1) else (h404_2))
private theorem k404_1_0 : check w404 pick404 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k404_1_1 : check w404 pick404 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k404_1_2 : check w404 pick404 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w404 pick404 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k404_1_0 k404_1_1
private theorem k404_1_3 : check w404 pick404 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k404_1_4 : check w404 pick404 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k404_1_5 : check w404 pick404 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w404 pick404 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k404_1_3 k404_1_4
private theorem k404_1_6 : check w404 pick404 1 t9546 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w404 pick404 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9537 k404_1_2 k404_1_5
private theorem k404_1_7 : check w404 pick404 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k404_1_8 : check w404 pick404 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k404_1_9 : check w404 pick404 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w404 pick404 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k404_1_7 k404_1_8
private theorem k404_1_10 : check w404 pick404 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k404_1_11 : check w404 pick404 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k404_1_12 : check w404 pick404 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w404 pick404 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k404_1_10 k404_1_11
private theorem k404_1_13 : check w404 pick404 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w404 pick404 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k404_1_9 k404_1_12
private theorem k404_1_14 : check w404 pick404 1 t9547 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w404 pick404 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9546 t3549 k404_1_6 k404_1_13
theorem cov404_1 : PA.Covered 1 (OZ.Valid 1 w404.low w404.t w404.y w404.r w404.cap) (P33.root 1) :=
  Night6836Tree.sound w404 pick404 1 t9547 _ k404_1_14
private theorem k404_2_0 : check w404 pick404 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k404_2_1 : check w404 pick404 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k404_2_2 : check w404 pick404 2 t9544 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w404 pick404 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9135 k404_2_0 k404_2_1
theorem cov404_2 : PA.Covered 2 (OZ.Valid 2 w404.low w404.t w404.y w404.r w404.cap) (P33.root 2) :=
  Night6836Tree.sound w404 pick404 2 t9544 _ k404_2_2
theorem cov404_3 : PA.Covered 3 (OZ.Valid 3 w404.low w404.t w404.y w404.r w404.cap) (P33.root 3) :=
  Night6836Tree.sound w404 pick404 3 t564 _ (by decide +kernel)
theorem cov404_4 : PA.Covered 4 (OZ.Valid 4 w404.low w404.t w404.y w404.r w404.cap) (P33.root 4) :=
  Night6836Tree.sound w404 pick404 4 t565 _ (by decide +kernel)
theorem cov404_5 : PA.Covered 5 (OZ.Valid 5 w404.low w404.t w404.y w404.r w404.cap) (P33.root 5) :=
  Night6836Tree.sound w404 pick404 5 t566 _ (by decide +kernel)
theorem cov404_6 : PA.Covered 6 (OZ.Valid 6 w404.low w404.t w404.y w404.r w404.cap) (P33.root 6) :=
  Night6836Tree.sound w404 pick404 6 t567 _ (by decide +kernel)
theorem cov404_7 : PA.Covered 7 (OZ.Valid 7 w404.low w404.t w404.y w404.r w404.cap) (P33.root 7) :=
  Night6836Tree.sound w404 pick404 7 t568 _ (by decide +kernel)
theorem window404 : P33.WindowCount w404 := by
  apply P33.window_count w404 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov404_1
  · exact cov404_2
  · exact cov404_3
  · exact cov404_4
  · exact cov404_5
  · exact cov404_6
  · exact cov404_7
def w405 : P33.Window := ⟨7,32,5831,4832,186090940948945331,31503,23000,5000000,81920000000⟩
def h405_0 : Height w405 := ⟨31503,23000,by decide +kernel⟩
def h405_1 : Height w405 := ⟨38072,19000,by decide +kernel⟩
def h405_2 : Height w405 := ⟨49304,15000,by decide +kernel⟩
def pick405 (cl : ℕ) : Height w405 := if cl<13 then (h405_0) else (if cl<231 then (h405_1) else (h405_2))
private theorem k405_1_0 : check w405 pick405 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k405_1_1 : check w405 pick405 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k405_1_2 : check w405 pick405 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w405 pick405 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k405_1_0 k405_1_1
private theorem k405_1_3 : check w405 pick405 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k405_1_4 : check w405 pick405 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k405_1_5 : check w405 pick405 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w405 pick405 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k405_1_3 k405_1_4
private theorem k405_1_6 : check w405 pick405 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w405 pick405 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k405_1_2 k405_1_5
private theorem k405_1_7 : check w405 pick405 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k405_1_8 : check w405 pick405 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k405_1_9 : check w405 pick405 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w405 pick405 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k405_1_7 k405_1_8
private theorem k405_1_10 : check w405 pick405 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k405_1_11 : check w405 pick405 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k405_1_12 : check w405 pick405 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w405 pick405 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k405_1_10 k405_1_11
private theorem k405_1_13 : check w405 pick405 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w405 pick405 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k405_1_9 k405_1_12
private theorem k405_1_14 : check w405 pick405 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w405 pick405 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k405_1_6 k405_1_13
theorem cov405_1 : PA.Covered 1 (OZ.Valid 1 w405.low w405.t w405.y w405.r w405.cap) (P33.root 1) :=
  Night6836Tree.sound w405 pick405 1 t9554 _ k405_1_14
theorem cov405_2 : PA.Covered 2 (OZ.Valid 2 w405.low w405.t w405.y w405.r w405.cap) (P33.root 2) :=
  Night6836Tree.sound w405 pick405 2 t4654 _ (by decide +kernel)
theorem cov405_3 : PA.Covered 3 (OZ.Valid 3 w405.low w405.t w405.y w405.r w405.cap) (P33.root 3) :=
  Night6836Tree.sound w405 pick405 3 t564 _ (by decide +kernel)
theorem cov405_4 : PA.Covered 4 (OZ.Valid 4 w405.low w405.t w405.y w405.r w405.cap) (P33.root 4) :=
  Night6836Tree.sound w405 pick405 4 t565 _ (by decide +kernel)
theorem cov405_5 : PA.Covered 5 (OZ.Valid 5 w405.low w405.t w405.y w405.r w405.cap) (P33.root 5) :=
  Night6836Tree.sound w405 pick405 5 t566 _ (by decide +kernel)
theorem cov405_6 : PA.Covered 6 (OZ.Valid 6 w405.low w405.t w405.y w405.r w405.cap) (P33.root 6) :=
  Night6836Tree.sound w405 pick405 6 t567 _ (by decide +kernel)
theorem cov405_7 : PA.Covered 7 (OZ.Valid 7 w405.low w405.t w405.y w405.r w405.cap) (P33.root 7) :=
  Night6836Tree.sound w405 pick405 7 t2134 _ (by decide +kernel)
theorem window405 : P33.WindowCount w405 := by
  apply P33.window_count w405 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov405_1
  · exact cov405_2
  · exact cov405_3
  · exact cov405_4
  · exact cov405_5
  · exact cov405_6
  · exact cov405_7
def w406 : P33.Window := ⟨7,32,7799,7569,232791041768046355,19701,15000,5000000,81920000000⟩
def h406_0 : Height w406 := ⟨19701,15000,by decide +kernel⟩
def h406_1 : Height w406 := ⟨24593,12000,by decide +kernel⟩
def h406_2 : Height w406 := ⟨34100,9000,by decide +kernel⟩
def pick406 (cl : ℕ) : Height w406 := if cl<13 then (h406_0) else (if cl<317 then (h406_1) else (h406_2))
private theorem k406_1_0 : check w406 pick406 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k406_1_1 : check w406 pick406 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k406_1_2 : check w406 pick406 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w406 pick406 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k406_1_0 k406_1_1
private theorem k406_1_3 : check w406 pick406 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k406_1_4 : check w406 pick406 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k406_1_5 : check w406 pick406 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w406 pick406 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k406_1_3 k406_1_4
private theorem k406_1_6 : check w406 pick406 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w406 pick406 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k406_1_2 k406_1_5
private theorem k406_1_7 : check w406 pick406 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k406_1_8 : check w406 pick406 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k406_1_9 : check w406 pick406 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w406 pick406 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k406_1_7 k406_1_8
private theorem k406_1_10 : check w406 pick406 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k406_1_11 : check w406 pick406 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k406_1_12 : check w406 pick406 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w406 pick406 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k406_1_10 k406_1_11
private theorem k406_1_13 : check w406 pick406 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w406 pick406 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k406_1_9 k406_1_12
private theorem k406_1_14 : check w406 pick406 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w406 pick406 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k406_1_6 k406_1_13
theorem cov406_1 : PA.Covered 1 (OZ.Valid 1 w406.low w406.t w406.y w406.r w406.cap) (P33.root 1) :=
  Night6836Tree.sound w406 pick406 1 t9554 _ k406_1_14
private theorem k406_2_0 : check w406 pick406 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k406_2_1 : check w406 pick406 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k406_2_2 : check w406 pick406 2 t9544 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w406 pick406 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9135 k406_2_0 k406_2_1
theorem cov406_2 : PA.Covered 2 (OZ.Valid 2 w406.low w406.t w406.y w406.r w406.cap) (P33.root 2) :=
  Night6836Tree.sound w406 pick406 2 t9544 _ k406_2_2
theorem cov406_3 : PA.Covered 3 (OZ.Valid 3 w406.low w406.t w406.y w406.r w406.cap) (P33.root 3) :=
  Night6836Tree.sound w406 pick406 3 t564 _ (by decide +kernel)
theorem cov406_4 : PA.Covered 4 (OZ.Valid 4 w406.low w406.t w406.y w406.r w406.cap) (P33.root 4) :=
  Night6836Tree.sound w406 pick406 4 t565 _ (by decide +kernel)
theorem cov406_5 : PA.Covered 5 (OZ.Valid 5 w406.low w406.t w406.y w406.r w406.cap) (P33.root 5) :=
  Night6836Tree.sound w406 pick406 5 t566 _ (by decide +kernel)
theorem cov406_6 : PA.Covered 6 (OZ.Valid 6 w406.low w406.t w406.y w406.r w406.cap) (P33.root 6) :=
  Night6836Tree.sound w406 pick406 6 t567 _ (by decide +kernel)
theorem cov406_7 : PA.Covered 7 (OZ.Valid 7 w406.low w406.t w406.y w406.r w406.cap) (P33.root 7) :=
  Night6836Tree.sound w406 pick406 7 t568 _ (by decide +kernel)
theorem window406 : P33.WindowCount w406 := by
  apply P33.window_count w406 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov406_1
  · exact cov406_2
  · exact cov406_3
  · exact cov406_4
  · exact cov406_5
  · exact cov406_6
  · exact cov406_7
def w407 : P33.Window := ⟨7,33,5732,4733,186792783386108064,34377,23000,5000000,81920000000⟩
def h407_0 : Height w407 := ⟨34377,23000,by decide +kernel⟩
def h407_1 : Height w407 := ⟨41414,19000,by decide +kernel⟩
def h407_2 : Height w407 := ⟨53687,15000,by decide +kernel⟩
def pick407 (cl : ℕ) : Height w407 := if cl<32 then (h407_0) else (if cl<302 then (h407_1) else (h407_2))
private theorem k407_1_0 : check w407 pick407 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k407_1_1 : check w407 pick407 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k407_1_2 : check w407 pick407 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w407 pick407 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k407_1_0 k407_1_1
private theorem k407_1_3 : check w407 pick407 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k407_1_4 : check w407 pick407 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k407_1_5 : check w407 pick407 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w407 pick407 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k407_1_3 k407_1_4
private theorem k407_1_6 : check w407 pick407 1 t9546 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w407 pick407 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9537 k407_1_2 k407_1_5
private theorem k407_1_7 : check w407 pick407 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k407_1_8 : check w407 pick407 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k407_1_9 : check w407 pick407 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w407 pick407 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k407_1_7 k407_1_8
private theorem k407_1_10 : check w407 pick407 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k407_1_11 : check w407 pick407 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k407_1_12 : check w407 pick407 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w407 pick407 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k407_1_10 k407_1_11
private theorem k407_1_13 : check w407 pick407 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w407 pick407 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k407_1_9 k407_1_12
private theorem k407_1_14 : check w407 pick407 1 t9547 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w407 pick407 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9546 t3549 k407_1_6 k407_1_13
theorem cov407_1 : PA.Covered 1 (OZ.Valid 1 w407.low w407.t w407.y w407.r w407.cap) (P33.root 1) :=
  Night6836Tree.sound w407 pick407 1 t9547 _ k407_1_14
theorem cov407_2 : PA.Covered 2 (OZ.Valid 2 w407.low w407.t w407.y w407.r w407.cap) (P33.root 2) :=
  Night6836Tree.sound w407 pick407 2 t4654 _ (by decide +kernel)
theorem cov407_3 : PA.Covered 3 (OZ.Valid 3 w407.low w407.t w407.y w407.r w407.cap) (P33.root 3) :=
  Night6836Tree.sound w407 pick407 3 t564 _ (by decide +kernel)
theorem cov407_4 : PA.Covered 4 (OZ.Valid 4 w407.low w407.t w407.y w407.r w407.cap) (P33.root 4) :=
  Night6836Tree.sound w407 pick407 4 t565 _ (by decide +kernel)
theorem cov407_5 : PA.Covered 5 (OZ.Valid 5 w407.low w407.t w407.y w407.r w407.cap) (P33.root 5) :=
  Night6836Tree.sound w407 pick407 5 t566 _ (by decide +kernel)
theorem cov407_6 : PA.Covered 6 (OZ.Valid 6 w407.low w407.t w407.y w407.r w407.cap) (P33.root 6) :=
  Night6836Tree.sound w407 pick407 6 t567 _ (by decide +kernel)
theorem cov407_7 : PA.Covered 7 (OZ.Valid 7 w407.low w407.t w407.y w407.r w407.cap) (P33.root 7) :=
  Night6836Tree.sound w407 pick407 7 t2134 _ (by decide +kernel)
theorem window407 : P33.WindowCount w407 := by
  apply P33.window_count w407 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov407_1
  · exact cov407_2
  · exact cov407_3
  · exact cov407_4
  · exact cov407_5
  · exact cov407_6
  · exact cov407_7
def w408 : P33.Window := ⟨7,33,7761,7725,236852018793793170,19841,15000,5000000,81920000000⟩
def h408_0 : Height w408 := ⟨19841,15000,by decide +kernel⟩
def h408_1 : Height w408 := ⟨24640,12000,by decide +kernel⟩
def h408_2 : Height w408 := ⟨33835,9000,by decide +kernel⟩
def pick408 (cl : ℕ) : Height w408 := if cl<10 then (h408_0) else (if cl<302 then (h408_1) else (h408_2))
private theorem k408_1_0 : check w408 pick408 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k408_1_1 : check w408 pick408 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k408_1_2 : check w408 pick408 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w408 pick408 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k408_1_0 k408_1_1
private theorem k408_1_3 : check w408 pick408 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k408_1_4 : check w408 pick408 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k408_1_5 : check w408 pick408 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w408 pick408 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k408_1_3 k408_1_4
private theorem k408_1_6 : check w408 pick408 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w408 pick408 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k408_1_2 k408_1_5
private theorem k408_1_7 : check w408 pick408 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k408_1_8 : check w408 pick408 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k408_1_9 : check w408 pick408 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w408 pick408 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k408_1_7 k408_1_8
private theorem k408_1_10 : check w408 pick408 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k408_1_11 : check w408 pick408 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k408_1_12 : check w408 pick408 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w408 pick408 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k408_1_10 k408_1_11
private theorem k408_1_13 : check w408 pick408 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w408 pick408 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k408_1_9 k408_1_12
private theorem k408_1_14 : check w408 pick408 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w408 pick408 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k408_1_6 k408_1_13
theorem cov408_1 : PA.Covered 1 (OZ.Valid 1 w408.low w408.t w408.y w408.r w408.cap) (P33.root 1) :=
  Night6836Tree.sound w408 pick408 1 t9554 _ k408_1_14
private theorem k408_2_0 : check w408 pick408 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k408_2_1 : check w408 pick408 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k408_2_2 : check w408 pick408 2 t9544 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w408 pick408 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9135 k408_2_0 k408_2_1
theorem cov408_2 : PA.Covered 2 (OZ.Valid 2 w408.low w408.t w408.y w408.r w408.cap) (P33.root 2) :=
  Night6836Tree.sound w408 pick408 2 t9544 _ k408_2_2
theorem cov408_3 : PA.Covered 3 (OZ.Valid 3 w408.low w408.t w408.y w408.r w408.cap) (P33.root 3) :=
  Night6836Tree.sound w408 pick408 3 t564 _ (by decide +kernel)
theorem cov408_4 : PA.Covered 4 (OZ.Valid 4 w408.low w408.t w408.y w408.r w408.cap) (P33.root 4) :=
  Night6836Tree.sound w408 pick408 4 t565 _ (by decide +kernel)
theorem cov408_5 : PA.Covered 5 (OZ.Valid 5 w408.low w408.t w408.y w408.r w408.cap) (P33.root 5) :=
  Night6836Tree.sound w408 pick408 5 t566 _ (by decide +kernel)
theorem cov408_6 : PA.Covered 6 (OZ.Valid 6 w408.low w408.t w408.y w408.r w408.cap) (P33.root 6) :=
  Night6836Tree.sound w408 pick408 6 t567 _ (by decide +kernel)
theorem cov408_7 : PA.Covered 7 (OZ.Valid 7 w408.low w408.t w408.y w408.r w408.cap) (P33.root 7) :=
  Night6836Tree.sound w408 pick408 7 t568 _ (by decide +kernel)
theorem window408 : P33.WindowCount w408 := by
  apply P33.window_count w408 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov408_1
  · exact cov408_2
  · exact cov408_3
  · exact cov408_4
  · exact cov408_5
  · exact cov408_6
  · exact cov408_7
def w409 : P33.Window := ⟨7,34,5733,4734,190677672092927591,35914,23000,5000000,81920000000⟩
def h409_0 : Height w409 := ⟨35914,23000,by decide +kernel⟩
def h409_1 : Height w409 := ⟨43116,19000,by decide +kernel⟩
def h409_2 : Height w409 := ⟨55723,15000,by decide +kernel⟩
def pick409 (cl : ℕ) : Height w409 := if cl<32 then (h409_0) else (if cl<312 then (h409_1) else (h409_2))
private theorem k409_1_0 : check w409 pick409 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k409_1_1 : check w409 pick409 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k409_1_2 : check w409 pick409 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w409 pick409 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k409_1_0 k409_1_1
private theorem k409_1_3 : check w409 pick409 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k409_1_4 : check w409 pick409 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k409_1_5 : check w409 pick409 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w409 pick409 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k409_1_3 k409_1_4
private theorem k409_1_6 : check w409 pick409 1 t9546 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w409 pick409 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9537 k409_1_2 k409_1_5
private theorem k409_1_7 : check w409 pick409 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k409_1_8 : check w409 pick409 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k409_1_9 : check w409 pick409 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w409 pick409 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k409_1_7 k409_1_8
private theorem k409_1_10 : check w409 pick409 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k409_1_11 : check w409 pick409 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k409_1_12 : check w409 pick409 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w409 pick409 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k409_1_10 k409_1_11
private theorem k409_1_13 : check w409 pick409 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w409 pick409 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k409_1_9 k409_1_12
private theorem k409_1_14 : check w409 pick409 1 t9547 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w409 pick409 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9546 t3549 k409_1_6 k409_1_13
theorem cov409_1 : PA.Covered 1 (OZ.Valid 1 w409.low w409.t w409.y w409.r w409.cap) (P33.root 1) :=
  Night6836Tree.sound w409 pick409 1 t9547 _ k409_1_14
theorem cov409_2 : PA.Covered 2 (OZ.Valid 2 w409.low w409.t w409.y w409.r w409.cap) (P33.root 2) :=
  Night6836Tree.sound w409 pick409 2 t4654 _ (by decide +kernel)
theorem cov409_3 : PA.Covered 3 (OZ.Valid 3 w409.low w409.t w409.y w409.r w409.cap) (P33.root 3) :=
  Night6836Tree.sound w409 pick409 3 t564 _ (by decide +kernel)
theorem cov409_4 : PA.Covered 4 (OZ.Valid 4 w409.low w409.t w409.y w409.r w409.cap) (P33.root 4) :=
  Night6836Tree.sound w409 pick409 4 t565 _ (by decide +kernel)
theorem cov409_5 : PA.Covered 5 (OZ.Valid 5 w409.low w409.t w409.y w409.r w409.cap) (P33.root 5) :=
  Night6836Tree.sound w409 pick409 5 t566 _ (by decide +kernel)
theorem cov409_6 : PA.Covered 6 (OZ.Valid 6 w409.low w409.t w409.y w409.r w409.cap) (P33.root 6) :=
  Night6836Tree.sound w409 pick409 6 t567 _ (by decide +kernel)
theorem cov409_7 : PA.Covered 7 (OZ.Valid 7 w409.low w409.t w409.y w409.r w409.cap) (P33.root 7) :=
  Night6836Tree.sound w409 pick409 7 t2134 _ (by decide +kernel)
theorem window409 : P33.WindowCount w409 := by
  apply P33.window_count w409 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov409_1
  · exact cov409_2
  · exact cov409_3
  · exact cov409_4
  · exact cov409_5
  · exact cov409_6
  · exact cov409_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w410 : P33.Window := ⟨7,34,7724,7609,240892476933141615,21387,15000,5000000,81920000000⟩
def h410_0 : Height w410 := ⟨21387,15000,by decide +kernel⟩
def h410_1 : Height w410 := ⟨26457,12000,by decide +kernel⟩
def h410_2 : Height w410 := ⟨36356,9000,by decide +kernel⟩
def pick410 (cl : ℕ) : Height w410 := if cl<18 then (h410_0) else (if cl<465 then (h410_1) else (h410_2))
private theorem k410_1_0 : check w410 pick410 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k410_1_1 : check w410 pick410 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k410_1_2 : check w410 pick410 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w410 pick410 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k410_1_0 k410_1_1
private theorem k410_1_3 : check w410 pick410 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k410_1_4 : check w410 pick410 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k410_1_5 : check w410 pick410 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w410 pick410 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k410_1_3 k410_1_4
private theorem k410_1_6 : check w410 pick410 1 t9548 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w410 pick410 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t9537 k410_1_2 k410_1_5
private theorem k410_1_7 : check w410 pick410 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k410_1_8 : check w410 pick410 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k410_1_9 : check w410 pick410 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w410 pick410 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k410_1_7 k410_1_8
private theorem k410_1_10 : check w410 pick410 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k410_1_11 : check w410 pick410 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k410_1_12 : check w410 pick410 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w410 pick410 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k410_1_10 k410_1_11
private theorem k410_1_13 : check w410 pick410 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w410 pick410 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k410_1_9 k410_1_12
private theorem k410_1_14 : check w410 pick410 1 t9555 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w410 pick410 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9548 t9097 k410_1_6 k410_1_13
theorem cov410_1 : PA.Covered 1 (OZ.Valid 1 w410.low w410.t w410.y w410.r w410.cap) (P33.root 1) :=
  Night6836Tree.sound w410 pick410 1 t9555 _ k410_1_14
private theorem k410_2_0 : check w410 pick410 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k410_2_1 : check w410 pick410 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k410_2_2 : check w410 pick410 2 t9556 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w410 pick410 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9133 k410_2_0 k410_2_1
theorem cov410_2 : PA.Covered 2 (OZ.Valid 2 w410.low w410.t w410.y w410.r w410.cap) (P33.root 2) :=
  Night6836Tree.sound w410 pick410 2 t9556 _ k410_2_2
theorem cov410_3 : PA.Covered 3 (OZ.Valid 3 w410.low w410.t w410.y w410.r w410.cap) (P33.root 3) :=
  Night6836Tree.sound w410 pick410 3 t564 _ (by decide +kernel)
theorem cov410_4 : PA.Covered 4 (OZ.Valid 4 w410.low w410.t w410.y w410.r w410.cap) (P33.root 4) :=
  Night6836Tree.sound w410 pick410 4 t565 _ (by decide +kernel)
theorem cov410_5 : PA.Covered 5 (OZ.Valid 5 w410.low w410.t w410.y w410.r w410.cap) (P33.root 5) :=
  Night6836Tree.sound w410 pick410 5 t566 _ (by decide +kernel)
theorem cov410_6 : PA.Covered 6 (OZ.Valid 6 w410.low w410.t w410.y w410.r w410.cap) (P33.root 6) :=
  Night6836Tree.sound w410 pick410 6 t567 _ (by decide +kernel)
theorem cov410_7 : PA.Covered 7 (OZ.Valid 7 w410.low w410.t w410.y w410.r w410.cap) (P33.root 7) :=
  Night6836Tree.sound w410 pick410 7 t568 _ (by decide +kernel)
theorem window410 : P33.WindowCount w410 := by
  apply P33.window_count w410 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov410_1
  · exact cov410_2
  · exact cov410_3
  · exact cov410_4
  · exact cov410_5
  · exact cov410_6
  · exact cov410_7
def w411 : P33.Window := ⟨7,35,7686,7648,241598285567121033,22114,15000,5000000,81920000000⟩
def h411_0 : Height w411 := ⟨22114,15000,by decide +kernel⟩
def h411_1 : Height w411 := ⟨27244,12000,by decide +kernel⟩
def h411_2 : Height w411 := ⟨37256,9000,by decide +kernel⟩
def pick411 (cl : ℕ) : Height w411 := if cl<18 then (h411_0) else (if cl<493 then (h411_1) else (h411_2))
private theorem k411_1_0 : check w411 pick411 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k411_1_1 : check w411 pick411 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k411_1_2 : check w411 pick411 1 t2653 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w411 pick411 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t2652 k411_1_0 k411_1_1
private theorem k411_1_3 : check w411 pick411 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k411_1_4 : check w411 pick411 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k411_1_5 : check w411 pick411 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w411 pick411 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k411_1_3 k411_1_4
private theorem k411_1_6 : check w411 pick411 1 t9548 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w411 pick411 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2653 t9537 k411_1_2 k411_1_5
private theorem k411_1_7 : check w411 pick411 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k411_1_8 : check w411 pick411 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k411_1_9 : check w411 pick411 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w411 pick411 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k411_1_7 k411_1_8
private theorem k411_1_10 : check w411 pick411 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k411_1_11 : check w411 pick411 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k411_1_12 : check w411 pick411 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w411 pick411 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k411_1_10 k411_1_11
private theorem k411_1_13 : check w411 pick411 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w411 pick411 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k411_1_9 k411_1_12
private theorem k411_1_14 : check w411 pick411 1 t9555 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w411 pick411 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9548 t9097 k411_1_6 k411_1_13
theorem cov411_1 : PA.Covered 1 (OZ.Valid 1 w411.low w411.t w411.y w411.r w411.cap) (P33.root 1) :=
  Night6836Tree.sound w411 pick411 1 t9555 _ k411_1_14
private theorem k411_2_0 : check w411 pick411 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k411_2_1 : check w411 pick411 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k411_2_2 : check w411 pick411 2 t9557 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w411 pick411 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t9133 k411_2_0 k411_2_1
theorem cov411_2 : PA.Covered 2 (OZ.Valid 2 w411.low w411.t w411.y w411.r w411.cap) (P33.root 2) :=
  Night6836Tree.sound w411 pick411 2 t9557 _ k411_2_2
theorem cov411_3 : PA.Covered 3 (OZ.Valid 3 w411.low w411.t w411.y w411.r w411.cap) (P33.root 3) :=
  Night6836Tree.sound w411 pick411 3 t564 _ (by decide +kernel)
theorem cov411_4 : PA.Covered 4 (OZ.Valid 4 w411.low w411.t w411.y w411.r w411.cap) (P33.root 4) :=
  Night6836Tree.sound w411 pick411 4 t565 _ (by decide +kernel)
theorem cov411_5 : PA.Covered 5 (OZ.Valid 5 w411.low w411.t w411.y w411.r w411.cap) (P33.root 5) :=
  Night6836Tree.sound w411 pick411 5 t566 _ (by decide +kernel)
theorem cov411_6 : PA.Covered 6 (OZ.Valid 6 w411.low w411.t w411.y w411.r w411.cap) (P33.root 6) :=
  Night6836Tree.sound w411 pick411 6 t567 _ (by decide +kernel)
theorem cov411_7 : PA.Covered 7 (OZ.Valid 7 w411.low w411.t w411.y w411.r w411.cap) (P33.root 7) :=
  Night6836Tree.sound w411 pick411 7 t568 _ (by decide +kernel)
theorem window411 : P33.WindowCount w411 := by
  apply P33.window_count w411 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov411_1
  · exact cov411_2
  · exact cov411_3
  · exact cov411_4
  · exact cov411_5
  · exact cov411_6
  · exact cov411_7
def w412 : P33.Window := ⟨7,36,7647,7609,244498779767577085,23279,15000,5000000,81920000000⟩
def h412_0 : Height w412 := ⟨23279,15000,by decide +kernel⟩
def h412_1 : Height w412 := ⟨28581,12000,by decide +kernel⟩
def h412_2 : Height w412 := ⟨39023,9000,by decide +kernel⟩
def pick412 (cl : ℕ) : Height w412 := if cl<32 then (h412_0) else (if cl<673 then (h412_1) else (h412_2))
private theorem k412_1_0 : check w412 pick412 1 t9558 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k412_1_1 : check w412 pick412 1 t9560 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k412_1_2 : check w412 pick412 1 t9561 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w412 pick412 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9558 t9560 k412_1_0 k412_1_1
private theorem k412_1_3 : check w412 pick412 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k412_1_4 : check w412 pick412 1 t9536 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k412_1_5 : check w412 pick412 1 t9537 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w412 pick412 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9536 k412_1_3 k412_1_4
private theorem k412_1_6 : check w412 pick412 1 t9562 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w412 pick412 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9561 t9537 k412_1_2 k412_1_5
private theorem k412_1_7 : check w412 pick412 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k412_1_8 : check w412 pick412 1 t6211 ⟨1,7,2,16,1,52,173,206⟩ = true := by decide +kernel
private theorem k412_1_9 : check w412 pick412 1 t6212 ⟨1,7,2,16,1,52,139,206⟩ = true := glue w412 pick412 1 ⟨1,7,2,16,1,52,139,206⟩ 3 172 t2459 t6211 k412_1_7 k412_1_8
private theorem k412_1_10 : check w412 pick412 1 t9148 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k412_1_11 : check w412 pick412 1 t5180 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k412_1_12 : check w412 pick412 1 t9563 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w412 pick412 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t9148 t5180 k412_1_10 k412_1_11
private theorem k412_1_13 : check w412 pick412 1 t9564 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w412 pick412 1 ⟨1,7,2,16,1,52,139,450⟩ 3 206 t6212 t9563 k412_1_9 k412_1_12
private theorem k412_1_14 : check w412 pick412 1 t9565 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w412 pick412 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9562 t9564 k412_1_6 k412_1_13
theorem cov412_1 : PA.Covered 1 (OZ.Valid 1 w412.low w412.t w412.y w412.r w412.cap) (P33.root 1) :=
  Night6836Tree.sound w412 pick412 1 t9565 _ k412_1_14
private theorem k412_2_0 : check w412 pick412 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k412_2_1 : check w412 pick412 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k412_2_2 : check w412 pick412 2 t9566 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w412 pick412 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t9135 k412_2_0 k412_2_1
theorem cov412_2 : PA.Covered 2 (OZ.Valid 2 w412.low w412.t w412.y w412.r w412.cap) (P33.root 2) :=
  Night6836Tree.sound w412 pick412 2 t9566 _ k412_2_2
theorem cov412_3 : PA.Covered 3 (OZ.Valid 3 w412.low w412.t w412.y w412.r w412.cap) (P33.root 3) :=
  Night6836Tree.sound w412 pick412 3 t564 _ (by decide +kernel)
theorem cov412_4 : PA.Covered 4 (OZ.Valid 4 w412.low w412.t w412.y w412.r w412.cap) (P33.root 4) :=
  Night6836Tree.sound w412 pick412 4 t565 _ (by decide +kernel)
theorem cov412_5 : PA.Covered 5 (OZ.Valid 5 w412.low w412.t w412.y w412.r w412.cap) (P33.root 5) :=
  Night6836Tree.sound w412 pick412 5 t566 _ (by decide +kernel)
theorem cov412_6 : PA.Covered 6 (OZ.Valid 6 w412.low w412.t w412.y w412.r w412.cap) (P33.root 6) :=
  Night6836Tree.sound w412 pick412 6 t567 _ (by decide +kernel)
theorem cov412_7 : PA.Covered 7 (OZ.Valid 7 w412.low w412.t w412.y w412.r w412.cap) (P33.root 7) :=
  Night6836Tree.sound w412 pick412 7 t568 _ (by decide +kernel)
theorem window412 : P33.WindowCount w412 := by
  apply P33.window_count w412 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov412_1
  · exact cov412_2
  · exact cov412_3
  · exact cov412_4
  · exact cov412_5
  · exact cov412_6
  · exact cov412_7
def w413 : P33.Window := ⟨7,37,5136,4137,181226302205112959,40126,31000,5000000,81920000000⟩
def h413_0 : Height w413 := ⟨40126,31000,by decide +kernel⟩
def h413_1 : Height w413 := ⟨45371,27000,by decide +kernel⟩
def h413_2 : Height w413 := ⟨52388,23000,by decide +kernel⟩
def h413_3 : Height w413 := ⟨63169,19000,by decide +kernel⟩
def pick413 (cl : ℕ) : Height w413 := if cl<32 then (if cl<2 then (h413_0) else (h413_1)) else (if cl<196 then (h413_2) else (h413_3))
private theorem k413_1_0 : check w413 pick413 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k413_1_1 : check w413 pick413 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k413_1_2 : check w413 pick413 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w413 pick413 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k413_1_0 k413_1_1
private theorem k413_1_3 : check w413 pick413 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k413_1_4 : check w413 pick413 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k413_1_5 : check w413 pick413 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w413 pick413 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k413_1_3 k413_1_4
private theorem k413_1_6 : check w413 pick413 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w413 pick413 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k413_1_2 k413_1_5
private theorem k413_1_7 : check w413 pick413 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k413_1_8 : check w413 pick413 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k413_1_9 : check w413 pick413 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w413 pick413 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k413_1_7 k413_1_8
private theorem k413_1_10 : check w413 pick413 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k413_1_11 : check w413 pick413 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k413_1_12 : check w413 pick413 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w413 pick413 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k413_1_10 k413_1_11
private theorem k413_1_13 : check w413 pick413 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w413 pick413 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k413_1_9 k413_1_12
private theorem k413_1_14 : check w413 pick413 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w413 pick413 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k413_1_6 k413_1_13
theorem cov413_1 : PA.Covered 1 (OZ.Valid 1 w413.low w413.t w413.y w413.r w413.cap) (P33.root 1) :=
  Night6836Tree.sound w413 pick413 1 t9554 _ k413_1_14
theorem cov413_2 : PA.Covered 2 (OZ.Valid 2 w413.low w413.t w413.y w413.r w413.cap) (P33.root 2) :=
  Night6836Tree.sound w413 pick413 2 t4654 _ (by decide +kernel)
theorem cov413_3 : PA.Covered 3 (OZ.Valid 3 w413.low w413.t w413.y w413.r w413.cap) (P33.root 3) :=
  Night6836Tree.sound w413 pick413 3 t564 _ (by decide +kernel)
theorem cov413_4 : PA.Covered 4 (OZ.Valid 4 w413.low w413.t w413.y w413.r w413.cap) (P33.root 4) :=
  Night6836Tree.sound w413 pick413 4 t565 _ (by decide +kernel)
theorem cov413_5 : PA.Covered 5 (OZ.Valid 5 w413.low w413.t w413.y w413.r w413.cap) (P33.root 5) :=
  Night6836Tree.sound w413 pick413 5 t566 _ (by decide +kernel)
theorem cov413_6 : PA.Covered 6 (OZ.Valid 6 w413.low w413.t w413.y w413.r w413.cap) (P33.root 6) :=
  Night6836Tree.sound w413 pick413 6 t567 _ (by decide +kernel)
theorem cov413_7 : PA.Covered 7 (OZ.Valid 7 w413.low w413.t w413.y w413.r w413.cap) (P33.root 7) :=
  Night6836Tree.sound w413 pick413 7 t2134 _ (by decide +kernel)
theorem window413 : P33.WindowCount w413 := by
  apply P33.window_count w413 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov413_1
  · exact cov413_2
  · exact cov413_3
  · exact cov413_4
  · exact cov413_5
  · exact cov413_6
  · exact cov413_7
def w414 : P33.Window := ⟨7,37,7608,7569,244215434372193108,24466,15000,5000000,81920000000⟩
def h414_0 : Height w414 := ⟨24466,15000,by decide +kernel⟩
def h414_1 : Height w414 := ⟨29948,12000,by decide +kernel⟩
def h414_2 : Height w414 := ⟨40840,9000,by decide +kernel⟩
def pick414 (cl : ℕ) : Height w414 := if cl<32 then (h414_0) else (if cl<922 then (h414_1) else (h414_2))
private theorem k414_1_0 : check w414 pick414 1 t9154 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k414_1_1 : check w414 pick414 1 t9568 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k414_1_2 : check w414 pick414 1 t9569 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w414 pick414 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t9154 t9568 k414_1_0 k414_1_1
private theorem k414_1_3 : check w414 pick414 1 t9573 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k414_1_4 : check w414 pick414 1 t9574 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w414 pick414 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9569 t9573 k414_1_2 k414_1_3
private theorem k414_1_5 : check w414 pick414 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k414_1_6 : check w414 pick414 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k414_1_7 : check w414 pick414 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w414 pick414 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k414_1_5 k414_1_6
private theorem k414_1_8 : check w414 pick414 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k414_1_9 : check w414 pick414 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k414_1_10 : check w414 pick414 1 t9575 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w414 pick414 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t3708 k414_1_8 k414_1_9
private theorem k414_1_11 : check w414 pick414 1 t9576 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w414 pick414 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9575 k414_1_7 k414_1_10
private theorem k414_1_12 : check w414 pick414 1 t9577 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w414 pick414 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9574 t9576 k414_1_4 k414_1_11
theorem cov414_1 : PA.Covered 1 (OZ.Valid 1 w414.low w414.t w414.y w414.r w414.cap) (P33.root 1) :=
  Night6836Tree.sound w414 pick414 1 t9577 _ k414_1_12
private theorem k414_2_0 : check w414 pick414 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k414_2_1 : check w414 pick414 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k414_2_2 : check w414 pick414 2 t9566 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w414 pick414 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t9135 k414_2_0 k414_2_1
theorem cov414_2 : PA.Covered 2 (OZ.Valid 2 w414.low w414.t w414.y w414.r w414.cap) (P33.root 2) :=
  Night6836Tree.sound w414 pick414 2 t9566 _ k414_2_2
theorem cov414_3 : PA.Covered 3 (OZ.Valid 3 w414.low w414.t w414.y w414.r w414.cap) (P33.root 3) :=
  Night6836Tree.sound w414 pick414 3 t564 _ (by decide +kernel)
theorem cov414_4 : PA.Covered 4 (OZ.Valid 4 w414.low w414.t w414.y w414.r w414.cap) (P33.root 4) :=
  Night6836Tree.sound w414 pick414 4 t565 _ (by decide +kernel)
theorem cov414_5 : PA.Covered 5 (OZ.Valid 5 w414.low w414.t w414.y w414.r w414.cap) (P33.root 5) :=
  Night6836Tree.sound w414 pick414 5 t566 _ (by decide +kernel)
theorem cov414_6 : PA.Covered 6 (OZ.Valid 6 w414.low w414.t w414.y w414.r w414.cap) (P33.root 6) :=
  Night6836Tree.sound w414 pick414 6 t567 _ (by decide +kernel)
theorem cov414_7 : PA.Covered 7 (OZ.Valid 7 w414.low w414.t w414.y w414.r w414.cap) (P33.root 7) :=
  Night6836Tree.sound w414 pick414 7 t568 _ (by decide +kernel)
theorem window414 : P33.WindowCount w414 := by
  apply P33.window_count w414 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov414_1
  · exact cov414_2
  · exact cov414_3
  · exact cov414_4
  · exact cov414_5
  · exact cov414_6
  · exact cov414_7
def w415 : P33.Window := ⟨7,38,7568,7529,243356761287349841,25672,15000,5000000,81920000000⟩
def h415_0 : Height w415 := ⟨25672,15000,by decide +kernel⟩
def h415_1 : Height w415 := ⟨31338,12000,by decide +kernel⟩
def h415_2 : Height w415 := ⟨42695,9000,by decide +kernel⟩
def pick415 (cl : ℕ) : Height w415 := if cl<32 then (h415_0) else (if cl<922 then (h415_1) else (h415_2))
private theorem k415_1_0 : check w415 pick415 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k415_1_1 : check w415 pick415 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k415_1_2 : check w415 pick415 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w415 pick415 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k415_1_0 k415_1_1
private theorem k415_1_3 : check w415 pick415 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k415_1_4 : check w415 pick415 1 t9579 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k415_1_5 : check w415 pick415 1 t9580 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w415 pick415 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9579 k415_1_3 k415_1_4
private theorem k415_1_6 : check w415 pick415 1 t9581 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w415 pick415 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9580 k415_1_2 k415_1_5
private theorem k415_1_7 : check w415 pick415 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k415_1_8 : check w415 pick415 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k415_1_9 : check w415 pick415 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w415 pick415 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k415_1_7 k415_1_8
private theorem k415_1_10 : check w415 pick415 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k415_1_11 : check w415 pick415 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k415_1_12 : check w415 pick415 1 t9575 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w415 pick415 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t3708 k415_1_10 k415_1_11
private theorem k415_1_13 : check w415 pick415 1 t9576 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w415 pick415 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9575 k415_1_9 k415_1_12
private theorem k415_1_14 : check w415 pick415 1 t9582 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w415 pick415 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9581 t9576 k415_1_6 k415_1_13
theorem cov415_1 : PA.Covered 1 (OZ.Valid 1 w415.low w415.t w415.y w415.r w415.cap) (P33.root 1) :=
  Night6836Tree.sound w415 pick415 1 t9582 _ k415_1_14
private theorem k415_2_0 : check w415 pick415 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k415_2_1 : check w415 pick415 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k415_2_2 : check w415 pick415 2 t9566 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w415 pick415 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t9135 k415_2_0 k415_2_1
theorem cov415_2 : PA.Covered 2 (OZ.Valid 2 w415.low w415.t w415.y w415.r w415.cap) (P33.root 2) :=
  Night6836Tree.sound w415 pick415 2 t9566 _ k415_2_2
theorem cov415_3 : PA.Covered 3 (OZ.Valid 3 w415.low w415.t w415.y w415.r w415.cap) (P33.root 3) :=
  Night6836Tree.sound w415 pick415 3 t564 _ (by decide +kernel)
theorem cov415_4 : PA.Covered 4 (OZ.Valid 4 w415.low w415.t w415.y w415.r w415.cap) (P33.root 4) :=
  Night6836Tree.sound w415 pick415 4 t565 _ (by decide +kernel)
theorem cov415_5 : PA.Covered 5 (OZ.Valid 5 w415.low w415.t w415.y w415.r w415.cap) (P33.root 5) :=
  Night6836Tree.sound w415 pick415 5 t566 _ (by decide +kernel)
theorem cov415_6 : PA.Covered 6 (OZ.Valid 6 w415.low w415.t w415.y w415.r w415.cap) (P33.root 6) :=
  Night6836Tree.sound w415 pick415 6 t567 _ (by decide +kernel)
theorem cov415_7 : PA.Covered 7 (OZ.Valid 7 w415.low w415.t w415.y w415.r w415.cap) (P33.root 7) :=
  Night6836Tree.sound w415 pick415 7 t568 _ (by decide +kernel)
theorem window415 : P33.WindowCount w415 := by
  apply P33.window_count w415 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov415_1
  · exact cov415_2
  · exact cov415_3
  · exact cov415_4
  · exact cov415_5
  · exact cov415_6
  · exact cov415_7
def w416 : P33.Window := ⟨7,39,4638,3639,198040186917367127,49668,35000,5000000,81920000000⟩
def h416_0 : Height w416 := ⟨49668,35000,by decide +kernel⟩
def h416_1 : Height w416 := ⟨55082,31000,by decide +kernel⟩
def h416_2 : Height w416 := ⟨62055,27000,by decide +kernel⟩
def h416_3 : Height w416 := ⟨71963,23000,by decide +kernel⟩
def pick416 (cl : ℕ) : Height w416 := if cl<32 then (if cl<2 then (h416_0) else (h416_1)) else (if cl<132 then (h416_2) else (h416_3))
private theorem k416_1_0 : check w416 pick416 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k416_1_1 : check w416 pick416 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k416_1_2 : check w416 pick416 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w416 pick416 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k416_1_0 k416_1_1
private theorem k416_1_3 : check w416 pick416 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k416_1_4 : check w416 pick416 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k416_1_5 : check w416 pick416 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w416 pick416 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k416_1_3 k416_1_4
private theorem k416_1_6 : check w416 pick416 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w416 pick416 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k416_1_2 k416_1_5
private theorem k416_1_7 : check w416 pick416 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k416_1_8 : check w416 pick416 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k416_1_9 : check w416 pick416 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w416 pick416 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k416_1_7 k416_1_8
private theorem k416_1_10 : check w416 pick416 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k416_1_11 : check w416 pick416 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k416_1_12 : check w416 pick416 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w416 pick416 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k416_1_10 k416_1_11
private theorem k416_1_13 : check w416 pick416 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w416 pick416 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k416_1_9 k416_1_12
private theorem k416_1_14 : check w416 pick416 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w416 pick416 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k416_1_6 k416_1_13
theorem cov416_1 : PA.Covered 1 (OZ.Valid 1 w416.low w416.t w416.y w416.r w416.cap) (P33.root 1) :=
  Night6836Tree.sound w416 pick416 1 t9554 _ k416_1_14
theorem cov416_2 : PA.Covered 2 (OZ.Valid 2 w416.low w416.t w416.y w416.r w416.cap) (P33.root 2) :=
  Night6836Tree.sound w416 pick416 2 t4274 _ (by decide +kernel)
theorem cov416_3 : PA.Covered 3 (OZ.Valid 3 w416.low w416.t w416.y w416.r w416.cap) (P33.root 3) :=
  Night6836Tree.sound w416 pick416 3 t564 _ (by decide +kernel)
theorem cov416_4 : PA.Covered 4 (OZ.Valid 4 w416.low w416.t w416.y w416.r w416.cap) (P33.root 4) :=
  Night6836Tree.sound w416 pick416 4 t565 _ (by decide +kernel)
theorem cov416_5 : PA.Covered 5 (OZ.Valid 5 w416.low w416.t w416.y w416.r w416.cap) (P33.root 5) :=
  Night6836Tree.sound w416 pick416 5 t566 _ (by decide +kernel)
theorem cov416_6 : PA.Covered 6 (OZ.Valid 6 w416.low w416.t w416.y w416.r w416.cap) (P33.root 6) :=
  Night6836Tree.sound w416 pick416 6 t567 _ (by decide +kernel)
theorem cov416_7 : PA.Covered 7 (OZ.Valid 7 w416.low w416.t w416.y w416.r w416.cap) (P33.root 7) :=
  Night6836Tree.sound w416 pick416 7 t2134 _ (by decide +kernel)
theorem window416 : P33.WindowCount w416 := by
  apply P33.window_count w416 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov416_1
  · exact cov416_2
  · exact cov416_3
  · exact cov416_4
  · exact cov416_5
  · exact cov416_6
  · exact cov416_7
def w417 : P33.Window := ⟨7,39,7528,7488,242987092240873682,23001,18000,5000000,81920000000⟩
def h417_0 : Height w417 := ⟨23001,18000,by decide +kernel⟩
def h417_1 : Height w417 := ⟨26903,15000,by decide +kernel⟩
def h417_2 : Height w417 := ⟨32761,12000,by decide +kernel⟩
def h417_3 : Height w417 := ⟨44604,9000,by decide +kernel⟩
def pick417 (cl : ℕ) : Height w417 := if cl<36 then (if cl<2 then (h417_0) else (h417_1)) else (if cl<922 then (h417_2) else (h417_3))
private theorem k417_1_0 : check w417 pick417 1 t9283 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k417_1_1 : check w417 pick417 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k417_1_2 : check w417 pick417 1 t9284 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w417 pick417 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9283 t9190 k417_1_0 k417_1_1
private theorem k417_1_3 : check w417 pick417 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k417_1_4 : check w417 pick417 1 t9579 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k417_1_5 : check w417 pick417 1 t9580 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w417 pick417 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9579 k417_1_3 k417_1_4
private theorem k417_1_6 : check w417 pick417 1 t9583 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w417 pick417 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9284 t9580 k417_1_2 k417_1_5
private theorem k417_1_7 : check w417 pick417 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k417_1_8 : check w417 pick417 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k417_1_9 : check w417 pick417 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w417 pick417 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k417_1_7 k417_1_8
private theorem k417_1_10 : check w417 pick417 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k417_1_11 : check w417 pick417 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k417_1_12 : check w417 pick417 1 t9575 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w417 pick417 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t3708 k417_1_10 k417_1_11
private theorem k417_1_13 : check w417 pick417 1 t9576 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w417 pick417 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9575 k417_1_9 k417_1_12
private theorem k417_1_14 : check w417 pick417 1 t9584 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w417 pick417 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9583 t9576 k417_1_6 k417_1_13
theorem cov417_1 : PA.Covered 1 (OZ.Valid 1 w417.low w417.t w417.y w417.r w417.cap) (P33.root 1) :=
  Night6836Tree.sound w417 pick417 1 t9584 _ k417_1_14
private theorem k417_2_0 : check w417 pick417 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k417_2_1 : check w417 pick417 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k417_2_2 : check w417 pick417 2 t9566 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w417 pick417 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t9135 k417_2_0 k417_2_1
theorem cov417_2 : PA.Covered 2 (OZ.Valid 2 w417.low w417.t w417.y w417.r w417.cap) (P33.root 2) :=
  Night6836Tree.sound w417 pick417 2 t9566 _ k417_2_2
theorem cov417_3 : PA.Covered 3 (OZ.Valid 3 w417.low w417.t w417.y w417.r w417.cap) (P33.root 3) :=
  Night6836Tree.sound w417 pick417 3 t564 _ (by decide +kernel)
theorem cov417_4 : PA.Covered 4 (OZ.Valid 4 w417.low w417.t w417.y w417.r w417.cap) (P33.root 4) :=
  Night6836Tree.sound w417 pick417 4 t565 _ (by decide +kernel)
theorem cov417_5 : PA.Covered 5 (OZ.Valid 5 w417.low w417.t w417.y w417.r w417.cap) (P33.root 5) :=
  Night6836Tree.sound w417 pick417 5 t566 _ (by decide +kernel)
theorem cov417_6 : PA.Covered 6 (OZ.Valid 6 w417.low w417.t w417.y w417.r w417.cap) (P33.root 6) :=
  Night6836Tree.sound w417 pick417 6 t567 _ (by decide +kernel)
theorem cov417_7 : PA.Covered 7 (OZ.Valid 7 w417.low w417.t w417.y w417.r w417.cap) (P33.root 7) :=
  Night6836Tree.sound w417 pick417 7 t568 _ (by decide +kernel)
theorem window417 : P33.WindowCount w417 := by
  apply P33.window_count w417 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov417_1
  · exact cov417_2
  · exact cov417_3
  · exact cov417_4
  · exact cov417_5
  · exact cov417_6
  · exact cov417_7
def w418 : P33.Window := ⟨7,40,7487,7348,244565990051140747,24753,18000,5000000,81920000000⟩
def h418_0 : Height w418 := ⟨24753,18000,by decide +kernel⟩
def h418_1 : Height w418 := ⟨28855,15000,by decide +kernel⟩
def h418_2 : Height w418 := ⟨35104,12000,by decide +kernel⟩
def h418_3 : Height w418 := ⟨48001,9000,by decide +kernel⟩
def pick418 (cl : ℕ) : Height w418 := if cl<46 then (if cl<2 then (h418_0) else (h418_1)) else (if cl<1021 then (h418_2) else (h418_3))
private theorem k418_1_0 : check w418 pick418 1 t9283 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k418_1_1 : check w418 pick418 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k418_1_2 : check w418 pick418 1 t9284 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w418 pick418 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9283 t9190 k418_1_0 k418_1_1
private theorem k418_1_3 : check w418 pick418 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k418_1_4 : check w418 pick418 1 t9579 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k418_1_5 : check w418 pick418 1 t9580 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w418 pick418 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9579 k418_1_3 k418_1_4
private theorem k418_1_6 : check w418 pick418 1 t9583 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w418 pick418 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9284 t9580 k418_1_2 k418_1_5
private theorem k418_1_7 : check w418 pick418 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k418_1_8 : check w418 pick418 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k418_1_9 : check w418 pick418 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w418 pick418 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k418_1_7 k418_1_8
private theorem k418_1_10 : check w418 pick418 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k418_1_11 : check w418 pick418 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k418_1_12 : check w418 pick418 1 t9575 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w418 pick418 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t3708 k418_1_10 k418_1_11
private theorem k418_1_13 : check w418 pick418 1 t9576 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w418 pick418 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9575 k418_1_9 k418_1_12
private theorem k418_1_14 : check w418 pick418 1 t9584 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w418 pick418 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9583 t9576 k418_1_6 k418_1_13
theorem cov418_1 : PA.Covered 1 (OZ.Valid 1 w418.low w418.t w418.y w418.r w418.cap) (P33.root 1) :=
  Night6836Tree.sound w418 pick418 1 t9584 _ k418_1_14
private theorem k418_2_0 : check w418 pick418 2 t9585 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k418_2_1 : check w418 pick418 2 t9589 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k418_2_2 : check w418 pick418 2 t9590 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w418 pick418 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t9585 t9589 k418_2_0 k418_2_1
theorem cov418_2 : PA.Covered 2 (OZ.Valid 2 w418.low w418.t w418.y w418.r w418.cap) (P33.root 2) :=
  Night6836Tree.sound w418 pick418 2 t9590 _ k418_2_2
theorem cov418_3 : PA.Covered 3 (OZ.Valid 3 w418.low w418.t w418.y w418.r w418.cap) (P33.root 3) :=
  Night6836Tree.sound w418 pick418 3 t564 _ (by decide +kernel)
theorem cov418_4 : PA.Covered 4 (OZ.Valid 4 w418.low w418.t w418.y w418.r w418.cap) (P33.root 4) :=
  Night6836Tree.sound w418 pick418 4 t565 _ (by decide +kernel)
theorem cov418_5 : PA.Covered 5 (OZ.Valid 5 w418.low w418.t w418.y w418.r w418.cap) (P33.root 5) :=
  Night6836Tree.sound w418 pick418 5 t566 _ (by decide +kernel)
theorem cov418_6 : PA.Covered 6 (OZ.Valid 6 w418.low w418.t w418.y w418.r w418.cap) (P33.root 6) :=
  Night6836Tree.sound w418 pick418 6 t567 _ (by decide +kernel)
theorem cov418_7 : PA.Covered 7 (OZ.Valid 7 w418.low w418.t w418.y w418.r w418.cap) (P33.root 7) :=
  Night6836Tree.sound w418 pick418 7 t568 _ (by decide +kernel)
theorem window418 : P33.WindowCount w418 := by
  apply P33.window_count w418 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov418_1
  · exact cov418_2
  · exact cov418_3
  · exact cov418_4
  · exact cov418_5
  · exact cov418_6
  · exact cov418_7
def w419 : P33.Window := ⟨7,41,4640,3641,198585251393102440,53389,35000,5000000,81920000000⟩
def h419_0 : Height w419 := ⟨53389,35000,by decide +kernel⟩
def h419_1 : Height w419 := ⟨58987,31000,by decide +kernel⟩
def h419_2 : Height w419 := ⟨66226,27000,by decide +kernel⟩
def h419_3 : Height w419 := ⟨76554,23000,by decide +kernel⟩
def pick419 (cl : ℕ) : Height w419 := if cl<32 then (if cl<4 then (h419_0) else (h419_1)) else (if cl<172 then (h419_2) else (h419_3))
private theorem k419_1_0 : check w419 pick419 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k419_1_1 : check w419 pick419 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k419_1_2 : check w419 pick419 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w419 pick419 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k419_1_0 k419_1_1
private theorem k419_1_3 : check w419 pick419 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k419_1_4 : check w419 pick419 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k419_1_5 : check w419 pick419 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w419 pick419 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k419_1_3 k419_1_4
private theorem k419_1_6 : check w419 pick419 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w419 pick419 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k419_1_2 k419_1_5
private theorem k419_1_7 : check w419 pick419 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k419_1_8 : check w419 pick419 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k419_1_9 : check w419 pick419 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w419 pick419 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k419_1_7 k419_1_8
private theorem k419_1_10 : check w419 pick419 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k419_1_11 : check w419 pick419 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k419_1_12 : check w419 pick419 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w419 pick419 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k419_1_10 k419_1_11
private theorem k419_1_13 : check w419 pick419 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w419 pick419 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k419_1_9 k419_1_12
private theorem k419_1_14 : check w419 pick419 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w419 pick419 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k419_1_6 k419_1_13
theorem cov419_1 : PA.Covered 1 (OZ.Valid 1 w419.low w419.t w419.y w419.r w419.cap) (P33.root 1) :=
  Night6836Tree.sound w419 pick419 1 t9554 _ k419_1_14
theorem cov419_2 : PA.Covered 2 (OZ.Valid 2 w419.low w419.t w419.y w419.r w419.cap) (P33.root 2) :=
  Night6836Tree.sound w419 pick419 2 t9593 _ (by decide +kernel)
theorem cov419_3 : PA.Covered 3 (OZ.Valid 3 w419.low w419.t w419.y w419.r w419.cap) (P33.root 3) :=
  Night6836Tree.sound w419 pick419 3 t564 _ (by decide +kernel)
theorem cov419_4 : PA.Covered 4 (OZ.Valid 4 w419.low w419.t w419.y w419.r w419.cap) (P33.root 4) :=
  Night6836Tree.sound w419 pick419 4 t565 _ (by decide +kernel)
theorem cov419_5 : PA.Covered 5 (OZ.Valid 5 w419.low w419.t w419.y w419.r w419.cap) (P33.root 5) :=
  Night6836Tree.sound w419 pick419 5 t566 _ (by decide +kernel)
theorem cov419_6 : PA.Covered 6 (OZ.Valid 6 w419.low w419.t w419.y w419.r w419.cap) (P33.root 6) :=
  Night6836Tree.sound w419 pick419 6 t567 _ (by decide +kernel)
theorem cov419_7 : PA.Covered 7 (OZ.Valid 7 w419.low w419.t w419.y w419.r w419.cap) (P33.root 7) :=
  Night6836Tree.sound w419 pick419 7 t2134 _ (by decide +kernel)
theorem window419 : P33.WindowCount w419 := by
  apply P33.window_count w419 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov419_1
  · exact cov419_2
  · exact cov419_3
  · exact cov419_4
  · exact cov419_5
  · exact cov419_6
  · exact cov419_7
end ProximityPrize.SubmissionLower.Night6836Bank
