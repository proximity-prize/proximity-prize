/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT02
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w150 : P33.Window := ⟨11,51,5032,4722,246422504460249065,49093,39000,5000000,81920000000⟩
def h150_0 : Height w150 := ⟨49093,39000,by decide +kernel⟩
def h150_1 : Height w150 := ⟨53088,36000,by decide +kernel⟩
def h150_2 : Height w150 := ⟨57779,33000,by decide +kernel⟩
def h150_3 : Height w150 := ⟨63501,30000,by decide +kernel⟩
def h150_4 : Height w150 := ⟨70851,27000,by decide +kernel⟩
def h150_5 : Height w150 := ⟨80991,24000,by decide +kernel⟩
def h150_6 : Height w150 := ⟨96522,21000,by decide +kernel⟩
def pick150 (cl : ℕ) : Height w150 := if cl<32 then (if cl<2 then (h150_0) else (if cl<10 then (h150_1) else (h150_2))) else (if cl<556 then (if cl<117 then (h150_3) else (h150_4)) else (if cl<1014 then (h150_5) else (h150_6)))
private theorem k150_1_0 : check w150 pick150 1 t5570 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k150_1_1 : check w150 pick150 1 t5960 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k150_1_2 : check w150 pick150 1 t5961 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w150 pick150 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5570 t5960 k150_1_0 k150_1_1
private theorem k150_1_3 : check w150 pick150 1 t6458 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k150_1_4 : check w150 pick150 1 t5979 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k150_1_5 : check w150 pick150 1 t6459 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w150 pick150 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t6458 t5979 k150_1_3 k150_1_4
private theorem k150_1_6 : check w150 pick150 1 t6460 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w150 pick150 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5961 t6459 k150_1_2 k150_1_5
private theorem k150_1_7 : check w150 pick150 1 t5991 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k150_1_8 : check w150 pick150 1 t3840 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k150_1_9 : check w150 pick150 1 t5992 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w150 pick150 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t5991 t3840 k150_1_7 k150_1_8
private theorem k150_1_10 : check w150 pick150 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k150_1_11 : check w150 pick150 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k150_1_12 : check w150 pick150 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w150 pick150 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k150_1_10 k150_1_11
private theorem k150_1_13 : check w150 pick150 1 t5993 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w150 pick150 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5992 t3709 k150_1_9 k150_1_12
private theorem k150_1_14 : check w150 pick150 1 t6461 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w150 pick150 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t6460 t5993 k150_1_6 k150_1_13
theorem cov150_1 : PA.Covered 1 (OZ.Valid 1 w150.low w150.t w150.y w150.r w150.cap) (P33.root 1) :=
  Night6836Tree.sound w150 pick150 1 t6461 _ k150_1_14
private theorem k150_2_0 : check w150 pick150 2 t5998 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k150_2_1 : check w150 pick150 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k150_2_2 : check w150 pick150 2 t5999 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w150 pick150 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5998 t3777 k150_2_0 k150_2_1
private theorem k150_2_3 : check w150 pick150 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k150_2_4 : check w150 pick150 2 t6469 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k150_2_5 : check w150 pick150 2 t6470 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w150 pick150 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t6469 k150_2_3 k150_2_4
private theorem k150_2_6 : check w150 pick150 2 t6471 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w150 pick150 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5999 t6470 k150_2_2 k150_2_5
theorem cov150_2 : PA.Covered 2 (OZ.Valid 2 w150.low w150.t w150.y w150.r w150.cap) (P33.root 2) :=
  Night6836Tree.sound w150 pick150 2 t6471 _ k150_2_6
theorem cov150_3 : PA.Covered 3 (OZ.Valid 3 w150.low w150.t w150.y w150.r w150.cap) (P33.root 3) :=
  Night6836Tree.sound w150 pick150 3 t564 _ (by decide +kernel)
theorem cov150_4 : PA.Covered 4 (OZ.Valid 4 w150.low w150.t w150.y w150.r w150.cap) (P33.root 4) :=
  Night6836Tree.sound w150 pick150 4 t565 _ (by decide +kernel)
theorem cov150_5 : PA.Covered 5 (OZ.Valid 5 w150.low w150.t w150.y w150.r w150.cap) (P33.root 5) :=
  Night6836Tree.sound w150 pick150 5 t566 _ (by decide +kernel)
theorem cov150_6 : PA.Covered 6 (OZ.Valid 6 w150.low w150.t w150.y w150.r w150.cap) (P33.root 6) :=
  Night6836Tree.sound w150 pick150 6 t567 _ (by decide +kernel)
theorem cov150_7 : PA.Covered 7 (OZ.Valid 7 w150.low w150.t w150.y w150.r w150.cap) (P33.root 7) :=
  Night6836Tree.sound w150 pick150 7 t2134 _ (by decide +kernel)
theorem window150 : P33.WindowCount w150 := by
  apply P33.window_count w150 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov150_1
  · exact cov150_2
  · exact cov150_3
  · exact cov150_4
  · exact cov150_5
  · exact cov150_6
  · exact cov150_7
def w151 : P33.Window := ⟨11,52,4721,4398,246948354030939351,54156,42000,5000000,81920000000⟩
def h151_0 : Height w151 := ⟨54156,42000,by decide +kernel⟩
def h151_1 : Height w151 := ⟨58159,39000,by decide +kernel⟩
def h151_2 : Height w151 := ⟨62795,36000,by decide +kernel⟩
def h151_3 : Height w151 := ⟨68339,33000,by decide +kernel⟩
def h151_4 : Height w151 := ⟨75251,30000,by decide +kernel⟩
def h151_5 : Height w151 := ⟨84363,27000,by decide +kernel⟩
def h151_6 : Height w151 := ⟨97351,24000,by decide +kernel⟩
def pick151 (cl : ℕ) : Height w151 := if cl<32 then (if cl<2 then (h151_0) else (if cl<6 then (h151_1) else (h151_2))) else (if cl<302 then (if cl<92 then (h151_3) else (h151_4)) else (if cl<961 then (h151_5) else (h151_6)))
private theorem k151_1_0 : check w151 pick151 1 t6472 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k151_1_1 : check w151 pick151 1 t6484 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k151_1_2 : check w151 pick151 1 t6485 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w151 pick151 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t6472 t6484 k151_1_0 k151_1_1
private theorem k151_1_3 : check w151 pick151 1 t6498 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k151_1_4 : check w151 pick151 1 t6500 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k151_1_5 : check w151 pick151 1 t6501 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w151 pick151 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t6498 t6500 k151_1_3 k151_1_4
private theorem k151_1_6 : check w151 pick151 1 t6502 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w151 pick151 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t6485 t6501 k151_1_2 k151_1_5
private theorem k151_1_7 : check w151 pick151 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k151_1_8 : check w151 pick151 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k151_1_9 : check w151 pick151 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w151 pick151 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k151_1_7 k151_1_8
private theorem k151_1_10 : check w151 pick151 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k151_1_11 : check w151 pick151 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k151_1_12 : check w151 pick151 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w151 pick151 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k151_1_10 k151_1_11
private theorem k151_1_13 : check w151 pick151 1 t3710 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w151 pick151 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t3709 k151_1_9 k151_1_12
private theorem k151_1_14 : check w151 pick151 1 t6503 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w151 pick151 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6502 t3710 k151_1_6 k151_1_13
theorem cov151_1 : PA.Covered 1 (OZ.Valid 1 w151.low w151.t w151.y w151.r w151.cap) (P33.root 1) :=
  Night6836Tree.sound w151 pick151 1 t6503 _ k151_1_14
private theorem k151_2_0 : check w151 pick151 2 t6505 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k151_2_1 : check w151 pick151 2 t6506 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k151_2_2 : check w151 pick151 2 t6507 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w151 pick151 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t6505 t6506 k151_2_0 k151_2_1
theorem cov151_2 : PA.Covered 2 (OZ.Valid 2 w151.low w151.t w151.y w151.r w151.cap) (P33.root 2) :=
  Night6836Tree.sound w151 pick151 2 t6507 _ k151_2_2
theorem cov151_3 : PA.Covered 3 (OZ.Valid 3 w151.low w151.t w151.y w151.r w151.cap) (P33.root 3) :=
  Night6836Tree.sound w151 pick151 3 t564 _ (by decide +kernel)
theorem cov151_4 : PA.Covered 4 (OZ.Valid 4 w151.low w151.t w151.y w151.r w151.cap) (P33.root 4) :=
  Night6836Tree.sound w151 pick151 4 t565 _ (by decide +kernel)
theorem cov151_5 : PA.Covered 5 (OZ.Valid 5 w151.low w151.t w151.y w151.r w151.cap) (P33.root 5) :=
  Night6836Tree.sound w151 pick151 5 t566 _ (by decide +kernel)
theorem cov151_6 : PA.Covered 6 (OZ.Valid 6 w151.low w151.t w151.y w151.r w151.cap) (P33.root 6) :=
  Night6836Tree.sound w151 pick151 6 t567 _ (by decide +kernel)
theorem cov151_7 : PA.Covered 7 (OZ.Valid 7 w151.low w151.t w151.y w151.r w151.cap) (P33.root 7) :=
  Night6836Tree.sound w151 pick151 7 t2134 _ (by decide +kernel)
theorem window151 : P33.WindowCount w151 := by
  apply P33.window_count w151 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov151_1
  · exact cov151_2
  · exact cov151_3
  · exact cov151_4
  · exact cov151_5
  · exact cov151_6
  · exact cov151_7
def w152 : P33.Window := ⟨11,53,4397,3707,245981954504326573,68522,48000,5000000,81920000000⟩
def h152_0 : Height w152 := ⟨68522,48000,by decide +kernel⟩
def h152_1 : Height w152 := ⟨72822,45000,by decide +kernel⟩
def h152_2 : Height w152 := ⟨77733,42000,by decide +kernel⟩
def h152_3 : Height w152 := ⟨83480,39000,by decide +kernel⟩
def h152_4 : Height w152 := ⟨90411,36000,by decide +kernel⟩
def h152_5 : Height w152 := ⟨99101,33000,by decide +kernel⟩
def h152_6 : Height w152 := ⟨110561,30000,by decide +kernel⟩
def pick152 (cl : ℕ) : Height w152 := if cl<32 then (if cl<4 then (h152_0) else (if cl<13 then (h152_1) else (h152_2))) else (if cl<260 then (if cl<92 then (h152_3) else (h152_4)) else (if cl<922 then (h152_5) else (h152_6)))
private theorem k152_1_0 : check w152 pick152 1 t6395 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k152_1_1 : check w152 pick152 1 t6402 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k152_1_2 : check w152 pick152 1 t6403 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w152 pick152 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t6395 t6402 k152_1_0 k152_1_1
private theorem k152_1_3 : check w152 pick152 1 t6511 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k152_1_4 : check w152 pick152 1 t6203 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k152_1_5 : check w152 pick152 1 t6512 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w152 pick152 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t6511 t6203 k152_1_3 k152_1_4
private theorem k152_1_6 : check w152 pick152 1 t6513 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w152 pick152 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t6403 t6512 k152_1_2 k152_1_5
private theorem k152_1_7 : check w152 pick152 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k152_1_8 : check w152 pick152 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k152_1_9 : check w152 pick152 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w152 pick152 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k152_1_7 k152_1_8
private theorem k152_1_10 : check w152 pick152 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k152_1_11 : check w152 pick152 1 t6514 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k152_1_12 : check w152 pick152 1 t6515 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w152 pick152 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t6514 k152_1_10 k152_1_11
private theorem k152_1_13 : check w152 pick152 1 t6516 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w152 pick152 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t6515 k152_1_9 k152_1_12
private theorem k152_1_14 : check w152 pick152 1 t6517 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w152 pick152 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6513 t6516 k152_1_6 k152_1_13
theorem cov152_1 : PA.Covered 1 (OZ.Valid 1 w152.low w152.t w152.y w152.r w152.cap) (P33.root 1) :=
  Night6836Tree.sound w152 pick152 1 t6517 _ k152_1_14
private theorem k152_2_0 : check w152 pick152 2 t6415 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k152_2_1 : check w152 pick152 2 t5187 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k152_2_2 : check w152 pick152 2 t6416 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w152 pick152 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t6415 t5187 k152_2_0 k152_2_1
theorem cov152_2 : PA.Covered 2 (OZ.Valid 2 w152.low w152.t w152.y w152.r w152.cap) (P33.root 2) :=
  Night6836Tree.sound w152 pick152 2 t6416 _ k152_2_2
theorem cov152_3 : PA.Covered 3 (OZ.Valid 3 w152.low w152.t w152.y w152.r w152.cap) (P33.root 3) :=
  Night6836Tree.sound w152 pick152 3 t564 _ (by decide +kernel)
theorem cov152_4 : PA.Covered 4 (OZ.Valid 4 w152.low w152.t w152.y w152.r w152.cap) (P33.root 4) :=
  Night6836Tree.sound w152 pick152 4 t565 _ (by decide +kernel)
theorem cov152_5 : PA.Covered 5 (OZ.Valid 5 w152.low w152.t w152.y w152.r w152.cap) (P33.root 5) :=
  Night6836Tree.sound w152 pick152 5 t566 _ (by decide +kernel)
theorem cov152_6 : PA.Covered 6 (OZ.Valid 6 w152.low w152.t w152.y w152.r w152.cap) (P33.root 6) :=
  Night6836Tree.sound w152 pick152 6 t567 _ (by decide +kernel)
theorem cov152_7 : PA.Covered 7 (OZ.Valid 7 w152.low w152.t w152.y w152.r w152.cap) (P33.root 7) :=
  Night6836Tree.sound w152 pick152 7 t2134 _ (by decide +kernel)
theorem window152 : P33.WindowCount w152 := by
  apply P33.window_count w152 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov152_1
  · exact cov152_2
  · exact cov152_3
  · exact cov152_4
  · exact cov152_5
  · exact cov152_6
  · exact cov152_7
def w153 : P33.Window := ⟨11,54,4059,3707,246468191722365700,70462,48000,5000000,81920000000⟩
def h153_0 : Height w153 := ⟨70462,48000,by decide +kernel⟩
def h153_1 : Height w153 := ⟨74820,45000,by decide +kernel⟩
def h153_2 : Height w153 := ⟨79801,42000,by decide +kernel⟩
def h153_3 : Height w153 := ⟨85635,39000,by decide +kernel⟩
def h153_4 : Height w153 := ⟨92677,36000,by decide +kernel⟩
def h153_5 : Height w153 := ⟨101512,33000,by decide +kernel⟩
def h153_6 : Height w153 := ⟨113173,30000,by decide +kernel⟩
def pick153 (cl : ℕ) : Height w153 := if cl<36 then (if cl<5 then (h153_0) else (if cl<14 then (h153_1) else (h153_2))) else (if cl<269 then (if cl<95 then (h153_3) else (h153_4)) else (if cl<989 then (h153_5) else (h153_6)))
private theorem k153_1_0 : check w153 pick153 1 t52 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k153_1_1 : check w153 pick153 1 t6519 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k153_1_2 : check w153 pick153 1 t6520 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w153 pick153 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t52 t6519 k153_1_0 k153_1_1
private theorem k153_1_3 : check w153 pick153 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k153_1_4 : check w153 pick153 1 t6523 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k153_1_5 : check w153 pick153 1 t6524 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w153 pick153 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6523 k153_1_3 k153_1_4
private theorem k153_1_6 : check w153 pick153 1 t6525 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w153 pick153 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t6520 t6524 k153_1_2 k153_1_5
private theorem k153_1_7 : check w153 pick153 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k153_1_8 : check w153 pick153 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k153_1_9 : check w153 pick153 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w153 pick153 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k153_1_7 k153_1_8
private theorem k153_1_10 : check w153 pick153 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k153_1_11 : check w153 pick153 1 t4260 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k153_1_12 : check w153 pick153 1 t4261 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w153 pick153 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t4260 k153_1_10 k153_1_11
private theorem k153_1_13 : check w153 pick153 1 t4262 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w153 pick153 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t4261 k153_1_9 k153_1_12
private theorem k153_1_14 : check w153 pick153 1 t6526 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w153 pick153 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6525 t4262 k153_1_6 k153_1_13
theorem cov153_1 : PA.Covered 1 (OZ.Valid 1 w153.low w153.t w153.y w153.r w153.cap) (P33.root 1) :=
  Night6836Tree.sound w153 pick153 1 t6526 _ k153_1_14
private theorem k153_2_0 : check w153 pick153 2 t6534 ⟨2,7,4,16,2,52,2,166⟩ = true := by decide +kernel
private theorem k153_2_1 : check w153 pick153 2 t5204 ⟨2,7,4,16,2,52,167,450⟩ = true := by decide +kernel
private theorem k153_2_2 : check w153 pick153 2 t6535 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w153 pick153 2 ⟨2,7,4,16,0,52,0,450⟩ 3 166 t6534 t5204 k153_2_0 k153_2_1
theorem cov153_2 : PA.Covered 2 (OZ.Valid 2 w153.low w153.t w153.y w153.r w153.cap) (P33.root 2) :=
  Night6836Tree.sound w153 pick153 2 t6535 _ k153_2_2
theorem cov153_3 : PA.Covered 3 (OZ.Valid 3 w153.low w153.t w153.y w153.r w153.cap) (P33.root 3) :=
  Night6836Tree.sound w153 pick153 3 t564 _ (by decide +kernel)
theorem cov153_4 : PA.Covered 4 (OZ.Valid 4 w153.low w153.t w153.y w153.r w153.cap) (P33.root 4) :=
  Night6836Tree.sound w153 pick153 4 t565 _ (by decide +kernel)
theorem cov153_5 : PA.Covered 5 (OZ.Valid 5 w153.low w153.t w153.y w153.r w153.cap) (P33.root 5) :=
  Night6836Tree.sound w153 pick153 5 t566 _ (by decide +kernel)
theorem cov153_6 : PA.Covered 6 (OZ.Valid 6 w153.low w153.t w153.y w153.r w153.cap) (P33.root 6) :=
  Night6836Tree.sound w153 pick153 6 t567 _ (by decide +kernel)
theorem cov153_7 : PA.Covered 7 (OZ.Valid 7 w153.low w153.t w153.y w153.r w153.cap) (P33.root 7) :=
  Night6836Tree.sound w153 pick153 7 t2134 _ (by decide +kernel)
theorem window153 : P33.WindowCount w153 := by
  apply P33.window_count w153 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov153_1
  · exact cov153_2
  · exact cov153_3
  · exact cov153_4
  · exact cov153_5
  · exact cov153_6
  · exact cov153_7
def w154 : P33.Window := ⟨11,55,3706,3341,244878385643791664,79292,54000,5000000,81920000000⟩
def h154_0 : Height w154 := ⟨79292,54000,by decide +kernel⟩
def h154_1 : Height w154 := ⟨83557,51000,by decide +kernel⟩
def h154_2 : Height w154 := ⟨88341,48000,by decide +kernel⟩
def h154_3 : Height w154 := ⟨93806,45000,by decide +kernel⟩
def h154_4 : Height w154 := ⟨100186,42000,by decide +kernel⟩
def h154_5 : Height w154 := ⟨107840,39000,by decide +kernel⟩
def h154_6 : Height w154 := ⟨117338,36000,by decide +kernel⟩
def pick154 (cl : ℕ) : Height w154 := if cl<32 then (if cl<4 then (h154_0) else (if cl<10 then (h154_1) else (h154_2))) else (if cl<181 then (if cl<51 then (h154_3) else (h154_4)) else (if cl<317 then (h154_5) else (h154_6)))
private theorem k154_1_0 : check w154 pick154 1 t6541 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k154_1_1 : check w154 pick154 1 t5292 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k154_1_2 : check w154 pick154 1 t6542 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w154 pick154 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t6541 t5292 k154_1_0 k154_1_1
private theorem k154_1_3 : check w154 pick154 1 t6543 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k154_1_4 : check w154 pick154 1 t6544 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w154 pick154 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t6542 t6543 k154_1_2 k154_1_3
private theorem k154_1_5 : check w154 pick154 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k154_1_6 : check w154 pick154 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k154_1_7 : check w154 pick154 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w154 pick154 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k154_1_5 k154_1_6
private theorem k154_1_8 : check w154 pick154 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k154_1_9 : check w154 pick154 1 t4260 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k154_1_10 : check w154 pick154 1 t4261 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w154 pick154 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t4260 k154_1_8 k154_1_9
private theorem k154_1_11 : check w154 pick154 1 t4262 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w154 pick154 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t4261 k154_1_7 k154_1_10
private theorem k154_1_12 : check w154 pick154 1 t6545 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w154 pick154 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6544 t4262 k154_1_4 k154_1_11
theorem cov154_1 : PA.Covered 1 (OZ.Valid 1 w154.low w154.t w154.y w154.r w154.cap) (P33.root 1) :=
  Night6836Tree.sound w154 pick154 1 t6545 _ k154_1_12
theorem cov154_2 : PA.Covered 2 (OZ.Valid 2 w154.low w154.t w154.y w154.r w154.cap) (P33.root 2) :=
  Night6836Tree.sound w154 pick154 2 t6553 _ (by decide +kernel)
theorem cov154_3 : PA.Covered 3 (OZ.Valid 3 w154.low w154.t w154.y w154.r w154.cap) (P33.root 3) :=
  Night6836Tree.sound w154 pick154 3 t564 _ (by decide +kernel)
theorem cov154_4 : PA.Covered 4 (OZ.Valid 4 w154.low w154.t w154.y w154.r w154.cap) (P33.root 4) :=
  Night6836Tree.sound w154 pick154 4 t565 _ (by decide +kernel)
theorem cov154_5 : PA.Covered 5 (OZ.Valid 5 w154.low w154.t w154.y w154.r w154.cap) (P33.root 5) :=
  Night6836Tree.sound w154 pick154 5 t566 _ (by decide +kernel)
theorem cov154_6 : PA.Covered 6 (OZ.Valid 6 w154.low w154.t w154.y w154.r w154.cap) (P33.root 6) :=
  Night6836Tree.sound w154 pick154 6 t567 _ (by decide +kernel)
theorem cov154_7 : PA.Covered 7 (OZ.Valid 7 w154.low w154.t w154.y w154.r w154.cap) (P33.root 7) :=
  Night6836Tree.sound w154 pick154 7 t2134 _ (by decide +kernel)
theorem window154 : P33.WindowCount w154 := by
  apply P33.window_count w154 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov154_1
  · exact cov154_2
  · exact cov154_3
  · exact cov154_4
  · exact cov154_5
  · exact cov154_6
  · exact cov154_7
def w155 : P33.Window := ⟨11,56,3340,2960,244473948328840053,89156,63000,5000000,81920000000⟩
def h155_0 : Height w155 := ⟨89156,63000,by decide +kernel⟩
def h155_1 : Height w155 := ⟨93184,60000,by decide +kernel⟩
def h155_2 : Height w155 := ⟨97601,57000,by decide +kernel⟩
def h155_3 : Height w155 := ⟨102505,54000,by decide +kernel⟩
def h155_4 : Height w155 := ⟨108028,51000,by decide +kernel⟩
def h155_5 : Height w155 := ⟨114357,48000,by decide +kernel⟩
def h155_6 : Height w155 := ⟨121758,45000,by decide +kernel⟩
def h155_7 : Height w155 := ⟨130633,42000,by decide +kernel⟩
def pick155 (cl : ℕ) : Height w155 := if cl<32 then (if cl<5 then (if cl<2 then (h155_0) else (h155_1)) else (if cl<13 then (h155_2) else (h155_3))) else (if cl<120 then (if cl<49 then (h155_4) else (h155_5)) else (if cl<278 then (h155_6) else (h155_7)))
private theorem k155_1_0 : check w155 pick155 1 t6541 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k155_1_1 : check w155 pick155 1 t5292 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k155_1_2 : check w155 pick155 1 t6542 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w155 pick155 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t6541 t5292 k155_1_0 k155_1_1
private theorem k155_1_3 : check w155 pick155 1 t6543 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k155_1_4 : check w155 pick155 1 t6544 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w155 pick155 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t6542 t6543 k155_1_2 k155_1_3
private theorem k155_1_5 : check w155 pick155 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k155_1_6 : check w155 pick155 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k155_1_7 : check w155 pick155 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w155 pick155 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k155_1_5 k155_1_6
private theorem k155_1_8 : check w155 pick155 1 t5264 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k155_1_9 : check w155 pick155 1 t5265 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w155 pick155 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5264 k155_1_7 k155_1_8
private theorem k155_1_10 : check w155 pick155 1 t6554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w155 pick155 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6544 t5265 k155_1_4 k155_1_9
theorem cov155_1 : PA.Covered 1 (OZ.Valid 1 w155.low w155.t w155.y w155.r w155.cap) (P33.root 1) :=
  Night6836Tree.sound w155 pick155 1 t6554 _ k155_1_10
theorem cov155_2 : PA.Covered 2 (OZ.Valid 2 w155.low w155.t w155.y w155.r w155.cap) (P33.root 2) :=
  Night6836Tree.sound w155 pick155 2 t6560 _ (by decide +kernel)
theorem cov155_3 : PA.Covered 3 (OZ.Valid 3 w155.low w155.t w155.y w155.r w155.cap) (P33.root 3) :=
  Night6836Tree.sound w155 pick155 3 t564 _ (by decide +kernel)
theorem cov155_4 : PA.Covered 4 (OZ.Valid 4 w155.low w155.t w155.y w155.r w155.cap) (P33.root 4) :=
  Night6836Tree.sound w155 pick155 4 t565 _ (by decide +kernel)
theorem cov155_5 : PA.Covered 5 (OZ.Valid 5 w155.low w155.t w155.y w155.r w155.cap) (P33.root 5) :=
  Night6836Tree.sound w155 pick155 5 t566 _ (by decide +kernel)
theorem cov155_6 : PA.Covered 6 (OZ.Valid 6 w155.low w155.t w155.y w155.r w155.cap) (P33.root 6) :=
  Night6836Tree.sound w155 pick155 6 t567 _ (by decide +kernel)
theorem cov155_7 : PA.Covered 7 (OZ.Valid 7 w155.low w155.t w155.y w155.r w155.cap) (P33.root 7) :=
  Night6836Tree.sound w155 pick155 7 t2134 _ (by decide +kernel)
theorem window155 : P33.WindowCount w155 := by
  apply P33.window_count w155 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov155_1
  · exact cov155_2
  · exact cov155_3
  · exact cov155_4
  · exact cov155_5
  · exact cov155_6
  · exact cov155_7
def w156 : P33.Window := ⟨11,57,2959,2564,239600054967971193,106565,72000,5000000,81920000000⟩
def h156_0 : Height w156 := ⟨106565,72000,by decide +kernel⟩
def h156_1 : Height w156 := ⟨110684,69000,by decide +kernel⟩
def h156_2 : Height w156 := ⟨115149,66000,by decide +kernel⟩
def h156_3 : Height w156 := ⟨120035,63000,by decide +kernel⟩
def h156_4 : Height w156 := ⟨125438,60000,by decide +kernel⟩
def h156_5 : Height w156 := ⟨131487,57000,by decide +kernel⟩
def h156_6 : Height w156 := ⟨138354,54000,by decide +kernel⟩
def h156_7 : Height w156 := ⟨146282,51000,by decide +kernel⟩
def h156_8 : Height w156 := ⟨155616,48000,by decide +kernel⟩
def pick156 (cl : ℕ) : Height w156 := if cl<32 then (if cl<5 then (if cl<3 then (h156_0) else (h156_1)) else (if cl<13 then (h156_2) else (h156_3))) else (if cl<83 then (if cl<40 then (h156_4) else (h156_5)) else (if cl<181 then (h156_6) else (if cl<312 then (h156_7) else (h156_8))))
private theorem k156_1_0 : check w156 pick156 1 t6574 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k156_1_1 : check w156 pick156 1 t5292 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k156_1_2 : check w156 pick156 1 t6575 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w156 pick156 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t6574 t5292 k156_1_0 k156_1_1
private theorem k156_1_3 : check w156 pick156 1 t6578 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k156_1_4 : check w156 pick156 1 t6579 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w156 pick156 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t6575 t6578 k156_1_2 k156_1_3
private theorem k156_1_5 : check w156 pick156 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k156_1_6 : check w156 pick156 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k156_1_7 : check w156 pick156 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w156 pick156 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k156_1_5 k156_1_6
private theorem k156_1_8 : check w156 pick156 1 t5264 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k156_1_9 : check w156 pick156 1 t5265 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w156 pick156 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5264 k156_1_7 k156_1_8
private theorem k156_1_10 : check w156 pick156 1 t6580 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w156 pick156 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6579 t5265 k156_1_4 k156_1_9
theorem cov156_1 : PA.Covered 1 (OZ.Valid 1 w156.low w156.t w156.y w156.r w156.cap) (P33.root 1) :=
  Night6836Tree.sound w156 pick156 1 t6580 _ k156_1_10
theorem cov156_2 : PA.Covered 2 (OZ.Valid 2 w156.low w156.t w156.y w156.r w156.cap) (P33.root 2) :=
  Night6836Tree.sound w156 pick156 2 t6560 _ (by decide +kernel)
theorem cov156_3 : PA.Covered 3 (OZ.Valid 3 w156.low w156.t w156.y w156.r w156.cap) (P33.root 3) :=
  Night6836Tree.sound w156 pick156 3 t564 _ (by decide +kernel)
theorem cov156_4 : PA.Covered 4 (OZ.Valid 4 w156.low w156.t w156.y w156.r w156.cap) (P33.root 4) :=
  Night6836Tree.sound w156 pick156 4 t565 _ (by decide +kernel)
theorem cov156_5 : PA.Covered 5 (OZ.Valid 5 w156.low w156.t w156.y w156.r w156.cap) (P33.root 5) :=
  Night6836Tree.sound w156 pick156 5 t566 _ (by decide +kernel)
theorem cov156_6 : PA.Covered 6 (OZ.Valid 6 w156.low w156.t w156.y w156.r w156.cap) (P33.root 6) :=
  Night6836Tree.sound w156 pick156 6 t567 _ (by decide +kernel)
theorem cov156_7 : PA.Covered 7 (OZ.Valid 7 w156.low w156.t w156.y w156.r w156.cap) (P33.root 7) :=
  Night6836Tree.sound w156 pick156 7 t2134 _ (by decide +kernel)
theorem window156 : P33.WindowCount w156 := by
  apply P33.window_count w156 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov156_1
  · exact cov156_2
  · exact cov156_3
  · exact cov156_4
  · exact cov156_5
  · exact cov156_6
  · exact cov156_7
def w157 : P33.Window := ⟨11,58,2563,2154,221733164215789134,128308,87000,5000000,81920000000⟩
def h157_0 : Height w157 := ⟨128308,87000,by decide +kernel⟩
def h157_1 : Height w157 := ⟨132325,84000,by decide +kernel⟩
def h157_2 : Height w157 := ⟨136609,81000,by decide +kernel⟩
def h157_3 : Height w157 := ⟨141206,78000,by decide +kernel⟩
def h157_4 : Height w157 := ⟨146170,75000,by decide +kernel⟩
def h157_5 : Height w157 := ⟨151572,72000,by decide +kernel⟩
def h157_6 : Height w157 := ⟨157499,69000,by decide +kernel⟩
def h157_7 : Height w157 := ⟨164065,66000,by decide +kernel⟩
def h157_8 : Height w157 := ⟨171419,63000,by decide +kernel⟩
def h157_9 : Height w157 := ⟨179757,60000,by decide +kernel⟩
def h157_10 : Height w157 := ⟨189349,57000,by decide +kernel⟩
def pick157 (cl : ℕ) : Height w157 := if cl<32 then (if cl<4 then (if cl<2 then (h157_0) else (h157_1)) else (if cl<6 then (h157_2) else (if cl<13 then (h157_3) else (h157_4)))) else (if cl<117 then (if cl<36 then (h157_5) else (if cl<62 then (h157_6) else (h157_7))) else (if cl<216 then (h157_8) else (if cl<334 then (h157_9) else (h157_10))))
private theorem k157_1_0 : check w157 pick157 1 t6582 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k157_1_1 : check w157 pick157 1 t5292 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k157_1_2 : check w157 pick157 1 t6583 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w157 pick157 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t6582 t5292 k157_1_0 k157_1_1
private theorem k157_1_3 : check w157 pick157 1 t6578 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k157_1_4 : check w157 pick157 1 t6584 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w157 pick157 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t6583 t6578 k157_1_2 k157_1_3
private theorem k157_1_5 : check w157 pick157 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k157_1_6 : check w157 pick157 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k157_1_7 : check w157 pick157 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w157 pick157 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k157_1_5 k157_1_6
private theorem k157_1_8 : check w157 pick157 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k157_1_9 : check w157 pick157 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w157 pick157 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k157_1_7 k157_1_8
private theorem k157_1_10 : check w157 pick157 1 t6585 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w157 pick157 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6584 t5276 k157_1_4 k157_1_9
theorem cov157_1 : PA.Covered 1 (OZ.Valid 1 w157.low w157.t w157.y w157.r w157.cap) (P33.root 1) :=
  Night6836Tree.sound w157 pick157 1 t6585 _ k157_1_10
theorem cov157_2 : PA.Covered 2 (OZ.Valid 2 w157.low w157.t w157.y w157.r w157.cap) (P33.root 2) :=
  Night6836Tree.sound w157 pick157 2 t6560 _ (by decide +kernel)
theorem cov157_3 : PA.Covered 3 (OZ.Valid 3 w157.low w157.t w157.y w157.r w157.cap) (P33.root 3) :=
  Night6836Tree.sound w157 pick157 3 t564 _ (by decide +kernel)
theorem cov157_4 : PA.Covered 4 (OZ.Valid 4 w157.low w157.t w157.y w157.r w157.cap) (P33.root 4) :=
  Night6836Tree.sound w157 pick157 4 t565 _ (by decide +kernel)
theorem cov157_5 : PA.Covered 5 (OZ.Valid 5 w157.low w157.t w157.y w157.r w157.cap) (P33.root 5) :=
  Night6836Tree.sound w157 pick157 5 t566 _ (by decide +kernel)
theorem cov157_6 : PA.Covered 6 (OZ.Valid 6 w157.low w157.t w157.y w157.r w157.cap) (P33.root 6) :=
  Night6836Tree.sound w157 pick157 6 t567 _ (by decide +kernel)
theorem cov157_7 : PA.Covered 7 (OZ.Valid 7 w157.low w157.t w157.y w157.r w157.cap) (P33.root 7) :=
  Night6836Tree.sound w157 pick157 7 t2134 _ (by decide +kernel)
theorem window157 : P33.WindowCount w157 := by
  apply P33.window_count w157 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov157_1
  · exact cov157_2
  · exact cov157_3
  · exact cov157_4
  · exact cov157_5
  · exact cov157_6
  · exact cov157_7
def w158 : P33.Window := ⟨11,59,2153,1729,237364054065523565,164184,108000,5000000,81920000000⟩
def h158_0 : Height w158 := ⟨164184,108000,by decide +kernel⟩
def h158_1 : Height w158 := ⟨168227,105000,by decide +kernel⟩
def h158_2 : Height w158 := ⟨172483,102000,by decide +kernel⟩
def h158_3 : Height w158 := ⟨176979,99000,by decide +kernel⟩
def h158_4 : Height w158 := ⟨181748,96000,by decide +kernel⟩
def h158_5 : Height w158 := ⟨186830,93000,by decide +kernel⟩
def h158_6 : Height w158 := ⟨192270,90000,by decide +kernel⟩
def h158_7 : Height w158 := ⟨198126,87000,by decide +kernel⟩
def h158_8 : Height w158 := ⟨204466,84000,by decide +kernel⟩
def h158_9 : Height w158 := ⟨211376,81000,by decide +kernel⟩
def h158_10 : Height w158 := ⟨218962,78000,by decide +kernel⟩
def h158_11 : Height w158 := ⟨227358,75000,by decide +kernel⟩
def h158_12 : Height w158 := ⟨236735,72000,by decide +kernel⟩
def pick158 (cl : ℕ) : Height w158 := if cl<32 then (if cl<5 then (if cl<2 then (h158_0) else (if cl<4 then (h158_1) else (h158_2))) else (if cl<10 then (h158_3) else (if cl<16 then (h158_4) else (h158_5)))) else (if cl<92 then (if cl<36 then (h158_6) else (if cl<49 then (h158_7) else (h158_8))) else (if cl<227 then (if cl<145 then (h158_9) else (h158_10)) else (if cl<312 then (h158_11) else (h158_12))))
private theorem k158_1_0 : check w158 pick158 1 t6582 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k158_1_1 : check w158 pick158 1 t5292 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k158_1_2 : check w158 pick158 1 t6583 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w158 pick158 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t6582 t5292 k158_1_0 k158_1_1
private theorem k158_1_3 : check w158 pick158 1 t6578 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k158_1_4 : check w158 pick158 1 t6584 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w158 pick158 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t6583 t6578 k158_1_2 k158_1_3
private theorem k158_1_5 : check w158 pick158 1 t6587 ⟨1,7,2,16,1,52,139,192⟩ = true := by decide +kernel
private theorem k158_1_6 : check w158 pick158 1 t6602 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k158_1_7 : check w158 pick158 1 t6610 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k158_1_8 : check w158 pick158 1 t6611 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w158 pick158 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6602 t6610 k158_1_6 k158_1_7
private theorem k158_1_9 : check w158 pick158 1 t6612 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w158 pick158 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t6587 t6611 k158_1_5 k158_1_8
private theorem k158_1_10 : check w158 pick158 1 t6613 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w158 pick158 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6584 t6612 k158_1_4 k158_1_9
theorem cov158_1 : PA.Covered 1 (OZ.Valid 1 w158.low w158.t w158.y w158.r w158.cap) (P33.root 1) :=
  Night6836Tree.sound w158 pick158 1 t6613 _ k158_1_10
theorem cov158_2 : PA.Covered 2 (OZ.Valid 2 w158.low w158.t w158.y w158.r w158.cap) (P33.root 2) :=
  Night6836Tree.sound w158 pick158 2 t6618 _ (by decide +kernel)
theorem cov158_3 : PA.Covered 3 (OZ.Valid 3 w158.low w158.t w158.y w158.r w158.cap) (P33.root 3) :=
  Night6836Tree.sound w158 pick158 3 t564 _ (by decide +kernel)
theorem cov158_4 : PA.Covered 4 (OZ.Valid 4 w158.low w158.t w158.y w158.r w158.cap) (P33.root 4) :=
  Night6836Tree.sound w158 pick158 4 t565 _ (by decide +kernel)
theorem cov158_5 : PA.Covered 5 (OZ.Valid 5 w158.low w158.t w158.y w158.r w158.cap) (P33.root 5) :=
  Night6836Tree.sound w158 pick158 5 t566 _ (by decide +kernel)
theorem cov158_6 : PA.Covered 6 (OZ.Valid 6 w158.low w158.t w158.y w158.r w158.cap) (P33.root 6) :=
  Night6836Tree.sound w158 pick158 6 t567 _ (by decide +kernel)
theorem cov158_7 : PA.Covered 7 (OZ.Valid 7 w158.low w158.t w158.y w158.r w158.cap) (P33.root 7) :=
  Night6836Tree.sound w158 pick158 7 t2134 _ (by decide +kernel)
theorem window158 : P33.WindowCount w158 := by
  apply P33.window_count w158 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov158_1
  · exact cov158_2
  · exact cov158_3
  · exact cov158_4
  · exact cov158_5
  · exact cov158_6
  · exact cov158_7
def w159 : P33.Window := ⟨11,60,1728,1689,200721518378172417,171597,111000,5000000,81920000000⟩
def h159_0 : Height w159 := ⟨171597,111000,by decide +kernel⟩
def h159_1 : Height w159 := ⟨175652,108000,by decide +kernel⟩
def h159_2 : Height w159 := ⟨179913,105000,by decide +kernel⟩
def h159_3 : Height w159 := ⟨184407,102000,by decide +kernel⟩
def h159_4 : Height w159 := ⟨189164,99000,by decide +kernel⟩
def h159_5 : Height w159 := ⟨194222,96000,by decide +kernel⟩
def h159_6 : Height w159 := ⟨205417,90000,by decide +kernel⟩
def h159_7 : Height w159 := ⟨211670,87000,by decide +kernel⟩
def h159_8 : Height w159 := ⟨218458,84000,by decide +kernel⟩
def h159_9 : Height w159 := ⟨225876,81000,by decide +kernel⟩
def h159_10 : Height w159 := ⟨234042,78000,by decide +kernel⟩
def h159_11 : Height w159 := ⟨243107,75000,by decide +kernel⟩
def h159_12 : Height w159 := ⟨253263,72000,by decide +kernel⟩
def pick159 (cl : ℕ) : Height w159 := if cl<32 then (if cl<5 then (if cl<2 then (h159_0) else (if cl<4 then (h159_1) else (h159_2))) else (if cl<10 then (h159_3) else (if cl<14 then (h159_4) else (h159_5)))) else (if cl<132 then (if cl<46 then (h159_6) else (if cl<83 then (h159_7) else (h159_8))) else (if cl<284 then (if cl<203 then (h159_9) else (h159_10)) else (if cl<561 then (h159_11) else (h159_12))))
private theorem k159_1_0 : check w159 pick159 1 t6582 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k159_1_1 : check w159 pick159 1 t6633 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k159_1_2 : check w159 pick159 1 t6634 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w159 pick159 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t6582 t6633 k159_1_0 k159_1_1
private theorem k159_1_3 : check w159 pick159 1 t6658 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k159_1_4 : check w159 pick159 1 t6659 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w159 pick159 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t6634 t6658 k159_1_2 k159_1_3
private theorem k159_1_5 : check w159 pick159 1 t6587 ⟨1,7,2,16,1,52,139,192⟩ = true := by decide +kernel
private theorem k159_1_6 : check w159 pick159 1 t6602 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k159_1_7 : check w159 pick159 1 t6610 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k159_1_8 : check w159 pick159 1 t6611 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w159 pick159 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6602 t6610 k159_1_6 k159_1_7
private theorem k159_1_9 : check w159 pick159 1 t6612 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w159 pick159 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t6587 t6611 k159_1_5 k159_1_8
private theorem k159_1_10 : check w159 pick159 1 t6660 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w159 pick159 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6659 t6612 k159_1_4 k159_1_9
theorem cov159_1 : PA.Covered 1 (OZ.Valid 1 w159.low w159.t w159.y w159.r w159.cap) (P33.root 1) :=
  Night6836Tree.sound w159 pick159 1 t6660 _ k159_1_10
theorem cov159_2 : PA.Covered 2 (OZ.Valid 2 w159.low w159.t w159.y w159.r w159.cap) (P33.root 2) :=
  Night6836Tree.sound w159 pick159 2 t6666 _ (by decide +kernel)
theorem cov159_3 : PA.Covered 3 (OZ.Valid 3 w159.low w159.t w159.y w159.r w159.cap) (P33.root 3) :=
  Night6836Tree.sound w159 pick159 3 t564 _ (by decide +kernel)
theorem cov159_4 : PA.Covered 4 (OZ.Valid 4 w159.low w159.t w159.y w159.r w159.cap) (P33.root 4) :=
  Night6836Tree.sound w159 pick159 4 t565 _ (by decide +kernel)
theorem cov159_5 : PA.Covered 5 (OZ.Valid 5 w159.low w159.t w159.y w159.r w159.cap) (P33.root 5) :=
  Night6836Tree.sound w159 pick159 5 t566 _ (by decide +kernel)
theorem cov159_6 : PA.Covered 6 (OZ.Valid 6 w159.low w159.t w159.y w159.r w159.cap) (P33.root 6) :=
  Night6836Tree.sound w159 pick159 6 t567 _ (by decide +kernel)
theorem cov159_7 : PA.Covered 7 (OZ.Valid 7 w159.low w159.t w159.y w159.r w159.cap) (P33.root 7) :=
  Night6836Tree.sound w159 pick159 7 t2134 _ (by decide +kernel)
theorem window159 : P33.WindowCount w159 := by
  apply P33.window_count w159 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov159_1
  · exact cov159_2
  · exact cov159_3
  · exact cov159_4
  · exact cov159_5
  · exact cov159_6
  · exact cov159_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w160 : P33.Window := ⟨12,18,7917,6918,202677022142859486,6454,19000,5000000,81920000000⟩
def h160_0 : Height w160 := ⟨6454,19000,by decide +kernel⟩
def h160_1 : Height w160 := ⟨13040,15000,by decide +kernel⟩
def h160_2 : Height w160 := ⟨35043,11000,by decide +kernel⟩
def pick160 (cl : ℕ) : Height w160 := if cl<14 then (h160_0) else (if cl<1021 then (h160_1) else (h160_2))
private theorem k160_1_0 : check w160 pick160 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k160_1_1 : check w160 pick160 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k160_1_2 : check w160 pick160 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w160 pick160 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k160_1_0 k160_1_1
private theorem k160_1_3 : check w160 pick160 1 t6748 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k160_1_4 : check w160 pick160 1 t6792 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k160_1_5 : check w160 pick160 1 t6793 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w160 pick160 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t6748 t6792 k160_1_3 k160_1_4
private theorem k160_1_6 : check w160 pick160 1 t6794 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w160 pick160 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t6793 k160_1_2 k160_1_5
private theorem k160_1_7 : check w160 pick160 1 t6841 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k160_1_8 : check w160 pick160 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k160_1_9 : check w160 pick160 1 t6873 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w160 pick160 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t6841 t6872 k160_1_7 k160_1_8
private theorem k160_1_10 : check w160 pick160 1 t6924 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k160_1_11 : check w160 pick160 1 t6960 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k160_1_12 : check w160 pick160 1 t6961 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w160 pick160 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6924 t6960 k160_1_10 k160_1_11
private theorem k160_1_13 : check w160 pick160 1 t6962 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w160 pick160 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t6873 t6961 k160_1_9 k160_1_12
private theorem k160_1_14 : check w160 pick160 1 t6963 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w160 pick160 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t6794 t6962 k160_1_6 k160_1_13
theorem cov160_1 : PA.Covered 1 (OZ.Valid 1 w160.low w160.t w160.y w160.r w160.cap) (P33.root 1) :=
  Night6836Tree.sound w160 pick160 1 t6963 _ k160_1_14
private theorem k160_2_0 : check w160 pick160 2 t6967 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k160_2_1 : check w160 pick160 2 t6983 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k160_2_2 : check w160 pick160 2 t6984 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w160 pick160 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t6967 t6983 k160_2_0 k160_2_1
theorem cov160_2 : PA.Covered 2 (OZ.Valid 2 w160.low w160.t w160.y w160.r w160.cap) (P33.root 2) :=
  Night6836Tree.sound w160 pick160 2 t6984 _ k160_2_2
theorem cov160_3 : PA.Covered 3 (OZ.Valid 3 w160.low w160.t w160.y w160.r w160.cap) (P33.root 3) :=
  Night6836Tree.sound w160 pick160 3 t564 _ (by decide +kernel)
theorem cov160_4 : PA.Covered 4 (OZ.Valid 4 w160.low w160.t w160.y w160.r w160.cap) (P33.root 4) :=
  Night6836Tree.sound w160 pick160 4 t565 _ (by decide +kernel)
theorem cov160_5 : PA.Covered 5 (OZ.Valid 5 w160.low w160.t w160.y w160.r w160.cap) (P33.root 5) :=
  Night6836Tree.sound w160 pick160 5 t566 _ (by decide +kernel)
theorem cov160_6 : PA.Covered 6 (OZ.Valid 6 w160.low w160.t w160.y w160.r w160.cap) (P33.root 6) :=
  Night6836Tree.sound w160 pick160 6 t567 _ (by decide +kernel)
theorem cov160_7 : PA.Covered 7 (OZ.Valid 7 w160.low w160.t w160.y w160.r w160.cap) (P33.root 7) :=
  Night6836Tree.sound w160 pick160 7 t568 _ (by decide +kernel)
theorem window160 : P33.WindowCount w160 := by
  apply P33.window_count w160 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov160_1
  · exact cov160_2
  · exact cov160_3
  · exact cov160_4
  · exact cov160_5
  · exact cov160_6
  · exact cov160_7
def w161 : P33.Window := ⟨12,19,7415,6466,241036071855432865,7508,21000,5000000,81920000000⟩
def h161_0 : Height w161 := ⟨7508,21000,by decide +kernel⟩
def h161_1 : Height w161 := ⟨11735,18000,by decide +kernel⟩
def h161_2 : Height w161 := ⟨18802,15000,by decide +kernel⟩
def pick161 (cl : ℕ) : Height w161 := if cl<4 then (h161_0) else (if cl<100 then (h161_1) else (h161_2))
private theorem k161_1_0 : check w161 pick161 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k161_1_1 : check w161 pick161 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k161_1_2 : check w161 pick161 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w161 pick161 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k161_1_0 k161_1_1
private theorem k161_1_3 : check w161 pick161 1 t7064 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k161_1_4 : check w161 pick161 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k161_1_5 : check w161 pick161 1 t7098 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w161 pick161 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7064 t7097 k161_1_3 k161_1_4
private theorem k161_1_6 : check w161 pick161 1 t7099 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w161 pick161 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t7098 k161_1_2 k161_1_5
theorem cov161_1 : PA.Covered 1 (OZ.Valid 1 w161.low w161.t w161.y w161.r w161.cap) (P33.root 1) :=
  Night6836Tree.sound w161 pick161 1 t7099 _ k161_1_6
theorem cov161_2 : PA.Covered 2 (OZ.Valid 2 w161.low w161.t w161.y w161.r w161.cap) (P33.root 2) :=
  Night6836Tree.sound w161 pick161 2 t5320 _ (by decide +kernel)
theorem cov161_3 : PA.Covered 3 (OZ.Valid 3 w161.low w161.t w161.y w161.r w161.cap) (P33.root 3) :=
  Night6836Tree.sound w161 pick161 3 t564 _ (by decide +kernel)
theorem cov161_4 : PA.Covered 4 (OZ.Valid 4 w161.low w161.t w161.y w161.r w161.cap) (P33.root 4) :=
  Night6836Tree.sound w161 pick161 4 t565 _ (by decide +kernel)
theorem cov161_5 : PA.Covered 5 (OZ.Valid 5 w161.low w161.t w161.y w161.r w161.cap) (P33.root 5) :=
  Night6836Tree.sound w161 pick161 5 t566 _ (by decide +kernel)
theorem cov161_6 : PA.Covered 6 (OZ.Valid 6 w161.low w161.t w161.y w161.r w161.cap) (P33.root 6) :=
  Night6836Tree.sound w161 pick161 6 t567 _ (by decide +kernel)
theorem cov161_7 : PA.Covered 7 (OZ.Valid 7 w161.low w161.t w161.y w161.r w161.cap) (P33.root 7) :=
  Night6836Tree.sound w161 pick161 7 t568 _ (by decide +kernel)
theorem window161 : P33.WindowCount w161 := by
  apply P33.window_count w161 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov161_1
  · exact cov161_2
  · exact cov161_3
  · exact cov161_4
  · exact cov161_5
  · exact cov161_6
  · exact cov161_7
def w162 : P33.Window := ⟨12,19,7550,7512,239355599842050693,6553,18000,5000000,81920000000⟩
def h162_0 : Height w162 := ⟨6553,18000,by decide +kernel⟩
def h162_1 : Height w162 := ⟨10995,15000,by decide +kernel⟩
def h162_2 : Height w162 := ⟨19799,12000,by decide +kernel⟩
def pick162 (cl : ℕ) : Height w162 := if cl<5 then (h162_0) else (if cl<302 then (h162_1) else (h162_2))
private theorem k162_1_0 : check w162 pick162 1 t7116 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k162_1_1 : check w162 pick162 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k162_1_2 : check w162 pick162 1 t7117 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w162 pick162 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7116 t7032 k162_1_0 k162_1_1
private theorem k162_1_3 : check w162 pick162 1 t7064 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k162_1_4 : check w162 pick162 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k162_1_5 : check w162 pick162 1 t7098 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w162 pick162 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7064 t7097 k162_1_3 k162_1_4
private theorem k162_1_6 : check w162 pick162 1 t7118 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w162 pick162 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7117 t7098 k162_1_2 k162_1_5
theorem cov162_1 : PA.Covered 1 (OZ.Valid 1 w162.low w162.t w162.y w162.r w162.cap) (P33.root 1) :=
  Night6836Tree.sound w162 pick162 1 t7118 _ k162_1_6
theorem cov162_2 : PA.Covered 2 (OZ.Valid 2 w162.low w162.t w162.y w162.r w162.cap) (P33.root 2) :=
  Night6836Tree.sound w162 pick162 2 t5320 _ (by decide +kernel)
theorem cov162_3 : PA.Covered 3 (OZ.Valid 3 w162.low w162.t w162.y w162.r w162.cap) (P33.root 3) :=
  Night6836Tree.sound w162 pick162 3 t564 _ (by decide +kernel)
theorem cov162_4 : PA.Covered 4 (OZ.Valid 4 w162.low w162.t w162.y w162.r w162.cap) (P33.root 4) :=
  Night6836Tree.sound w162 pick162 4 t565 _ (by decide +kernel)
theorem cov162_5 : PA.Covered 5 (OZ.Valid 5 w162.low w162.t w162.y w162.r w162.cap) (P33.root 5) :=
  Night6836Tree.sound w162 pick162 5 t566 _ (by decide +kernel)
theorem cov162_6 : PA.Covered 6 (OZ.Valid 6 w162.low w162.t w162.y w162.r w162.cap) (P33.root 6) :=
  Night6836Tree.sound w162 pick162 6 t567 _ (by decide +kernel)
theorem cov162_7 : PA.Covered 7 (OZ.Valid 7 w162.low w162.t w162.y w162.r w162.cap) (P33.root 7) :=
  Night6836Tree.sound w162 pick162 7 t568 _ (by decide +kernel)
theorem window162 : P33.WindowCount w162 := by
  apply P33.window_count w162 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov162_1
  · exact cov162_2
  · exact cov162_3
  · exact cov162_4
  · exact cov162_5
  · exact cov162_6
  · exact cov162_7
def w163 : P33.Window := ⟨12,20,7219,6220,203889305257205078,7880,23000,5000000,81920000000⟩
def h163_0 : Height w163 := ⟨7880,23000,by decide +kernel⟩
def h163_1 : Height w163 := ⟨13343,19000,by decide +kernel⟩
def h163_2 : Height w163 := ⟨23929,15000,by decide +kernel⟩
def pick163 (cl : ℕ) : Height w163 := if cl<2 then (h163_0) else (if cl<173 then (h163_1) else (h163_2))
private theorem k163_1_0 : check w163 pick163 1 t7124 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k163_1_1 : check w163 pick163 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k163_1_2 : check w163 pick163 1 t7132 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w163 pick163 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7124 t7131 k163_1_0 k163_1_1
private theorem k163_1_3 : check w163 pick163 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k163_1_4 : check w163 pick163 1 t7174 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k163_1_5 : check w163 pick163 1 t7175 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w163 pick163 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7174 k163_1_3 k163_1_4
private theorem k163_1_6 : check w163 pick163 1 t7176 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w163 pick163 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7132 t7175 k163_1_2 k163_1_5
private theorem k163_1_7 : check w163 pick163 1 t7179 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k163_1_8 : check w163 pick163 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k163_1_9 : check w163 pick163 1 t7180 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w163 pick163 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7179 t6872 k163_1_7 k163_1_8
private theorem k163_1_10 : check w163 pick163 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k163_1_11 : check w163 pick163 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k163_1_12 : check w163 pick163 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w163 pick163 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k163_1_10 k163_1_11
private theorem k163_1_13 : check w163 pick163 1 t7191 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w163 pick163 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7180 t7190 k163_1_9 k163_1_12
private theorem k163_1_14 : check w163 pick163 1 t7192 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w163 pick163 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7176 t7191 k163_1_6 k163_1_13
theorem cov163_1 : PA.Covered 1 (OZ.Valid 1 w163.low w163.t w163.y w163.r w163.cap) (P33.root 1) :=
  Night6836Tree.sound w163 pick163 1 t7192 _ k163_1_14
private theorem k163_2_0 : check w163 pick163 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k163_2_1 : check w163 pick163 2 t7203 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k163_2_2 : check w163 pick163 2 t7204 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w163 pick163 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t7203 k163_2_0 k163_2_1
theorem cov163_2 : PA.Covered 2 (OZ.Valid 2 w163.low w163.t w163.y w163.r w163.cap) (P33.root 2) :=
  Night6836Tree.sound w163 pick163 2 t7204 _ k163_2_2
theorem cov163_3 : PA.Covered 3 (OZ.Valid 3 w163.low w163.t w163.y w163.r w163.cap) (P33.root 3) :=
  Night6836Tree.sound w163 pick163 3 t564 _ (by decide +kernel)
theorem cov163_4 : PA.Covered 4 (OZ.Valid 4 w163.low w163.t w163.y w163.r w163.cap) (P33.root 4) :=
  Night6836Tree.sound w163 pick163 4 t565 _ (by decide +kernel)
theorem cov163_5 : PA.Covered 5 (OZ.Valid 5 w163.low w163.t w163.y w163.r w163.cap) (P33.root 5) :=
  Night6836Tree.sound w163 pick163 5 t566 _ (by decide +kernel)
theorem cov163_6 : PA.Covered 6 (OZ.Valid 6 w163.low w163.t w163.y w163.r w163.cap) (P33.root 6) :=
  Night6836Tree.sound w163 pick163 6 t567 _ (by decide +kernel)
theorem cov163_7 : PA.Covered 7 (OZ.Valid 7 w163.low w163.t w163.y w163.r w163.cap) (P33.root 7) :=
  Night6836Tree.sound w163 pick163 7 t568 _ (by decide +kernel)
theorem window163 : P33.WindowCount w163 := by
  apply P33.window_count w163 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov163_1
  · exact cov163_2
  · exact cov163_3
  · exact cov163_4
  · exact cov163_5
  · exact cov163_6
  · exact cov163_7
def w164 : P33.Window := ⟨12,20,7511,7393,243003481632196534,8238,18000,5000000,81920000000⟩
def h164_0 : Height w164 := ⟨8238,18000,by decide +kernel⟩
def h164_1 : Height w164 := ⟨13111,15000,by decide +kernel⟩
def h164_2 : Height w164 := ⟨23141,12000,by decide +kernel⟩
def pick164 (cl : ℕ) : Height w164 := if cl<12 then (h164_0) else (if cl<494 then (h164_1) else (h164_2))
private theorem k164_1_0 : check w164 pick164 1 t7212 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k164_1_1 : check w164 pick164 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k164_1_2 : check w164 pick164 1 t7213 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w164 pick164 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7212 t7032 k164_1_0 k164_1_1
private theorem k164_1_3 : check w164 pick164 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k164_1_4 : check w164 pick164 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k164_1_5 : check w164 pick164 1 t7219 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w164 pick164 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t7097 k164_1_3 k164_1_4
private theorem k164_1_6 : check w164 pick164 1 t7220 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w164 pick164 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7213 t7219 k164_1_2 k164_1_5
theorem cov164_1 : PA.Covered 1 (OZ.Valid 1 w164.low w164.t w164.y w164.r w164.cap) (P33.root 1) :=
  Night6836Tree.sound w164 pick164 1 t7220 _ k164_1_6
theorem cov164_2 : PA.Covered 2 (OZ.Valid 2 w164.low w164.t w164.y w164.r w164.cap) (P33.root 2) :=
  Night6836Tree.sound w164 pick164 2 t7224 _ (by decide +kernel)
theorem cov164_3 : PA.Covered 3 (OZ.Valid 3 w164.low w164.t w164.y w164.r w164.cap) (P33.root 3) :=
  Night6836Tree.sound w164 pick164 3 t564 _ (by decide +kernel)
theorem cov164_4 : PA.Covered 4 (OZ.Valid 4 w164.low w164.t w164.y w164.r w164.cap) (P33.root 4) :=
  Night6836Tree.sound w164 pick164 4 t565 _ (by decide +kernel)
theorem cov164_5 : PA.Covered 5 (OZ.Valid 5 w164.low w164.t w164.y w164.r w164.cap) (P33.root 5) :=
  Night6836Tree.sound w164 pick164 5 t566 _ (by decide +kernel)
theorem cov164_6 : PA.Covered 6 (OZ.Valid 6 w164.low w164.t w164.y w164.r w164.cap) (P33.root 6) :=
  Night6836Tree.sound w164 pick164 6 t567 _ (by decide +kernel)
theorem cov164_7 : PA.Covered 7 (OZ.Valid 7 w164.low w164.t w164.y w164.r w164.cap) (P33.root 7) :=
  Night6836Tree.sound w164 pick164 7 t568 _ (by decide +kernel)
theorem window164 : P33.WindowCount w164 := by
  apply P33.window_count w164 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov164_1
  · exact cov164_2
  · exact cov164_3
  · exact cov164_4
  · exact cov164_5
  · exact cov164_6
  · exact cov164_7
def w165 : P33.Window := ⟨12,21,7472,7433,243880445513076982,9288,18000,5000000,81920000000⟩
def h165_0 : Height w165 := ⟨9288,18000,by decide +kernel⟩
def h165_1 : Height w165 := ⟨14324,15000,by decide +kernel⟩
def h165_2 : Height w165 := ⟨24702,12000,by decide +kernel⟩
def pick165 (cl : ℕ) : Height w165 := if cl<14 then (h165_0) else (if cl<644 then (h165_1) else (h165_2))
private theorem k165_1_0 : check w165 pick165 1 t7229 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k165_1_1 : check w165 pick165 1 t7234 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k165_1_2 : check w165 pick165 1 t7235 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w165 pick165 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7229 t7234 k165_1_0 k165_1_1
private theorem k165_1_3 : check w165 pick165 1 t7241 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k165_1_4 : check w165 pick165 1 t7258 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k165_1_5 : check w165 pick165 1 t7259 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w165 pick165 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t7241 t7258 k165_1_3 k165_1_4
private theorem k165_1_6 : check w165 pick165 1 t7260 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w165 pick165 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t7235 t7259 k165_1_2 k165_1_5
private theorem k165_1_7 : check w165 pick165 1 t7279 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k165_1_8 : check w165 pick165 1 t7295 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k165_1_9 : check w165 pick165 1 t7296 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w165 pick165 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t7279 t7295 k165_1_7 k165_1_8
private theorem k165_1_10 : check w165 pick165 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k165_1_11 : check w165 pick165 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k165_1_12 : check w165 pick165 1 t7319 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w165 pick165 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t7318 k165_1_10 k165_1_11
private theorem k165_1_13 : check w165 pick165 1 t7320 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w165 pick165 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t7296 t7319 k165_1_9 k165_1_12
private theorem k165_1_14 : check w165 pick165 1 t7321 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w165 pick165 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t7260 t7320 k165_1_6 k165_1_13
theorem cov165_1 : PA.Covered 1 (OZ.Valid 1 w165.low w165.t w165.y w165.r w165.cap) (P33.root 1) :=
  Night6836Tree.sound w165 pick165 1 t7321 _ k165_1_14
theorem cov165_2 : PA.Covered 2 (OZ.Valid 2 w165.low w165.t w165.y w165.r w165.cap) (P33.root 2) :=
  Night6836Tree.sound w165 pick165 2 t7324 _ (by decide +kernel)
theorem cov165_3 : PA.Covered 3 (OZ.Valid 3 w165.low w165.t w165.y w165.r w165.cap) (P33.root 3) :=
  Night6836Tree.sound w165 pick165 3 t564 _ (by decide +kernel)
theorem cov165_4 : PA.Covered 4 (OZ.Valid 4 w165.low w165.t w165.y w165.r w165.cap) (P33.root 4) :=
  Night6836Tree.sound w165 pick165 4 t565 _ (by decide +kernel)
theorem cov165_5 : PA.Covered 5 (OZ.Valid 5 w165.low w165.t w165.y w165.r w165.cap) (P33.root 5) :=
  Night6836Tree.sound w165 pick165 5 t566 _ (by decide +kernel)
theorem cov165_6 : PA.Covered 6 (OZ.Valid 6 w165.low w165.t w165.y w165.r w165.cap) (P33.root 6) :=
  Night6836Tree.sound w165 pick165 6 t567 _ (by decide +kernel)
theorem cov165_7 : PA.Covered 7 (OZ.Valid 7 w165.low w165.t w165.y w165.r w165.cap) (P33.root 7) :=
  Night6836Tree.sound w165 pick165 7 t568 _ (by decide +kernel)
theorem window165 : P33.WindowCount w165 := by
  apply P33.window_count w165 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov165_1
  · exact cov165_2
  · exact cov165_3
  · exact cov165_4
  · exact cov165_5
  · exact cov165_6
  · exact cov165_7
def w166 : P33.Window := ⟨12,22,5821,4822,201710496734721194,17247,27000,5000000,81920000000⟩
def h166_0 : Height w166 := ⟨17247,27000,by decide +kernel⟩
def h166_1 : Height w166 := ⟨24575,23000,by decide +kernel⟩
def h166_2 : Height w166 := ⟨38297,19000,by decide +kernel⟩
def pick166 (cl : ℕ) : Height w166 := if cl<32 then (h166_0) else (if cl<644 then (h166_1) else (h166_2))
private theorem k166_1_0 : check w166 pick166 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k166_1_1 : check w166 pick166 1 t7326 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k166_1_2 : check w166 pick166 1 t7327 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w166 pick166 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7326 k166_1_0 k166_1_1
private theorem k166_1_3 : check w166 pick166 1 t7064 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k166_1_4 : check w166 pick166 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k166_1_5 : check w166 pick166 1 t7098 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w166 pick166 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7064 t7097 k166_1_3 k166_1_4
private theorem k166_1_6 : check w166 pick166 1 t7328 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w166 pick166 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7327 t7098 k166_1_2 k166_1_5
theorem cov166_1 : PA.Covered 1 (OZ.Valid 1 w166.low w166.t w166.y w166.r w166.cap) (P33.root 1) :=
  Night6836Tree.sound w166 pick166 1 t7328 _ k166_1_6
theorem cov166_2 : PA.Covered 2 (OZ.Valid 2 w166.low w166.t w166.y w166.r w166.cap) (P33.root 2) :=
  Night6836Tree.sound w166 pick166 2 t7224 _ (by decide +kernel)
theorem cov166_3 : PA.Covered 3 (OZ.Valid 3 w166.low w166.t w166.y w166.r w166.cap) (P33.root 3) :=
  Night6836Tree.sound w166 pick166 3 t564 _ (by decide +kernel)
theorem cov166_4 : PA.Covered 4 (OZ.Valid 4 w166.low w166.t w166.y w166.r w166.cap) (P33.root 4) :=
  Night6836Tree.sound w166 pick166 4 t565 _ (by decide +kernel)
theorem cov166_5 : PA.Covered 5 (OZ.Valid 5 w166.low w166.t w166.y w166.r w166.cap) (P33.root 5) :=
  Night6836Tree.sound w166 pick166 5 t566 _ (by decide +kernel)
theorem cov166_6 : PA.Covered 6 (OZ.Valid 6 w166.low w166.t w166.y w166.r w166.cap) (P33.root 6) :=
  Night6836Tree.sound w166 pick166 6 t567 _ (by decide +kernel)
theorem cov166_7 : PA.Covered 7 (OZ.Valid 7 w166.low w166.t w166.y w166.r w166.cap) (P33.root 7) :=
  Night6836Tree.sound w166 pick166 7 t2134 _ (by decide +kernel)
theorem window166 : P33.WindowCount w166 := by
  apply P33.window_count w166 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov166_1
  · exact cov166_2
  · exact cov166_3
  · exact cov166_4
  · exact cov166_5
  · exact cov166_6
  · exact cov166_7
def w167 : P33.Window := ⟨12,22,7432,7393,244416771300464249,10698,18000,5000000,81920000000⟩
def h167_0 : Height w167 := ⟨10698,18000,by decide +kernel⟩
def h167_1 : Height w167 := ⟨16049,15000,by decide +kernel⟩
def h167_2 : Height w167 := ⟨27277,12000,by decide +kernel⟩
def pick167 (cl : ℕ) : Height w167 := if cl<32 then (h167_0) else (if cl<853 then (h167_1) else (h167_2))
private theorem k167_1_0 : check w167 pick167 1 t7338 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k167_1_1 : check w167 pick167 1 t7341 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k167_1_2 : check w167 pick167 1 t7342 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w167 pick167 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7338 t7341 k167_1_0 k167_1_1
private theorem k167_1_3 : check w167 pick167 1 t7345 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k167_1_4 : check w167 pick167 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k167_1_5 : check w167 pick167 1 t7349 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w167 pick167 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t7345 t7348 k167_1_3 k167_1_4
private theorem k167_1_6 : check w167 pick167 1 t7350 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w167 pick167 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t7342 t7349 k167_1_2 k167_1_5
private theorem k167_1_7 : check w167 pick167 1 t7356 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k167_1_8 : check w167 pick167 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k167_1_9 : check w167 pick167 1 t7363 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w167 pick167 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7356 t7362 k167_1_7 k167_1_8
private theorem k167_1_10 : check w167 pick167 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k167_1_11 : check w167 pick167 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k167_1_12 : check w167 pick167 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w167 pick167 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k167_1_10 k167_1_11
private theorem k167_1_13 : check w167 pick167 1 t7370 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w167 pick167 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7363 t7369 k167_1_9 k167_1_12
private theorem k167_1_14 : check w167 pick167 1 t7371 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w167 pick167 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7350 t7370 k167_1_6 k167_1_13
theorem cov167_1 : PA.Covered 1 (OZ.Valid 1 w167.low w167.t w167.y w167.r w167.cap) (P33.root 1) :=
  Night6836Tree.sound w167 pick167 1 t7371 _ k167_1_14
theorem cov167_2 : PA.Covered 2 (OZ.Valid 2 w167.low w167.t w167.y w167.r w167.cap) (P33.root 2) :=
  Night6836Tree.sound w167 pick167 2 t7377 _ (by decide +kernel)
theorem cov167_3 : PA.Covered 3 (OZ.Valid 3 w167.low w167.t w167.y w167.r w167.cap) (P33.root 3) :=
  Night6836Tree.sound w167 pick167 3 t564 _ (by decide +kernel)
theorem cov167_4 : PA.Covered 4 (OZ.Valid 4 w167.low w167.t w167.y w167.r w167.cap) (P33.root 4) :=
  Night6836Tree.sound w167 pick167 4 t565 _ (by decide +kernel)
theorem cov167_5 : PA.Covered 5 (OZ.Valid 5 w167.low w167.t w167.y w167.r w167.cap) (P33.root 5) :=
  Night6836Tree.sound w167 pick167 5 t566 _ (by decide +kernel)
theorem cov167_6 : PA.Covered 6 (OZ.Valid 6 w167.low w167.t w167.y w167.r w167.cap) (P33.root 6) :=
  Night6836Tree.sound w167 pick167 6 t567 _ (by decide +kernel)
theorem cov167_7 : PA.Covered 7 (OZ.Valid 7 w167.low w167.t w167.y w167.r w167.cap) (P33.root 7) :=
  Night6836Tree.sound w167 pick167 7 t568 _ (by decide +kernel)
theorem window167 : P33.WindowCount w167 := by
  apply P33.window_count w167 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov167_1
  · exact cov167_2
  · exact cov167_3
  · exact cov167_4
  · exact cov167_5
  · exact cov167_6
  · exact cov167_7
def w168 : P33.Window := ⟨12,23,7392,7352,244122290885594015,12140,18000,5000000,81920000000⟩
def h168_0 : Height w168 := ⟨12140,18000,by decide +kernel⟩
def h168_1 : Height w168 := ⟨17821,15000,by decide +kernel⟩
def h168_2 : Height w168 := ⟨29950,12000,by decide +kernel⟩
def pick168 (cl : ℕ) : Height w168 := if cl<32 then (h168_0) else (if cl<922 then (h168_1) else (h168_2))
private theorem k168_1_0 : check w168 pick168 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k168_1_1 : check w168 pick168 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k168_1_2 : check w168 pick168 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w168 pick168 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k168_1_0 k168_1_1
private theorem k168_1_3 : check w168 pick168 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k168_1_4 : check w168 pick168 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k168_1_5 : check w168 pick168 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w168 pick168 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k168_1_3 k168_1_4
private theorem k168_1_6 : check w168 pick168 1 t7382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w168 pick168 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7381 k168_1_2 k168_1_5
private theorem k168_1_7 : check w168 pick168 1 t7386 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k168_1_8 : check w168 pick168 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k168_1_9 : check w168 pick168 1 t7387 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w168 pick168 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7386 t7362 k168_1_7 k168_1_8
private theorem k168_1_10 : check w168 pick168 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k168_1_11 : check w168 pick168 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k168_1_12 : check w168 pick168 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w168 pick168 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k168_1_10 k168_1_11
private theorem k168_1_13 : check w168 pick168 1 t7388 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w168 pick168 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7387 t7369 k168_1_9 k168_1_12
private theorem k168_1_14 : check w168 pick168 1 t7389 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w168 pick168 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7382 t7388 k168_1_6 k168_1_13
theorem cov168_1 : PA.Covered 1 (OZ.Valid 1 w168.low w168.t w168.y w168.r w168.cap) (P33.root 1) :=
  Night6836Tree.sound w168 pick168 1 t7389 _ k168_1_14
theorem cov168_2 : PA.Covered 2 (OZ.Valid 2 w168.low w168.t w168.y w168.r w168.cap) (P33.root 2) :=
  Night6836Tree.sound w168 pick168 2 t7392 _ (by decide +kernel)
theorem cov168_3 : PA.Covered 3 (OZ.Valid 3 w168.low w168.t w168.y w168.r w168.cap) (P33.root 3) :=
  Night6836Tree.sound w168 pick168 3 t564 _ (by decide +kernel)
theorem cov168_4 : PA.Covered 4 (OZ.Valid 4 w168.low w168.t w168.y w168.r w168.cap) (P33.root 4) :=
  Night6836Tree.sound w168 pick168 4 t565 _ (by decide +kernel)
theorem cov168_5 : PA.Covered 5 (OZ.Valid 5 w168.low w168.t w168.y w168.r w168.cap) (P33.root 5) :=
  Night6836Tree.sound w168 pick168 5 t566 _ (by decide +kernel)
theorem cov168_6 : PA.Covered 6 (OZ.Valid 6 w168.low w168.t w168.y w168.r w168.cap) (P33.root 6) :=
  Night6836Tree.sound w168 pick168 6 t567 _ (by decide +kernel)
theorem cov168_7 : PA.Covered 7 (OZ.Valid 7 w168.low w168.t w168.y w168.r w168.cap) (P33.root 7) :=
  Night6836Tree.sound w168 pick168 7 t568 _ (by decide +kernel)
theorem window168 : P33.WindowCount w168 := by
  apply P33.window_count w168 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov168_1
  · exact cov168_2
  · exact cov168_3
  · exact cov168_4
  · exact cov168_5
  · exact cov168_6
  · exact cov168_7
def w169 : P33.Window := ⟨12,24,5823,4824,203835691121608053,15642,31000,5000000,81920000000⟩
def h169_0 : Height w169 := ⟨15642,31000,by decide +kernel⟩
def h169_1 : Height w169 := ⟨21055,27000,by decide +kernel⟩
def h169_2 : Height w169 := ⟨29028,23000,by decide +kernel⟩
def h169_3 : Height w169 := ⟨44150,19000,by decide +kernel⟩
def pick169 (cl : ℕ) : Height w169 := if cl<37 then (if cl<2 then (h169_0) else (h169_1)) else (if cl<853 then (h169_2) else (h169_3))
private theorem k169_1_0 : check w169 pick169 1 t7393 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k169_1_1 : check w169 pick169 1 t575 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k169_1_2 : check w169 pick169 1 t7394 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w169 pick169 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7393 t575 k169_1_0 k169_1_1
private theorem k169_1_3 : check w169 pick169 1 t7400 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k169_1_4 : check w169 pick169 1 t7403 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k169_1_5 : check w169 pick169 1 t7404 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w169 pick169 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7400 t7403 k169_1_3 k169_1_4
private theorem k169_1_6 : check w169 pick169 1 t7405 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w169 pick169 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7394 t7404 k169_1_2 k169_1_5
private theorem k169_1_7 : check w169 pick169 1 t7412 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k169_1_8 : check w169 pick169 1 t7295 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k169_1_9 : check w169 pick169 1 t7413 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w169 pick169 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7412 t7295 k169_1_7 k169_1_8
private theorem k169_1_10 : check w169 pick169 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k169_1_11 : check w169 pick169 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k169_1_12 : check w169 pick169 1 t7319 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w169 pick169 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t7318 k169_1_10 k169_1_11
private theorem k169_1_13 : check w169 pick169 1 t7414 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w169 pick169 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7413 t7319 k169_1_9 k169_1_12
private theorem k169_1_14 : check w169 pick169 1 t7415 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w169 pick169 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7405 t7414 k169_1_6 k169_1_13
theorem cov169_1 : PA.Covered 1 (OZ.Valid 1 w169.low w169.t w169.y w169.r w169.cap) (P33.root 1) :=
  Night6836Tree.sound w169 pick169 1 t7415 _ k169_1_14
theorem cov169_2 : PA.Covered 2 (OZ.Valid 2 w169.low w169.t w169.y w169.r w169.cap) (P33.root 2) :=
  Night6836Tree.sound w169 pick169 2 t5379 _ (by decide +kernel)
theorem cov169_3 : PA.Covered 3 (OZ.Valid 3 w169.low w169.t w169.y w169.r w169.cap) (P33.root 3) :=
  Night6836Tree.sound w169 pick169 3 t564 _ (by decide +kernel)
theorem cov169_4 : PA.Covered 4 (OZ.Valid 4 w169.low w169.t w169.y w169.r w169.cap) (P33.root 4) :=
  Night6836Tree.sound w169 pick169 4 t565 _ (by decide +kernel)
theorem cov169_5 : PA.Covered 5 (OZ.Valid 5 w169.low w169.t w169.y w169.r w169.cap) (P33.root 5) :=
  Night6836Tree.sound w169 pick169 5 t566 _ (by decide +kernel)
theorem cov169_6 : PA.Covered 6 (OZ.Valid 6 w169.low w169.t w169.y w169.r w169.cap) (P33.root 6) :=
  Night6836Tree.sound w169 pick169 6 t567 _ (by decide +kernel)
theorem cov169_7 : PA.Covered 7 (OZ.Valid 7 w169.low w169.t w169.y w169.r w169.cap) (P33.root 7) :=
  Night6836Tree.sound w169 pick169 7 t2134 _ (by decide +kernel)
theorem window169 : P33.WindowCount w169 := by
  apply P33.window_count w169 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov169_1
  · exact cov169_2
  · exact cov169_3
  · exact cov169_4
  · exact cov169_5
  · exact cov169_6
  · exact cov169_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w170 : P33.Window := ⟨12,24,7351,7311,237051844361846568,9702,21000,5000000,81920000000⟩
def h170_0 : Height w170 := ⟨9702,21000,by decide +kernel⟩
def h170_1 : Height w170 := ⟨13612,18000,by decide +kernel⟩
def h170_2 : Height w170 := ⟨19637,15000,by decide +kernel⟩
def h170_3 : Height w170 := ⟨32714,12000,by decide +kernel⟩
def pick170 (cl : ℕ) : Height w170 := if cl<40 then (if cl<2 then (h170_0) else (h170_1)) else (if cl<961 then (h170_2) else (h170_3))
private theorem k170_1_0 : check w170 pick170 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k170_1_1 : check w170 pick170 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k170_1_2 : check w170 pick170 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w170 pick170 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k170_1_0 k170_1_1
private theorem k170_1_3 : check w170 pick170 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k170_1_4 : check w170 pick170 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k170_1_5 : check w170 pick170 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w170 pick170 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k170_1_3 k170_1_4
private theorem k170_1_6 : check w170 pick170 1 t7382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w170 pick170 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7381 k170_1_2 k170_1_5
private theorem k170_1_7 : check w170 pick170 1 t7386 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k170_1_8 : check w170 pick170 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k170_1_9 : check w170 pick170 1 t7387 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w170 pick170 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7386 t7362 k170_1_7 k170_1_8
private theorem k170_1_10 : check w170 pick170 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k170_1_11 : check w170 pick170 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k170_1_12 : check w170 pick170 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w170 pick170 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k170_1_10 k170_1_11
private theorem k170_1_13 : check w170 pick170 1 t7388 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w170 pick170 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7387 t7369 k170_1_9 k170_1_12
private theorem k170_1_14 : check w170 pick170 1 t7389 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w170 pick170 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7382 t7388 k170_1_6 k170_1_13
theorem cov170_1 : PA.Covered 1 (OZ.Valid 1 w170.low w170.t w170.y w170.r w170.cap) (P33.root 1) :=
  Night6836Tree.sound w170 pick170 1 t7389 _ k170_1_14
private theorem k170_2_0 : check w170 pick170 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k170_2_1 : check w170 pick170 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k170_2_2 : check w170 pick170 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w170 pick170 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k170_2_0 k170_2_1
theorem cov170_2 : PA.Covered 2 (OZ.Valid 2 w170.low w170.t w170.y w170.r w170.cap) (P33.root 2) :=
  Night6836Tree.sound w170 pick170 2 t5461 _ k170_2_2
theorem cov170_3 : PA.Covered 3 (OZ.Valid 3 w170.low w170.t w170.y w170.r w170.cap) (P33.root 3) :=
  Night6836Tree.sound w170 pick170 3 t564 _ (by decide +kernel)
theorem cov170_4 : PA.Covered 4 (OZ.Valid 4 w170.low w170.t w170.y w170.r w170.cap) (P33.root 4) :=
  Night6836Tree.sound w170 pick170 4 t565 _ (by decide +kernel)
theorem cov170_5 : PA.Covered 5 (OZ.Valid 5 w170.low w170.t w170.y w170.r w170.cap) (P33.root 5) :=
  Night6836Tree.sound w170 pick170 5 t566 _ (by decide +kernel)
theorem cov170_6 : PA.Covered 6 (OZ.Valid 6 w170.low w170.t w170.y w170.r w170.cap) (P33.root 6) :=
  Night6836Tree.sound w170 pick170 6 t567 _ (by decide +kernel)
theorem cov170_7 : PA.Covered 7 (OZ.Valid 7 w170.low w170.t w170.y w170.r w170.cap) (P33.root 7) :=
  Night6836Tree.sound w170 pick170 7 t568 _ (by decide +kernel)
theorem window170 : P33.WindowCount w170 := by
  apply P33.window_count w170 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov170_1
  · exact cov170_2
  · exact cov170_3
  · exact cov170_4
  · exact cov170_5
  · exact cov170_6
  · exact cov170_7
def w171 : P33.Window := ⟨12,25,7310,6644,241856191771800395,14572,21000,5000000,81920000000⟩
def h171_0 : Height w171 := ⟨14572,21000,by decide +kernel⟩
def h171_1 : Height w171 := ⟨19657,18000,by decide +kernel⟩
def h171_2 : Height w171 := ⟨28310,15000,by decide +kernel⟩
def pick171 (cl : ℕ) : Height w171 := if cl<18 then (h171_0) else (if cl<257 then (h171_1) else (h171_2))
private theorem k171_1_0 : check w171 pick171 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k171_1_1 : check w171 pick171 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k171_1_2 : check w171 pick171 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w171 pick171 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k171_1_0 k171_1_1
private theorem k171_1_3 : check w171 pick171 1 t7416 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k171_1_4 : check w171 pick171 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k171_1_5 : check w171 pick171 1 t7417 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w171 pick171 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7416 t7348 k171_1_3 k171_1_4
private theorem k171_1_6 : check w171 pick171 1 t7418 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w171 pick171 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7417 k171_1_2 k171_1_5
private theorem k171_1_7 : check w171 pick171 1 t7386 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k171_1_8 : check w171 pick171 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k171_1_9 : check w171 pick171 1 t7387 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w171 pick171 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7386 t7362 k171_1_7 k171_1_8
private theorem k171_1_10 : check w171 pick171 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k171_1_11 : check w171 pick171 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k171_1_12 : check w171 pick171 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w171 pick171 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k171_1_10 k171_1_11
private theorem k171_1_13 : check w171 pick171 1 t7388 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w171 pick171 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7387 t7369 k171_1_9 k171_1_12
private theorem k171_1_14 : check w171 pick171 1 t7419 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w171 pick171 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7418 t7388 k171_1_6 k171_1_13
theorem cov171_1 : PA.Covered 1 (OZ.Valid 1 w171.low w171.t w171.y w171.r w171.cap) (P33.root 1) :=
  Night6836Tree.sound w171 pick171 1 t7419 _ k171_1_14
private theorem k171_2_0 : check w171 pick171 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k171_2_1 : check w171 pick171 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k171_2_2 : check w171 pick171 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w171 pick171 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k171_2_0 k171_2_1
theorem cov171_2 : PA.Covered 2 (OZ.Valid 2 w171.low w171.t w171.y w171.r w171.cap) (P33.root 2) :=
  Night6836Tree.sound w171 pick171 2 t5461 _ k171_2_2
theorem cov171_3 : PA.Covered 3 (OZ.Valid 3 w171.low w171.t w171.y w171.r w171.cap) (P33.root 3) :=
  Night6836Tree.sound w171 pick171 3 t564 _ (by decide +kernel)
theorem cov171_4 : PA.Covered 4 (OZ.Valid 4 w171.low w171.t w171.y w171.r w171.cap) (P33.root 4) :=
  Night6836Tree.sound w171 pick171 4 t565 _ (by decide +kernel)
theorem cov171_5 : PA.Covered 5 (OZ.Valid 5 w171.low w171.t w171.y w171.r w171.cap) (P33.root 5) :=
  Night6836Tree.sound w171 pick171 5 t566 _ (by decide +kernel)
theorem cov171_6 : PA.Covered 6 (OZ.Valid 6 w171.low w171.t w171.y w171.r w171.cap) (P33.root 6) :=
  Night6836Tree.sound w171 pick171 6 t567 _ (by decide +kernel)
theorem cov171_7 : PA.Covered 7 (OZ.Valid 7 w171.low w171.t w171.y w171.r w171.cap) (P33.root 7) :=
  Night6836Tree.sound w171 pick171 7 t568 _ (by decide +kernel)
theorem window171 : P33.WindowCount w171 := by
  apply P33.window_count w171 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov171_1
  · exact cov171_2
  · exact cov171_3
  · exact cov171_4
  · exact cov171_5
  · exact cov171_6
  · exact cov171_7
def w172 : P33.Window := ⟨12,26,5084,4135,231247774171881090,22480,36000,5000000,81920000000⟩
def h172_0 : Height w172 := ⟨22480,36000,by decide +kernel⟩
def h172_1 : Height w172 := ⟨26608,33000,by decide +kernel⟩
def h172_2 : Height w172 := ⟨31745,30000,by decide +kernel⟩
def h172_3 : Height w172 := ⟨38608,27000,by decide +kernel⟩
def h172_4 : Height w172 := ⟨48799,24000,by decide +kernel⟩
def pick172 (cl : ℕ) : Height w172 := if cl<18 then (if cl<3 then (h172_0) else (h172_1)) else (if cl<83 then (h172_2) else (if cl<594 then (h172_3) else (h172_4)))
private theorem k172_1_0 : check w172 pick172 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k172_1_1 : check w172 pick172 1 t7326 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k172_1_2 : check w172 pick172 1 t7327 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w172 pick172 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7326 k172_1_0 k172_1_1
private theorem k172_1_3 : check w172 pick172 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k172_1_4 : check w172 pick172 1 t7452 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k172_1_5 : check w172 pick172 1 t7453 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w172 pick172 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t7452 k172_1_3 k172_1_4
private theorem k172_1_6 : check w172 pick172 1 t7454 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w172 pick172 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7327 t7453 k172_1_2 k172_1_5
theorem cov172_1 : PA.Covered 1 (OZ.Valid 1 w172.low w172.t w172.y w172.r w172.cap) (P33.root 1) :=
  Night6836Tree.sound w172 pick172 1 t7454 _ k172_1_6
theorem cov172_2 : PA.Covered 2 (OZ.Valid 2 w172.low w172.t w172.y w172.r w172.cap) (P33.root 2) :=
  Night6836Tree.sound w172 pick172 2 t6109 _ (by decide +kernel)
theorem cov172_3 : PA.Covered 3 (OZ.Valid 3 w172.low w172.t w172.y w172.r w172.cap) (P33.root 3) :=
  Night6836Tree.sound w172 pick172 3 t564 _ (by decide +kernel)
theorem cov172_4 : PA.Covered 4 (OZ.Valid 4 w172.low w172.t w172.y w172.r w172.cap) (P33.root 4) :=
  Night6836Tree.sound w172 pick172 4 t565 _ (by decide +kernel)
theorem cov172_5 : PA.Covered 5 (OZ.Valid 5 w172.low w172.t w172.y w172.r w172.cap) (P33.root 5) :=
  Night6836Tree.sound w172 pick172 5 t566 _ (by decide +kernel)
theorem cov172_6 : PA.Covered 6 (OZ.Valid 6 w172.low w172.t w172.y w172.r w172.cap) (P33.root 6) :=
  Night6836Tree.sound w172 pick172 6 t567 _ (by decide +kernel)
theorem cov172_7 : PA.Covered 7 (OZ.Valid 7 w172.low w172.t w172.y w172.r w172.cap) (P33.root 7) :=
  Night6836Tree.sound w172 pick172 7 t2134 _ (by decide +kernel)
theorem window172 : P33.WindowCount w172 := by
  apply P33.window_count w172 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov172_1
  · exact cov172_2
  · exact cov172_3
  · exact cov172_4
  · exact cov172_5
  · exact cov172_6
  · exact cov172_7
def w173 : P33.Window := ⟨12,26,7269,7228,244888296046833565,12370,21000,5000000,81920000000⟩
def h173_0 : Height w173 := ⟨12370,21000,by decide +kernel⟩
def h173_1 : Height w173 := ⟨16653,18000,by decide +kernel⟩
def h173_2 : Height w173 := ⟨23412,15000,by decide +kernel⟩
def h173_3 : Height w173 := ⟨38551,12000,by decide +kernel⟩
def pick173 (cl : ℕ) : Height w173 := if cl<83 then (if cl<4 then (h173_0) else (h173_1)) else (if cl<1004 then (h173_2) else (h173_3))
private theorem k173_1_0 : check w173 pick173 1 t7124 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k173_1_1 : check w173 pick173 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k173_1_2 : check w173 pick173 1 t7132 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w173 pick173 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7124 t7131 k173_1_0 k173_1_1
private theorem k173_1_3 : check w173 pick173 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k173_1_4 : check w173 pick173 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k173_1_5 : check w173 pick173 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w173 pick173 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k173_1_3 k173_1_4
private theorem k173_1_6 : check w173 pick173 1 t7455 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w173 pick173 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7132 t7381 k173_1_2 k173_1_5
private theorem k173_1_7 : check w173 pick173 1 t7458 ⟨1,7,2,16,1,20,139,199⟩ = true := by decide +kernel
private theorem k173_1_8 : check w173 pick173 1 t3099 ⟨1,7,2,16,21,52,139,199⟩ = true := by decide +kernel
private theorem k173_1_9 : check w173 pick173 1 t7459 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w173 pick173 1 ⟨1,7,2,16,1,52,139,199⟩ 2 20 t7458 t3099 k173_1_7 k173_1_8
private theorem k173_1_10 : check w173 pick173 1 t7461 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k173_1_11 : check w173 pick173 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k173_1_12 : check w173 pick173 1 t7462 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w173 pick173 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7461 t7318 k173_1_10 k173_1_11
private theorem k173_1_13 : check w173 pick173 1 t7463 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w173 pick173 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7459 t7462 k173_1_9 k173_1_12
private theorem k173_1_14 : check w173 pick173 1 t7464 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w173 pick173 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7455 t7463 k173_1_6 k173_1_13
theorem cov173_1 : PA.Covered 1 (OZ.Valid 1 w173.low w173.t w173.y w173.r w173.cap) (P33.root 1) :=
  Night6836Tree.sound w173 pick173 1 t7464 _ k173_1_14
private theorem k173_2_0 : check w173 pick173 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k173_2_1 : check w173 pick173 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k173_2_2 : check w173 pick173 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w173 pick173 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k173_2_0 k173_2_1
theorem cov173_2 : PA.Covered 2 (OZ.Valid 2 w173.low w173.t w173.y w173.r w173.cap) (P33.root 2) :=
  Night6836Tree.sound w173 pick173 2 t5461 _ k173_2_2
theorem cov173_3 : PA.Covered 3 (OZ.Valid 3 w173.low w173.t w173.y w173.r w173.cap) (P33.root 3) :=
  Night6836Tree.sound w173 pick173 3 t564 _ (by decide +kernel)
theorem cov173_4 : PA.Covered 4 (OZ.Valid 4 w173.low w173.t w173.y w173.r w173.cap) (P33.root 4) :=
  Night6836Tree.sound w173 pick173 4 t565 _ (by decide +kernel)
theorem cov173_5 : PA.Covered 5 (OZ.Valid 5 w173.low w173.t w173.y w173.r w173.cap) (P33.root 5) :=
  Night6836Tree.sound w173 pick173 5 t566 _ (by decide +kernel)
theorem cov173_6 : PA.Covered 6 (OZ.Valid 6 w173.low w173.t w173.y w173.r w173.cap) (P33.root 6) :=
  Night6836Tree.sound w173 pick173 6 t567 _ (by decide +kernel)
theorem cov173_7 : PA.Covered 7 (OZ.Valid 7 w173.low w173.t w173.y w173.r w173.cap) (P33.root 7) :=
  Night6836Tree.sound w173 pick173 7 t568 _ (by decide +kernel)
theorem window173 : P33.WindowCount w173 := by
  apply P33.window_count w173 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov173_1
  · exact cov173_2
  · exact cov173_3
  · exact cov173_4
  · exact cov173_5
  · exact cov173_6
  · exact cov173_7
def w174 : P33.Window := ⟨12,27,7227,7020,244974826875479579,14709,21000,5000000,81920000000⟩
def h174_0 : Height w174 := ⟨14709,21000,by decide +kernel⟩
def h174_1 : Height w174 := ⟨19448,18000,by decide +kernel⟩
def h174_2 : Height w174 := ⟨27171,15000,by decide +kernel⟩
def pick174 (cl : ℕ) : Height w174 := if cl<8 then (h174_0) else (if cl<154 then (h174_1) else (h174_2))
private theorem k174_1_0 : check w174 pick174 1 t7465 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k174_1_1 : check w174 pick174 1 t7470 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k174_1_2 : check w174 pick174 1 t7471 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w174 pick174 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7465 t7470 k174_1_0 k174_1_1
private theorem k174_1_3 : check w174 pick174 1 t7477 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k174_1_4 : check w174 pick174 1 t7482 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k174_1_5 : check w174 pick174 1 t7483 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w174 pick174 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t7477 t7482 k174_1_3 k174_1_4
private theorem k174_1_6 : check w174 pick174 1 t7484 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w174 pick174 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t7471 t7483 k174_1_2 k174_1_5
private theorem k174_1_7 : check w174 pick174 1 t7489 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k174_1_8 : check w174 pick174 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k174_1_9 : check w174 pick174 1 t7490 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w174 pick174 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7489 t6872 k174_1_7 k174_1_8
private theorem k174_1_10 : check w174 pick174 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k174_1_11 : check w174 pick174 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k174_1_12 : check w174 pick174 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w174 pick174 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k174_1_10 k174_1_11
private theorem k174_1_13 : check w174 pick174 1 t7491 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w174 pick174 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7490 t7190 k174_1_9 k174_1_12
private theorem k174_1_14 : check w174 pick174 1 t7492 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w174 pick174 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7484 t7491 k174_1_6 k174_1_13
theorem cov174_1 : PA.Covered 1 (OZ.Valid 1 w174.low w174.t w174.y w174.r w174.cap) (P33.root 1) :=
  Night6836Tree.sound w174 pick174 1 t7492 _ k174_1_14
private theorem k174_2_0 : check w174 pick174 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k174_2_1 : check w174 pick174 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k174_2_2 : check w174 pick174 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w174 pick174 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k174_2_0 k174_2_1
theorem cov174_2 : PA.Covered 2 (OZ.Valid 2 w174.low w174.t w174.y w174.r w174.cap) (P33.root 2) :=
  Night6836Tree.sound w174 pick174 2 t5461 _ k174_2_2
theorem cov174_3 : PA.Covered 3 (OZ.Valid 3 w174.low w174.t w174.y w174.r w174.cap) (P33.root 3) :=
  Night6836Tree.sound w174 pick174 3 t564 _ (by decide +kernel)
theorem cov174_4 : PA.Covered 4 (OZ.Valid 4 w174.low w174.t w174.y w174.r w174.cap) (P33.root 4) :=
  Night6836Tree.sound w174 pick174 4 t565 _ (by decide +kernel)
theorem cov174_5 : PA.Covered 5 (OZ.Valid 5 w174.low w174.t w174.y w174.r w174.cap) (P33.root 5) :=
  Night6836Tree.sound w174 pick174 5 t566 _ (by decide +kernel)
theorem cov174_6 : PA.Covered 6 (OZ.Valid 6 w174.low w174.t w174.y w174.r w174.cap) (P33.root 6) :=
  Night6836Tree.sound w174 pick174 6 t567 _ (by decide +kernel)
theorem cov174_7 : PA.Covered 7 (OZ.Valid 7 w174.low w174.t w174.y w174.r w174.cap) (P33.root 7) :=
  Night6836Tree.sound w174 pick174 7 t568 _ (by decide +kernel)
theorem window174 : P33.WindowCount w174 := by
  apply P33.window_count w174 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov174_1
  · exact cov174_2
  · exact cov174_3
  · exact cov174_4
  · exact cov174_5
  · exact cov174_6
  · exact cov174_7
def w175 : P33.Window := ⟨12,28,7184,7099,244620365385311955,15417,21000,5000000,81920000000⟩
def h175_0 : Height w175 := ⟨15417,21000,by decide +kernel⟩
def h175_1 : Height w175 := ⟨20176,18000,by decide +kernel⟩
def h175_2 : Height w175 := ⟨27896,15000,by decide +kernel⟩
def pick175 (cl : ℕ) : Height w175 := if cl<10 then (h175_0) else (if cl<154 then (h175_1) else (h175_2))
private theorem k175_1_0 : check w175 pick175 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k175_1_1 : check w175 pick175 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k175_1_2 : check w175 pick175 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w175 pick175 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k175_1_0 k175_1_1
private theorem k175_1_3 : check w175 pick175 1 t7506 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k175_1_4 : check w175 pick175 1 t7510 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k175_1_5 : check w175 pick175 1 t7511 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w175 pick175 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t7506 t7510 k175_1_3 k175_1_4
private theorem k175_1_6 : check w175 pick175 1 t7512 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w175 pick175 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t7511 k175_1_2 k175_1_5
private theorem k175_1_7 : check w175 pick175 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k175_1_8 : check w175 pick175 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k175_1_9 : check w175 pick175 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w175 pick175 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k175_1_7 k175_1_8
private theorem k175_1_10 : check w175 pick175 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k175_1_11 : check w175 pick175 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k175_1_12 : check w175 pick175 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w175 pick175 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k175_1_10 k175_1_11
private theorem k175_1_13 : check w175 pick175 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w175 pick175 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k175_1_9 k175_1_12
private theorem k175_1_14 : check w175 pick175 1 t7520 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w175 pick175 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t7512 t7519 k175_1_6 k175_1_13
theorem cov175_1 : PA.Covered 1 (OZ.Valid 1 w175.low w175.t w175.y w175.r w175.cap) (P33.root 1) :=
  Night6836Tree.sound w175 pick175 1 t7520 _ k175_1_14
private theorem k175_2_0 : check w175 pick175 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k175_2_1 : check w175 pick175 2 t7522 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k175_2_2 : check w175 pick175 2 t7523 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w175 pick175 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t7522 k175_2_0 k175_2_1
theorem cov175_2 : PA.Covered 2 (OZ.Valid 2 w175.low w175.t w175.y w175.r w175.cap) (P33.root 2) :=
  Night6836Tree.sound w175 pick175 2 t7523 _ k175_2_2
theorem cov175_3 : PA.Covered 3 (OZ.Valid 3 w175.low w175.t w175.y w175.r w175.cap) (P33.root 3) :=
  Night6836Tree.sound w175 pick175 3 t564 _ (by decide +kernel)
theorem cov175_4 : PA.Covered 4 (OZ.Valid 4 w175.low w175.t w175.y w175.r w175.cap) (P33.root 4) :=
  Night6836Tree.sound w175 pick175 4 t565 _ (by decide +kernel)
theorem cov175_5 : PA.Covered 5 (OZ.Valid 5 w175.low w175.t w175.y w175.r w175.cap) (P33.root 5) :=
  Night6836Tree.sound w175 pick175 5 t566 _ (by decide +kernel)
theorem cov175_6 : PA.Covered 6 (OZ.Valid 6 w175.low w175.t w175.y w175.r w175.cap) (P33.root 6) :=
  Night6836Tree.sound w175 pick175 6 t567 _ (by decide +kernel)
theorem cov175_7 : PA.Covered 7 (OZ.Valid 7 w175.low w175.t w175.y w175.r w175.cap) (P33.root 7) :=
  Night6836Tree.sound w175 pick175 7 t568 _ (by decide +kernel)
theorem window175 : P33.WindowCount w175 := by
  apply P33.window_count w175 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov175_1
  · exact cov175_2
  · exact cov175_3
  · exact cov175_4
  · exact cov175_5
  · exact cov175_6
  · exact cov175_7
def w176 : P33.Window := ⟨12,29,7141,7099,245833743488358814,16593,21000,5000000,81920000000⟩
def h176_0 : Height w176 := ⟨16593,21000,by decide +kernel⟩
def h176_1 : Height w176 := ⟨21499,18000,by decide +kernel⟩
def h176_2 : Height w176 := ⟨29497,15000,by decide +kernel⟩
def pick176 (cl : ℕ) : Height w176 := if cl<12 then (h176_0) else (if cl<183 then (h176_1) else (h176_2))
private theorem k176_1_0 : check w176 pick176 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k176_1_1 : check w176 pick176 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k176_1_2 : check w176 pick176 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w176 pick176 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k176_1_0 k176_1_1
private theorem k176_1_3 : check w176 pick176 1 t7526 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k176_1_4 : check w176 pick176 1 t7529 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k176_1_5 : check w176 pick176 1 t7530 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w176 pick176 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t7526 t7529 k176_1_3 k176_1_4
private theorem k176_1_6 : check w176 pick176 1 t7531 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w176 pick176 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t7530 k176_1_2 k176_1_5
private theorem k176_1_7 : check w176 pick176 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k176_1_8 : check w176 pick176 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k176_1_9 : check w176 pick176 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w176 pick176 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k176_1_7 k176_1_8
private theorem k176_1_10 : check w176 pick176 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k176_1_11 : check w176 pick176 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k176_1_12 : check w176 pick176 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w176 pick176 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k176_1_10 k176_1_11
private theorem k176_1_13 : check w176 pick176 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w176 pick176 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k176_1_9 k176_1_12
private theorem k176_1_14 : check w176 pick176 1 t7532 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w176 pick176 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t7531 t7519 k176_1_6 k176_1_13
theorem cov176_1 : PA.Covered 1 (OZ.Valid 1 w176.low w176.t w176.y w176.r w176.cap) (P33.root 1) :=
  Night6836Tree.sound w176 pick176 1 t7532 _ k176_1_14
private theorem k176_2_0 : check w176 pick176 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k176_2_1 : check w176 pick176 2 t7541 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k176_2_2 : check w176 pick176 2 t7542 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w176 pick176 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t7541 k176_2_0 k176_2_1
theorem cov176_2 : PA.Covered 2 (OZ.Valid 2 w176.low w176.t w176.y w176.r w176.cap) (P33.root 2) :=
  Night6836Tree.sound w176 pick176 2 t7542 _ k176_2_2
theorem cov176_3 : PA.Covered 3 (OZ.Valid 3 w176.low w176.t w176.y w176.r w176.cap) (P33.root 3) :=
  Night6836Tree.sound w176 pick176 3 t564 _ (by decide +kernel)
theorem cov176_4 : PA.Covered 4 (OZ.Valid 4 w176.low w176.t w176.y w176.r w176.cap) (P33.root 4) :=
  Night6836Tree.sound w176 pick176 4 t565 _ (by decide +kernel)
theorem cov176_5 : PA.Covered 5 (OZ.Valid 5 w176.low w176.t w176.y w176.r w176.cap) (P33.root 5) :=
  Night6836Tree.sound w176 pick176 5 t566 _ (by decide +kernel)
theorem cov176_6 : PA.Covered 6 (OZ.Valid 6 w176.low w176.t w176.y w176.r w176.cap) (P33.root 6) :=
  Night6836Tree.sound w176 pick176 6 t567 _ (by decide +kernel)
theorem cov176_7 : PA.Covered 7 (OZ.Valid 7 w176.low w176.t w176.y w176.r w176.cap) (P33.root 7) :=
  Night6836Tree.sound w176 pick176 7 t568 _ (by decide +kernel)
theorem window176 : P33.WindowCount w176 := by
  apply P33.window_count w176 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov176_1
  · exact cov176_2
  · exact cov176_3
  · exact cov176_4
  · exact cov176_5
  · exact cov176_6
  · exact cov176_7
def w177 : P33.Window := ⟨12,30,7098,7051,244940218030032224,18092,21000,5000000,81920000000⟩
def h177_0 : Height w177 := ⟨18092,21000,by decide +kernel⟩
def h177_1 : Height w177 := ⟨23231,18000,by decide +kernel⟩
def h177_2 : Height w177 := ⟨31701,15000,by decide +kernel⟩
def h177_3 : Height w177 := ⟨51854,12000,by decide +kernel⟩
def pick177 (cl : ℕ) : Height w177 := if cl<236 then (if cl<18 then (h177_0) else (h177_1)) else (if cl<1027 then (h177_2) else (h177_3))
private theorem k177_1_0 : check w177 pick177 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k177_1_1 : check w177 pick177 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k177_1_2 : check w177 pick177 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w177 pick177 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k177_1_0 k177_1_1
private theorem k177_1_3 : check w177 pick177 1 t7526 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k177_1_4 : check w177 pick177 1 t7529 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k177_1_5 : check w177 pick177 1 t7530 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w177 pick177 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t7526 t7529 k177_1_3 k177_1_4
private theorem k177_1_6 : check w177 pick177 1 t7531 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w177 pick177 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t7530 k177_1_2 k177_1_5
private theorem k177_1_7 : check w177 pick177 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k177_1_8 : check w177 pick177 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k177_1_9 : check w177 pick177 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w177 pick177 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k177_1_7 k177_1_8
private theorem k177_1_10 : check w177 pick177 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k177_1_11 : check w177 pick177 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k177_1_12 : check w177 pick177 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w177 pick177 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k177_1_10 k177_1_11
private theorem k177_1_13 : check w177 pick177 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w177 pick177 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k177_1_9 k177_1_12
private theorem k177_1_14 : check w177 pick177 1 t7532 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w177 pick177 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t7531 t7519 k177_1_6 k177_1_13
theorem cov177_1 : PA.Covered 1 (OZ.Valid 1 w177.low w177.t w177.y w177.r w177.cap) (P33.root 1) :=
  Night6836Tree.sound w177 pick177 1 t7532 _ k177_1_14
private theorem k177_2_0 : check w177 pick177 2 t7548 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k177_2_1 : check w177 pick177 2 t5624 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k177_2_2 : check w177 pick177 2 t7549 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w177 pick177 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7548 t5624 k177_2_0 k177_2_1
theorem cov177_2 : PA.Covered 2 (OZ.Valid 2 w177.low w177.t w177.y w177.r w177.cap) (P33.root 2) :=
  Night6836Tree.sound w177 pick177 2 t7549 _ k177_2_2
theorem cov177_3 : PA.Covered 3 (OZ.Valid 3 w177.low w177.t w177.y w177.r w177.cap) (P33.root 3) :=
  Night6836Tree.sound w177 pick177 3 t564 _ (by decide +kernel)
theorem cov177_4 : PA.Covered 4 (OZ.Valid 4 w177.low w177.t w177.y w177.r w177.cap) (P33.root 4) :=
  Night6836Tree.sound w177 pick177 4 t565 _ (by decide +kernel)
theorem cov177_5 : PA.Covered 5 (OZ.Valid 5 w177.low w177.t w177.y w177.r w177.cap) (P33.root 5) :=
  Night6836Tree.sound w177 pick177 5 t566 _ (by decide +kernel)
theorem cov177_6 : PA.Covered 6 (OZ.Valid 6 w177.low w177.t w177.y w177.r w177.cap) (P33.root 6) :=
  Night6836Tree.sound w177 pick177 6 t567 _ (by decide +kernel)
theorem cov177_7 : PA.Covered 7 (OZ.Valid 7 w177.low w177.t w177.y w177.r w177.cap) (P33.root 7) :=
  Night6836Tree.sound w177 pick177 7 t568 _ (by decide +kernel)
theorem window177 : P33.WindowCount w177 := by
  apply P33.window_count w177 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov177_1
  · exact cov177_2
  · exact cov177_3
  · exact cov177_4
  · exact cov177_5
  · exact cov177_6
  · exact cov177_7
def w178 : P33.Window := ⟨12,31,7050,6898,245636639128371072,16408,24000,5000000,81920000000⟩
def h178_0 : Height w178 := ⟨16408,24000,by decide +kernel⟩
def h178_1 : Height w178 := ⟨20405,21000,by decide +kernel⟩
def h178_2 : Height w178 := ⟨26004,18000,by decide +kernel⟩
def h178_3 : Height w178 := ⟨35461,15000,by decide +kernel⟩
def pick178 (cl : ℕ) : Height w178 := if cl<32 then (if cl<2 then (h178_0) else (h178_1)) else (if cl<312 then (h178_2) else (h178_3))
private theorem k178_1_0 : check w178 pick178 1 t7551 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k178_1_1 : check w178 pick178 1 t7555 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k178_1_2 : check w178 pick178 1 t7556 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w178 pick178 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7551 t7555 k178_1_0 k178_1_1
private theorem k178_1_3 : check w178 pick178 1 t7559 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k178_1_4 : check w178 pick178 1 t7482 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k178_1_5 : check w178 pick178 1 t7560 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w178 pick178 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7559 t7482 k178_1_3 k178_1_4
private theorem k178_1_6 : check w178 pick178 1 t7561 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w178 pick178 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7556 t7560 k178_1_2 k178_1_5
private theorem k178_1_7 : check w178 pick178 1 t7565 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k178_1_8 : check w178 pick178 1 t7576 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k178_1_9 : check w178 pick178 1 t7577 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w178 pick178 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7565 t7576 k178_1_7 k178_1_8
private theorem k178_1_10 : check w178 pick178 1 t7585 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k178_1_11 : check w178 pick178 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k178_1_12 : check w178 pick178 1 t7591 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w178 pick178 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7585 t7590 k178_1_10 k178_1_11
private theorem k178_1_13 : check w178 pick178 1 t7592 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w178 pick178 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7577 t7591 k178_1_9 k178_1_12
private theorem k178_1_14 : check w178 pick178 1 t7593 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w178 pick178 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7561 t7592 k178_1_6 k178_1_13
theorem cov178_1 : PA.Covered 1 (OZ.Valid 1 w178.low w178.t w178.y w178.r w178.cap) (P33.root 1) :=
  Night6836Tree.sound w178 pick178 1 t7593 _ k178_1_14
private theorem k178_2_0 : check w178 pick178 2 t7595 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k178_2_1 : check w178 pick178 2 t5624 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k178_2_2 : check w178 pick178 2 t7596 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w178 pick178 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7595 t5624 k178_2_0 k178_2_1
theorem cov178_2 : PA.Covered 2 (OZ.Valid 2 w178.low w178.t w178.y w178.r w178.cap) (P33.root 2) :=
  Night6836Tree.sound w178 pick178 2 t7596 _ k178_2_2
theorem cov178_3 : PA.Covered 3 (OZ.Valid 3 w178.low w178.t w178.y w178.r w178.cap) (P33.root 3) :=
  Night6836Tree.sound w178 pick178 3 t564 _ (by decide +kernel)
theorem cov178_4 : PA.Covered 4 (OZ.Valid 4 w178.low w178.t w178.y w178.r w178.cap) (P33.root 4) :=
  Night6836Tree.sound w178 pick178 4 t565 _ (by decide +kernel)
theorem cov178_5 : PA.Covered 5 (OZ.Valid 5 w178.low w178.t w178.y w178.r w178.cap) (P33.root 5) :=
  Night6836Tree.sound w178 pick178 5 t566 _ (by decide +kernel)
theorem cov178_6 : PA.Covered 6 (OZ.Valid 6 w178.low w178.t w178.y w178.r w178.cap) (P33.root 6) :=
  Night6836Tree.sound w178 pick178 6 t567 _ (by decide +kernel)
theorem cov178_7 : PA.Covered 7 (OZ.Valid 7 w178.low w178.t w178.y w178.r w178.cap) (P33.root 7) :=
  Night6836Tree.sound w178 pick178 7 t568 _ (by decide +kernel)
theorem window178 : P33.WindowCount w178 := by
  apply P33.window_count w178 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov178_1
  · exact cov178_2
  · exact cov178_3
  · exact cov178_4
  · exact cov178_5
  · exact cov178_6
  · exact cov178_7
def w179 : P33.Window := ⟨12,32,7000,6950,246327927489265090,17198,24000,5000000,81920000000⟩
def h179_0 : Height w179 := ⟨17198,24000,by decide +kernel⟩
def h179_1 : Height w179 := ⟨21232,21000,by decide +kernel⟩
def h179_2 : Height w179 := ⟨26879,18000,by decide +kernel⟩
def h179_3 : Height w179 := ⟨36389,15000,by decide +kernel⟩
def pick179 (cl : ℕ) : Height w179 := if cl<32 then (if cl<2 then (h179_0) else (h179_1)) else (if cl<318 then (h179_2) else (h179_3))
private theorem k179_1_0 : check w179 pick179 1 t7600 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k179_1_1 : check w179 pick179 1 t7603 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k179_1_2 : check w179 pick179 1 t7604 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w179 pick179 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7600 t7603 k179_1_0 k179_1_1
private theorem k179_1_3 : check w179 pick179 1 t7612 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k179_1_4 : check w179 pick179 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k179_1_5 : check w179 pick179 1 t7624 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w179 pick179 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t7612 t7623 k179_1_3 k179_1_4
private theorem k179_1_6 : check w179 pick179 1 t7625 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w179 pick179 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t7604 t7624 k179_1_2 k179_1_5
private theorem k179_1_7 : check w179 pick179 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k179_1_8 : check w179 pick179 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k179_1_9 : check w179 pick179 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w179 pick179 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k179_1_7 k179_1_8
private theorem k179_1_10 : check w179 pick179 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k179_1_11 : check w179 pick179 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k179_1_12 : check w179 pick179 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w179 pick179 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k179_1_10 k179_1_11
private theorem k179_1_13 : check w179 pick179 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w179 pick179 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k179_1_9 k179_1_12
private theorem k179_1_14 : check w179 pick179 1 t7650 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w179 pick179 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7625 t7649 k179_1_6 k179_1_13
theorem cov179_1 : PA.Covered 1 (OZ.Valid 1 w179.low w179.t w179.y w179.r w179.cap) (P33.root 1) :=
  Night6836Tree.sound w179 pick179 1 t7650 _ k179_1_14
private theorem k179_2_0 : check w179 pick179 2 t7595 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k179_2_1 : check w179 pick179 2 t5624 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k179_2_2 : check w179 pick179 2 t7596 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w179 pick179 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7595 t5624 k179_2_0 k179_2_1
theorem cov179_2 : PA.Covered 2 (OZ.Valid 2 w179.low w179.t w179.y w179.r w179.cap) (P33.root 2) :=
  Night6836Tree.sound w179 pick179 2 t7596 _ k179_2_2
theorem cov179_3 : PA.Covered 3 (OZ.Valid 3 w179.low w179.t w179.y w179.r w179.cap) (P33.root 3) :=
  Night6836Tree.sound w179 pick179 3 t564 _ (by decide +kernel)
theorem cov179_4 : PA.Covered 4 (OZ.Valid 4 w179.low w179.t w179.y w179.r w179.cap) (P33.root 4) :=
  Night6836Tree.sound w179 pick179 4 t565 _ (by decide +kernel)
theorem cov179_5 : PA.Covered 5 (OZ.Valid 5 w179.low w179.t w179.y w179.r w179.cap) (P33.root 5) :=
  Night6836Tree.sound w179 pick179 5 t566 _ (by decide +kernel)
theorem cov179_6 : PA.Covered 6 (OZ.Valid 6 w179.low w179.t w179.y w179.r w179.cap) (P33.root 6) :=
  Night6836Tree.sound w179 pick179 6 t567 _ (by decide +kernel)
theorem cov179_7 : PA.Covered 7 (OZ.Valid 7 w179.low w179.t w179.y w179.r w179.cap) (P33.root 7) :=
  Night6836Tree.sound w179 pick179 7 t568 _ (by decide +kernel)
theorem window179 : P33.WindowCount w179 := by
  apply P33.window_count w179 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov179_1
  · exact cov179_2
  · exact cov179_3
  · exact cov179_4
  · exact cov179_5
  · exact cov179_6
  · exact cov179_7
end ProximityPrize.SubmissionLower.Night6836Bank
