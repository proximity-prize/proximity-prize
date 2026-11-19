/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w90 : P33.Window := ⟨10,51,5922,5620,247477255861490445,43101,30000,5000000,81920000000⟩
def h90_0 : Height w90 := ⟨43101,30000,by decide +kernel⟩
def h90_1 : Height w90 := ⟨47428,27000,by decide +kernel⟩
def h90_2 : Height w90 := ⟨52869,24000,by decide +kernel⟩
def h90_3 : Height w90 := ⟨60243,21000,by decide +kernel⟩
def h90_4 : Height w90 := ⟨71425,18000,by decide +kernel⟩
def pick90 (cl : ℕ) : Height w90 := if cl<23 then (if cl<5 then (h90_0) else (h90_1)) else (if cl<117 then (h90_2) else (if cl<853 then (h90_3) else (h90_4)))
private theorem k90_1_0 : check w90 pick90 1 t4290 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k90_1_1 : check w90 pick90 1 t4737 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k90_1_2 : check w90 pick90 1 t4738 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w90 pick90 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t4290 t4737 k90_1_0 k90_1_1
private theorem k90_1_3 : check w90 pick90 1 t4569 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k90_1_4 : check w90 pick90 1 t4919 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k90_1_5 : check w90 pick90 1 t4920 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w90 pick90 1 ⟨1,7,2,16,1,52,70,131⟩ 3 104 t4569 t4919 k90_1_3 k90_1_4
private theorem k90_1_6 : check w90 pick90 1 t4921 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w90 pick90 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t4738 t4920 k90_1_2 k90_1_5
private theorem k90_1_7 : check w90 pick90 1 t4754 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k90_1_8 : check w90 pick90 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k90_1_9 : check w90 pick90 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k90_1_10 : check w90 pick90 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w90 pick90 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k90_1_8 k90_1_9
private theorem k90_1_11 : check w90 pick90 1 t4755 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w90 pick90 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t4754 t4432 k90_1_7 k90_1_10
private theorem k90_1_12 : check w90 pick90 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k90_1_13 : check w90 pick90 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k90_1_14 : check w90 pick90 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w90 pick90 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k90_1_12 k90_1_13
private theorem k90_1_15 : check w90 pick90 1 t4756 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w90 pick90 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4755 t4179 k90_1_11 k90_1_14
private theorem k90_1_16 : check w90 pick90 1 t4922 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w90 pick90 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t4921 t4756 k90_1_6 k90_1_15
theorem cov90_1 : PA.Covered 1 (OZ.Valid 1 w90.low w90.t w90.y w90.r w90.cap) (P33.root 1) :=
  Night6836Tree.sound w90 pick90 1 t4922 _ k90_1_16
private theorem k90_2_0 : check w90 pick90 2 t4930 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k90_2_1 : check w90 pick90 2 t4937 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k90_2_2 : check w90 pick90 2 t4938 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w90 pick90 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4930 t4937 k90_2_0 k90_2_1
private theorem k90_2_3 : check w90 pick90 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k90_2_4 : check w90 pick90 2 t4950 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k90_2_5 : check w90 pick90 2 t4951 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w90 pick90 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t4950 k90_2_3 k90_2_4
private theorem k90_2_6 : check w90 pick90 2 t4952 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w90 pick90 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4938 t4951 k90_2_2 k90_2_5
theorem cov90_2 : PA.Covered 2 (OZ.Valid 2 w90.low w90.t w90.y w90.r w90.cap) (P33.root 2) :=
  Night6836Tree.sound w90 pick90 2 t4952 _ k90_2_6
theorem cov90_3 : PA.Covered 3 (OZ.Valid 3 w90.low w90.t w90.y w90.r w90.cap) (P33.root 3) :=
  Night6836Tree.sound w90 pick90 3 t4877 _ (by decide +kernel)
theorem cov90_4 : PA.Covered 4 (OZ.Valid 4 w90.low w90.t w90.y w90.r w90.cap) (P33.root 4) :=
  Night6836Tree.sound w90 pick90 4 t565 _ (by decide +kernel)
theorem cov90_5 : PA.Covered 5 (OZ.Valid 5 w90.low w90.t w90.y w90.r w90.cap) (P33.root 5) :=
  Night6836Tree.sound w90 pick90 5 t566 _ (by decide +kernel)
theorem cov90_6 : PA.Covered 6 (OZ.Valid 6 w90.low w90.t w90.y w90.r w90.cap) (P33.root 6) :=
  Night6836Tree.sound w90 pick90 6 t567 _ (by decide +kernel)
theorem cov90_7 : PA.Covered 7 (OZ.Valid 7 w90.low w90.t w90.y w90.r w90.cap) (P33.root 7) :=
  Night6836Tree.sound w90 pick90 7 t2134 _ (by decide +kernel)
theorem window90 : P33.WindowCount w90 := by
  apply P33.window_count w90 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov90_1
  · exact cov90_2
  · exact cov90_3
  · exact cov90_4
  · exact cov90_5
  · exact cov90_6
  · exact cov90_7
def w91 : P33.Window := ⟨10,52,5619,5303,247410186324540544,45459,33000,5000000,81920000000⟩
def h91_0 : Height w91 := ⟨45459,33000,by decide +kernel⟩
def h91_1 : Height w91 := ⟨49514,30000,by decide +kernel⟩
def h91_2 : Height w91 := ⟨54435,27000,by decide +kernel⟩
def h91_3 : Height w91 := ⟨60751,24000,by decide +kernel⟩
def h91_4 : Height w91 := ⟨69530,21000,by decide +kernel⟩
def h91_5 : Height w91 := ⟨83299,18000,by decide +kernel⟩
def pick91 (cl : ℕ) : Height w91 := if cl<49 then (if cl<2 then (h91_0) else (if cl<13 then (h91_1) else (h91_2))) else (if cl<264 then (h91_3) else (if cl<973 then (h91_4) else (h91_5)))
private theorem k91_1_0 : check w91 pick91 1 t4958 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k91_1_1 : check w91 pick91 1 t4975 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k91_1_2 : check w91 pick91 1 t4976 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w91 pick91 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t4958 t4975 k91_1_0 k91_1_1
private theorem k91_1_3 : check w91 pick91 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k91_1_4 : check w91 pick91 1 t4989 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k91_1_5 : check w91 pick91 1 t4990 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w91 pick91 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t4989 k91_1_3 k91_1_4
private theorem k91_1_6 : check w91 pick91 1 t4991 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w91 pick91 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4976 t4990 k91_1_2 k91_1_5
private theorem k91_1_7 : check w91 pick91 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k91_1_8 : check w91 pick91 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k91_1_9 : check w91 pick91 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w91 pick91 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k91_1_7 k91_1_8
private theorem k91_1_10 : check w91 pick91 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k91_1_11 : check w91 pick91 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k91_1_12 : check w91 pick91 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w91 pick91 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k91_1_10 k91_1_11
private theorem k91_1_13 : check w91 pick91 1 t4180 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w91 pick91 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4179 k91_1_9 k91_1_12
private theorem k91_1_14 : check w91 pick91 1 t4992 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w91 pick91 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4991 t4180 k91_1_6 k91_1_13
theorem cov91_1 : PA.Covered 1 (OZ.Valid 1 w91.low w91.t w91.y w91.r w91.cap) (P33.root 1) :=
  Night6836Tree.sound w91 pick91 1 t4992 _ k91_1_14
private theorem k91_2_0 : check w91 pick91 2 t4994 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k91_2_1 : check w91 pick91 2 t5002 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k91_2_2 : check w91 pick91 2 t5003 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w91 pick91 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4994 t5002 k91_2_0 k91_2_1
private theorem k91_2_3 : check w91 pick91 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k91_2_4 : check w91 pick91 2 t5004 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k91_2_5 : check w91 pick91 2 t5005 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w91 pick91 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t5004 k91_2_3 k91_2_4
private theorem k91_2_6 : check w91 pick91 2 t5006 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w91 pick91 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5003 t5005 k91_2_2 k91_2_5
theorem cov91_2 : PA.Covered 2 (OZ.Valid 2 w91.low w91.t w91.y w91.r w91.cap) (P33.root 2) :=
  Night6836Tree.sound w91 pick91 2 t5006 _ k91_2_6
theorem cov91_3 : PA.Covered 3 (OZ.Valid 3 w91.low w91.t w91.y w91.r w91.cap) (P33.root 3) :=
  Night6836Tree.sound w91 pick91 3 t564 _ (by decide +kernel)
theorem cov91_4 : PA.Covered 4 (OZ.Valid 4 w91.low w91.t w91.y w91.r w91.cap) (P33.root 4) :=
  Night6836Tree.sound w91 pick91 4 t565 _ (by decide +kernel)
theorem cov91_5 : PA.Covered 5 (OZ.Valid 5 w91.low w91.t w91.y w91.r w91.cap) (P33.root 5) :=
  Night6836Tree.sound w91 pick91 5 t566 _ (by decide +kernel)
theorem cov91_6 : PA.Covered 6 (OZ.Valid 6 w91.low w91.t w91.y w91.r w91.cap) (P33.root 6) :=
  Night6836Tree.sound w91 pick91 6 t567 _ (by decide +kernel)
theorem cov91_7 : PA.Covered 7 (OZ.Valid 7 w91.low w91.t w91.y w91.r w91.cap) (P33.root 7) :=
  Night6836Tree.sound w91 pick91 7 t2134 _ (by decide +kernel)
theorem window91 : P33.WindowCount w91 := by
  apply P33.window_count w91 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov91_1
  · exact cov91_2
  · exact cov91_3
  · exact cov91_4
  · exact cov91_5
  · exact cov91_6
  · exact cov91_7
def w92 : P33.Window := ⟨10,53,5302,4628,246093020468237525,55961,36000,5000000,81920000000⟩
def h92_0 : Height w92 := ⟨55961,36000,by decide +kernel⟩
def h92_1 : Height w92 := ⟨60423,33000,by decide +kernel⟩
def h92_2 : Height w92 := ⟨65802,30000,by decide +kernel⟩
def h92_3 : Height w92 := ⟨72600,27000,by decide +kernel⟩
def h92_4 : Height w92 := ⟨81768,24000,by decide +kernel⟩
def h92_5 : Height w92 := ⟨95344,21000,by decide +kernel⟩
def pick92 (cl : ℕ) : Height w92 := if cl<82 then (if cl<5 then (h92_0) else (if cl<25 then (h92_1) else (h92_2))) else (if cl<299 then (h92_3) else (if cl<962 then (h92_4) else (h92_5)))
private theorem k92_1_0 : check w92 pick92 1 t5016 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k92_1_1 : check w92 pick92 1 t5026 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k92_1_2 : check w92 pick92 1 t5027 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w92 pick92 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5016 t5026 k92_1_0 k92_1_1
private theorem k92_1_3 : check w92 pick92 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k92_1_4 : check w92 pick92 1 t5063 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k92_1_5 : check w92 pick92 1 t5064 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w92 pick92 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t5063 k92_1_3 k92_1_4
private theorem k92_1_6 : check w92 pick92 1 t5065 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w92 pick92 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t5027 t5064 k92_1_2 k92_1_5
private theorem k92_1_7 : check w92 pick92 1 t3836 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k92_1_8 : check w92 pick92 1 t3840 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k92_1_9 : check w92 pick92 1 t3841 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w92 pick92 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t3836 t3840 k92_1_7 k92_1_8
private theorem k92_1_10 : check w92 pick92 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k92_1_11 : check w92 pick92 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k92_1_12 : check w92 pick92 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w92 pick92 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k92_1_10 k92_1_11
private theorem k92_1_13 : check w92 pick92 1 t3842 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w92 pick92 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t3841 t3709 k92_1_9 k92_1_12
private theorem k92_1_14 : check w92 pick92 1 t5066 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w92 pick92 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5065 t3842 k92_1_6 k92_1_13
theorem cov92_1 : PA.Covered 1 (OZ.Valid 1 w92.low w92.t w92.y w92.r w92.cap) (P33.root 1) :=
  Night6836Tree.sound w92 pick92 1 t5066 _ k92_1_14
private theorem k92_2_0 : check w92 pick92 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k92_2_1 : check w92 pick92 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k92_2_2 : check w92 pick92 2 t3778 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w92 pick92 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3777 k92_2_0 k92_2_1
private theorem k92_2_3 : check w92 pick92 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k92_2_4 : check w92 pick92 2 t5069 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k92_2_5 : check w92 pick92 2 t5070 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w92 pick92 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t5069 k92_2_3 k92_2_4
private theorem k92_2_6 : check w92 pick92 2 t5071 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w92 pick92 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3778 t5070 k92_2_2 k92_2_5
theorem cov92_2 : PA.Covered 2 (OZ.Valid 2 w92.low w92.t w92.y w92.r w92.cap) (P33.root 2) :=
  Night6836Tree.sound w92 pick92 2 t5071 _ k92_2_6
theorem cov92_3 : PA.Covered 3 (OZ.Valid 3 w92.low w92.t w92.y w92.r w92.cap) (P33.root 3) :=
  Night6836Tree.sound w92 pick92 3 t564 _ (by decide +kernel)
theorem cov92_4 : PA.Covered 4 (OZ.Valid 4 w92.low w92.t w92.y w92.r w92.cap) (P33.root 4) :=
  Night6836Tree.sound w92 pick92 4 t565 _ (by decide +kernel)
theorem cov92_5 : PA.Covered 5 (OZ.Valid 5 w92.low w92.t w92.y w92.r w92.cap) (P33.root 5) :=
  Night6836Tree.sound w92 pick92 5 t566 _ (by decide +kernel)
theorem cov92_6 : PA.Covered 6 (OZ.Valid 6 w92.low w92.t w92.y w92.r w92.cap) (P33.root 6) :=
  Night6836Tree.sound w92 pick92 6 t567 _ (by decide +kernel)
theorem cov92_7 : PA.Covered 7 (OZ.Valid 7 w92.low w92.t w92.y w92.r w92.cap) (P33.root 7) :=
  Night6836Tree.sound w92 pick92 7 t2134 _ (by decide +kernel)
theorem window92 : P33.WindowCount w92 := by
  apply P33.window_count w92 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov92_1
  · exact cov92_2
  · exact cov92_3
  · exact cov92_4
  · exact cov92_5
  · exact cov92_6
  · exact cov92_7
def w93 : P33.Window := ⟨10,54,4972,4628,246985319862832433,57497,36000,5000000,81920000000⟩
def h93_0 : Height w93 := ⟨57497,36000,by decide +kernel⟩
def h93_1 : Height w93 := ⟨62020,33000,by decide +kernel⟩
def h93_2 : Height w93 := ⟨67477,30000,by decide +kernel⟩
def h93_3 : Height w93 := ⟨74383,27000,by decide +kernel⟩
def h93_4 : Height w93 := ⟨83707,24000,by decide +kernel⟩
def h93_5 : Height w93 := ⟨97525,21000,by decide +kernel⟩
def pick93 (cl : ℕ) : Height w93 := if cl<83 then (if cl<6 then (h93_0) else (if cl<27 then (h93_1) else (h93_2))) else (if cl<302 then (h93_3) else (if cl<974 then (h93_4) else (h93_5)))
private theorem k93_1_0 : check w93 pick93 1 t5078 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k93_1_1 : check w93 pick93 1 t5105 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k93_1_2 : check w93 pick93 1 t5106 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w93 pick93 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5078 t5105 k93_1_0 k93_1_1
private theorem k93_1_3 : check w93 pick93 1 t5112 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k93_1_4 : check w93 pick93 1 t5115 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k93_1_5 : check w93 pick93 1 t5116 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w93 pick93 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t5112 t5115 k93_1_3 k93_1_4
private theorem k93_1_6 : check w93 pick93 1 t5117 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w93 pick93 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t5106 t5116 k93_1_2 k93_1_5
private theorem k93_1_7 : check w93 pick93 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k93_1_8 : check w93 pick93 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k93_1_9 : check w93 pick93 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w93 pick93 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k93_1_7 k93_1_8
private theorem k93_1_10 : check w93 pick93 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k93_1_11 : check w93 pick93 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k93_1_12 : check w93 pick93 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w93 pick93 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k93_1_10 k93_1_11
private theorem k93_1_13 : check w93 pick93 1 t3710 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w93 pick93 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t3709 k93_1_9 k93_1_12
private theorem k93_1_14 : check w93 pick93 1 t5118 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w93 pick93 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5117 t3710 k93_1_6 k93_1_13
theorem cov93_1 : PA.Covered 1 (OZ.Valid 1 w93.low w93.t w93.y w93.r w93.cap) (P33.root 1) :=
  Night6836Tree.sound w93 pick93 1 t5118 _ k93_1_14
private theorem k93_2_0 : check w93 pick93 2 t3321 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k93_2_1 : check w93 pick93 2 t5122 ⟨2,7,4,16,2,52,85,166⟩ = true := by decide +kernel
private theorem k93_2_2 : check w93 pick93 2 t5123 ⟨2,7,4,16,2,52,2,166⟩ = true := glue w93 pick93 2 ⟨2,7,4,16,2,52,2,166⟩ 3 84 t3321 t5122 k93_2_0 k93_2_1
private theorem k93_2_3 : check w93 pick93 2 t5127 ⟨2,7,4,16,2,52,167,450⟩ = true := by decide +kernel
private theorem k93_2_4 : check w93 pick93 2 t5128 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w93 pick93 2 ⟨2,7,4,16,0,52,0,450⟩ 3 166 t5123 t5127 k93_2_2 k93_2_3
theorem cov93_2 : PA.Covered 2 (OZ.Valid 2 w93.low w93.t w93.y w93.r w93.cap) (P33.root 2) :=
  Night6836Tree.sound w93 pick93 2 t5128 _ k93_2_4
theorem cov93_3 : PA.Covered 3 (OZ.Valid 3 w93.low w93.t w93.y w93.r w93.cap) (P33.root 3) :=
  Night6836Tree.sound w93 pick93 3 t564 _ (by decide +kernel)
theorem cov93_4 : PA.Covered 4 (OZ.Valid 4 w93.low w93.t w93.y w93.r w93.cap) (P33.root 4) :=
  Night6836Tree.sound w93 pick93 4 t565 _ (by decide +kernel)
theorem cov93_5 : PA.Covered 5 (OZ.Valid 5 w93.low w93.t w93.y w93.r w93.cap) (P33.root 5) :=
  Night6836Tree.sound w93 pick93 5 t566 _ (by decide +kernel)
theorem cov93_6 : PA.Covered 6 (OZ.Valid 6 w93.low w93.t w93.y w93.r w93.cap) (P33.root 6) :=
  Night6836Tree.sound w93 pick93 6 t567 _ (by decide +kernel)
theorem cov93_7 : PA.Covered 7 (OZ.Valid 7 w93.low w93.t w93.y w93.r w93.cap) (P33.root 7) :=
  Night6836Tree.sound w93 pick93 7 t2134 _ (by decide +kernel)
theorem window93 : P33.WindowCount w93 := by
  apply P33.window_count w93 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov93_1
  · exact cov93_2
  · exact cov93_3
  · exact cov93_4
  · exact cov93_5
  · exact cov93_6
  · exact cov93_7
def w94 : P33.Window := ⟨10,55,4627,4268,246309286984879498,60095,42000,5000000,81920000000⟩
def h94_0 : Height w94 := ⟨60095,42000,by decide +kernel⟩
def h94_1 : Height w94 := ⟨64050,39000,by decide +kernel⟩
def h94_2 : Height w94 := ⟨68606,36000,by decide +kernel⟩
def h94_3 : Height w94 := ⟨74014,33000,by decide +kernel⟩
def h94_4 : Height w94 := ⟨80688,30000,by decide +kernel⟩
def h94_5 : Height w94 := ⟨89359,27000,by decide +kernel⟩
def h94_6 : Height w94 := ⟨101453,24000,by decide +kernel⟩
def pick94 (cl : ℕ) : Height w94 := if cl<32 then (if cl<2 then (h94_0) else (if cl<6 then (h94_1) else (h94_2))) else (if cl<260 then (if cl<69 then (h94_3) else (h94_4)) else (if cl<922 then (h94_5) else (h94_6)))
private theorem k94_1_0 : check w94 pick94 1 t5132 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k94_1_1 : check w94 pick94 1 t5141 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k94_1_2 : check w94 pick94 1 t5142 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w94 pick94 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5132 t5141 k94_1_0 k94_1_1
private theorem k94_1_3 : check w94 pick94 1 t5158 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k94_1_4 : check w94 pick94 1 t5172 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k94_1_5 : check w94 pick94 1 t5173 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w94 pick94 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t5158 t5172 k94_1_3 k94_1_4
private theorem k94_1_6 : check w94 pick94 1 t5174 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w94 pick94 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t5142 t5173 k94_1_2 k94_1_5
private theorem k94_1_7 : check w94 pick94 1 t5178 ⟨1,7,2,16,1,52,146,179⟩ = true := by decide +kernel
private theorem k94_1_8 : check w94 pick94 1 t2374 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k94_1_9 : check w94 pick94 1 t5179 ⟨1,7,2,16,1,52,146,206⟩ = true := glue w94 pick94 1 ⟨1,7,2,16,1,52,146,206⟩ 3 179 t5178 t2374 k94_1_7 k94_1_8
private theorem k94_1_10 : check w94 pick94 1 t2385 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k94_1_11 : check w94 pick94 1 t5180 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k94_1_12 : check w94 pick94 1 t5181 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w94 pick94 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t2385 t5180 k94_1_10 k94_1_11
private theorem k94_1_13 : check w94 pick94 1 t5182 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w94 pick94 1 ⟨1,7,2,16,1,52,146,450⟩ 3 206 t5179 t5181 k94_1_9 k94_1_12
private theorem k94_1_14 : check w94 pick94 1 t5183 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w94 pick94 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t5174 t5182 k94_1_6 k94_1_13
theorem cov94_1 : PA.Covered 1 (OZ.Valid 1 w94.low w94.t w94.y w94.r w94.cap) (P33.root 1) :=
  Night6836Tree.sound w94 pick94 1 t5183 _ k94_1_14
private theorem k94_2_0 : check w94 pick94 2 t5184 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k94_2_1 : check w94 pick94 2 t5187 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k94_2_2 : check w94 pick94 2 t5188 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w94 pick94 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5184 t5187 k94_2_0 k94_2_1
theorem cov94_2 : PA.Covered 2 (OZ.Valid 2 w94.low w94.t w94.y w94.r w94.cap) (P33.root 2) :=
  Night6836Tree.sound w94 pick94 2 t5188 _ k94_2_2
theorem cov94_3 : PA.Covered 3 (OZ.Valid 3 w94.low w94.t w94.y w94.r w94.cap) (P33.root 3) :=
  Night6836Tree.sound w94 pick94 3 t564 _ (by decide +kernel)
theorem cov94_4 : PA.Covered 4 (OZ.Valid 4 w94.low w94.t w94.y w94.r w94.cap) (P33.root 4) :=
  Night6836Tree.sound w94 pick94 4 t565 _ (by decide +kernel)
theorem cov94_5 : PA.Covered 5 (OZ.Valid 5 w94.low w94.t w94.y w94.r w94.cap) (P33.root 5) :=
  Night6836Tree.sound w94 pick94 5 t566 _ (by decide +kernel)
theorem cov94_6 : PA.Covered 6 (OZ.Valid 6 w94.low w94.t w94.y w94.r w94.cap) (P33.root 6) :=
  Night6836Tree.sound w94 pick94 6 t567 _ (by decide +kernel)
theorem cov94_7 : PA.Covered 7 (OZ.Valid 7 w94.low w94.t w94.y w94.r w94.cap) (P33.root 7) :=
  Night6836Tree.sound w94 pick94 7 t2134 _ (by decide +kernel)
theorem window94 : P33.WindowCount w94 := by
  apply P33.window_count w94 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov94_1
  · exact cov94_2
  · exact cov94_3
  · exact cov94_4
  · exact cov94_5
  · exact cov94_6
  · exact cov94_7
def w95 : P33.Window := ⟨10,56,4267,3895,243822357519877065,68910,45000,5000000,81920000000⟩
def h95_0 : Height w95 := ⟨68910,45000,by decide +kernel⟩
def h95_1 : Height w95 := ⟨73052,42000,by decide +kernel⟩
def h95_2 : Height w95 := ⟨77795,39000,by decide +kernel⟩
def h95_3 : Height w95 := ⟨83367,36000,by decide +kernel⟩
def h95_4 : Height w95 := ⟨90133,33000,by decide +kernel⟩
def h95_5 : Height w95 := ⟨98707,30000,by decide +kernel⟩
def h95_6 : Height w95 := ⟨110207,27000,by decide +kernel⟩
def pick95 (cl : ℕ) : Height w95 := if cl<32 then (if cl<3 then (h95_0) else (if cl<10 then (h95_1) else (h95_2))) else (if cl<260 then (if cl<83 then (h95_3) else (h95_4)) else (if cl<989 then (h95_5) else (h95_6)))
private theorem k95_1_0 : check w95 pick95 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k95_1_1 : check w95 pick95 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k95_1_2 : check w95 pick95 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w95 pick95 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k95_1_0 k95_1_1
private theorem k95_1_3 : check w95 pick95 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k95_1_4 : check w95 pick95 1 t5189 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k95_1_5 : check w95 pick95 1 t5190 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w95 pick95 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t5189 k95_1_3 k95_1_4
private theorem k95_1_6 : check w95 pick95 1 t5191 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w95 pick95 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t5190 k95_1_2 k95_1_5
private theorem k95_1_7 : check w95 pick95 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k95_1_8 : check w95 pick95 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k95_1_9 : check w95 pick95 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w95 pick95 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k95_1_7 k95_1_8
private theorem k95_1_10 : check w95 pick95 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k95_1_11 : check w95 pick95 1 t4260 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k95_1_12 : check w95 pick95 1 t4261 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w95 pick95 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t4260 k95_1_10 k95_1_11
private theorem k95_1_13 : check w95 pick95 1 t4262 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w95 pick95 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t4261 k95_1_9 k95_1_12
private theorem k95_1_14 : check w95 pick95 1 t5192 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w95 pick95 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5191 t4262 k95_1_6 k95_1_13
theorem cov95_1 : PA.Covered 1 (OZ.Valid 1 w95.low w95.t w95.y w95.r w95.cap) (P33.root 1) :=
  Night6836Tree.sound w95 pick95 1 t5192 _ k95_1_14
private theorem k95_2_0 : check w95 pick95 2 t5202 ⟨2,7,4,16,2,52,2,166⟩ = true := by decide +kernel
private theorem k95_2_1 : check w95 pick95 2 t5204 ⟨2,7,4,16,2,52,167,450⟩ = true := by decide +kernel
private theorem k95_2_2 : check w95 pick95 2 t5205 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w95 pick95 2 ⟨2,7,4,16,0,52,0,450⟩ 3 166 t5202 t5204 k95_2_0 k95_2_1
theorem cov95_2 : PA.Covered 2 (OZ.Valid 2 w95.low w95.t w95.y w95.r w95.cap) (P33.root 2) :=
  Night6836Tree.sound w95 pick95 2 t5205 _ k95_2_2
theorem cov95_3 : PA.Covered 3 (OZ.Valid 3 w95.low w95.t w95.y w95.r w95.cap) (P33.root 3) :=
  Night6836Tree.sound w95 pick95 3 t564 _ (by decide +kernel)
theorem cov95_4 : PA.Covered 4 (OZ.Valid 4 w95.low w95.t w95.y w95.r w95.cap) (P33.root 4) :=
  Night6836Tree.sound w95 pick95 4 t565 _ (by decide +kernel)
theorem cov95_5 : PA.Covered 5 (OZ.Valid 5 w95.low w95.t w95.y w95.r w95.cap) (P33.root 5) :=
  Night6836Tree.sound w95 pick95 5 t566 _ (by decide +kernel)
theorem cov95_6 : PA.Covered 6 (OZ.Valid 6 w95.low w95.t w95.y w95.r w95.cap) (P33.root 6) :=
  Night6836Tree.sound w95 pick95 6 t567 _ (by decide +kernel)
theorem cov95_7 : PA.Covered 7 (OZ.Valid 7 w95.low w95.t w95.y w95.r w95.cap) (P33.root 7) :=
  Night6836Tree.sound w95 pick95 7 t2134 _ (by decide +kernel)
theorem window95 : P33.WindowCount w95 := by
  apply P33.window_count w95 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov95_1
  · exact cov95_2
  · exact cov95_3
  · exact cov95_4
  · exact cov95_5
  · exact cov95_6
  · exact cov95_7
def w96 : P33.Window := ⟨10,57,3894,3506,245423229780701363,77215,51000,5000000,81920000000⟩
def h96_0 : Height w96 := ⟨77215,51000,by decide +kernel⟩
def h96_1 : Height w96 := ⟨81227,48000,by decide +kernel⟩
def h96_2 : Height w96 := ⟨85724,45000,by decide +kernel⟩
def h96_3 : Height w96 := ⟨90862,42000,by decide +kernel⟩
def h96_4 : Height w96 := ⟨96869,39000,by decide +kernel⟩
def h96_5 : Height w96 := ⟨104099,36000,by decide +kernel⟩
def h96_6 : Height w96 := ⟨113124,33000,by decide +kernel⟩
def pick96 (cl : ℕ) : Height w96 := if cl<18 then (if cl<2 then (h96_0) else (if cl<5 then (h96_1) else (h96_2))) else (if cl<107 then (if cl<40 then (h96_3) else (h96_4)) else (if cl<282 then (h96_5) else (h96_6)))
private theorem k96_1_0 : check w96 pick96 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k96_1_1 : check w96 pick96 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k96_1_2 : check w96 pick96 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w96 pick96 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k96_1_0 k96_1_1
private theorem k96_1_3 : check w96 pick96 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k96_1_4 : check w96 pick96 1 t4252 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k96_1_5 : check w96 pick96 1 t4253 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w96 pick96 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t4252 k96_1_3 k96_1_4
private theorem k96_1_6 : check w96 pick96 1 t4254 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w96 pick96 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t4253 k96_1_2 k96_1_5
private theorem k96_1_7 : check w96 pick96 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k96_1_8 : check w96 pick96 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k96_1_9 : check w96 pick96 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w96 pick96 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k96_1_7 k96_1_8
private theorem k96_1_10 : check w96 pick96 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k96_1_11 : check w96 pick96 1 t4260 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k96_1_12 : check w96 pick96 1 t4261 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w96 pick96 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t4260 k96_1_10 k96_1_11
private theorem k96_1_13 : check w96 pick96 1 t4262 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w96 pick96 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t4261 k96_1_9 k96_1_12
private theorem k96_1_14 : check w96 pick96 1 t4263 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w96 pick96 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4254 t4262 k96_1_6 k96_1_13
theorem cov96_1 : PA.Covered 1 (OZ.Valid 1 w96.low w96.t w96.y w96.r w96.cap) (P33.root 1) :=
  Night6836Tree.sound w96 pick96 1 t4263 _ k96_1_14
theorem cov96_2 : PA.Covered 2 (OZ.Valid 2 w96.low w96.t w96.y w96.r w96.cap) (P33.root 2) :=
  Night6836Tree.sound w96 pick96 2 t5209 _ (by decide +kernel)
theorem cov96_3 : PA.Covered 3 (OZ.Valid 3 w96.low w96.t w96.y w96.r w96.cap) (P33.root 3) :=
  Night6836Tree.sound w96 pick96 3 t564 _ (by decide +kernel)
theorem cov96_4 : PA.Covered 4 (OZ.Valid 4 w96.low w96.t w96.y w96.r w96.cap) (P33.root 4) :=
  Night6836Tree.sound w96 pick96 4 t565 _ (by decide +kernel)
theorem cov96_5 : PA.Covered 5 (OZ.Valid 5 w96.low w96.t w96.y w96.r w96.cap) (P33.root 5) :=
  Night6836Tree.sound w96 pick96 5 t566 _ (by decide +kernel)
theorem cov96_6 : PA.Covered 6 (OZ.Valid 6 w96.low w96.t w96.y w96.r w96.cap) (P33.root 6) :=
  Night6836Tree.sound w96 pick96 6 t567 _ (by decide +kernel)
theorem cov96_7 : PA.Covered 7 (OZ.Valid 7 w96.low w96.t w96.y w96.r w96.cap) (P33.root 7) :=
  Night6836Tree.sound w96 pick96 7 t2134 _ (by decide +kernel)
theorem window96 : P33.WindowCount w96 := by
  apply P33.window_count w96 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov96_1
  · exact cov96_2
  · exact cov96_3
  · exact cov96_4
  · exact cov96_5
  · exact cov96_6
  · exact cov96_7
def w97 : P33.Window := ⟨10,58,3505,3103,244143474617446660,90238,57000,5000000,81920000000⟩
def h97_0 : Height w97 := ⟨90238,57000,by decide +kernel⟩
def h97_1 : Height w97 := ⟨94345,54000,by decide +kernel⟩
def h97_2 : Height w97 := ⟨98895,51000,by decide +kernel⟩
def h97_3 : Height w97 := ⟨104012,48000,by decide +kernel⟩
def h97_4 : Height w97 := ⟨109867,45000,by decide +kernel⟩
def h97_5 : Height w97 := ⟨116713,42000,by decide +kernel⟩
def h97_6 : Height w97 := ⟨124930,39000,by decide +kernel⟩
def h97_7 : Height w97 := ⟨135120,36000,by decide +kernel⟩
def pick97 (cl : ℕ) : Height w97 := if cl<36 then (if cl<6 then (if cl<3 then (h97_0) else (h97_1)) else (if cl<16 then (h97_2) else (h97_3))) else (if cl<213 then (if cl<83 then (h97_4) else (h97_5)) else (if cl<594 then (h97_6) else (h97_7)))
private theorem k97_1_0 : check w97 pick97 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k97_1_1 : check w97 pick97 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k97_1_2 : check w97 pick97 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w97 pick97 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k97_1_0 k97_1_1
private theorem k97_1_3 : check w97 pick97 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k97_1_4 : check w97 pick97 1 t4252 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k97_1_5 : check w97 pick97 1 t4253 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w97 pick97 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t4252 k97_1_3 k97_1_4
private theorem k97_1_6 : check w97 pick97 1 t4254 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w97 pick97 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t4253 k97_1_2 k97_1_5
private theorem k97_1_7 : check w97 pick97 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k97_1_8 : check w97 pick97 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k97_1_9 : check w97 pick97 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w97 pick97 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k97_1_7 k97_1_8
private theorem k97_1_10 : check w97 pick97 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k97_1_11 : check w97 pick97 1 t4260 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k97_1_12 : check w97 pick97 1 t4261 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w97 pick97 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t4260 k97_1_10 k97_1_11
private theorem k97_1_13 : check w97 pick97 1 t4262 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w97 pick97 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t4261 k97_1_9 k97_1_12
private theorem k97_1_14 : check w97 pick97 1 t4263 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w97 pick97 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t4254 t4262 k97_1_6 k97_1_13
theorem cov97_1 : PA.Covered 1 (OZ.Valid 1 w97.low w97.t w97.y w97.r w97.cap) (P33.root 1) :=
  Night6836Tree.sound w97 pick97 1 t4263 _ k97_1_14
theorem cov97_2 : PA.Covered 2 (OZ.Valid 2 w97.low w97.t w97.y w97.r w97.cap) (P33.root 2) :=
  Night6836Tree.sound w97 pick97 2 t5222 _ (by decide +kernel)
theorem cov97_3 : PA.Covered 3 (OZ.Valid 3 w97.low w97.t w97.y w97.r w97.cap) (P33.root 3) :=
  Night6836Tree.sound w97 pick97 3 t564 _ (by decide +kernel)
theorem cov97_4 : PA.Covered 4 (OZ.Valid 4 w97.low w97.t w97.y w97.r w97.cap) (P33.root 4) :=
  Night6836Tree.sound w97 pick97 4 t565 _ (by decide +kernel)
theorem cov97_5 : PA.Covered 5 (OZ.Valid 5 w97.low w97.t w97.y w97.r w97.cap) (P33.root 5) :=
  Night6836Tree.sound w97 pick97 5 t566 _ (by decide +kernel)
theorem cov97_6 : PA.Covered 6 (OZ.Valid 6 w97.low w97.t w97.y w97.r w97.cap) (P33.root 6) :=
  Night6836Tree.sound w97 pick97 6 t567 _ (by decide +kernel)
theorem cov97_7 : PA.Covered 7 (OZ.Valid 7 w97.low w97.t w97.y w97.r w97.cap) (P33.root 7) :=
  Night6836Tree.sound w97 pick97 7 t2134 _ (by decide +kernel)
theorem window97 : P33.WindowCount w97 := by
  apply P33.window_count w97 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov97_1
  · exact cov97_2
  · exact cov97_3
  · exact cov97_4
  · exact cov97_5
  · exact cov97_6
  · exact cov97_7
def w98 : P33.Window := ⟨10,59,3102,2686,241690565165508367,106565,66000,5000000,81920000000⟩
def h98_0 : Height w98 := ⟨106565,66000,by decide +kernel⟩
def h98_1 : Height w98 := ⟨110667,63000,by decide +kernel⟩
def h98_2 : Height w98 := ⟨115140,60000,by decide +kernel⟩
def h98_3 : Height w98 := ⟨120071,57000,by decide +kernel⟩
def h98_4 : Height w98 := ⟨125574,54000,by decide +kernel⟩
def h98_5 : Height w98 := ⟨131803,51000,by decide +kernel⟩
def h98_6 : Height w98 := ⟨138977,48000,by decide +kernel⟩
def h98_7 : Height w98 := ⟨147408,45000,by decide +kernel⟩
def h98_8 : Height w98 := ⟨157563,42000,by decide +kernel⟩
def pick98 (cl : ℕ) : Height w98 := if cl<32 then (if cl<5 then (if cl<2 then (h98_0) else (h98_1)) else (if cl<13 then (h98_2) else (h98_3))) else (if cl<105 then (if cl<44 then (h98_4) else (h98_5)) else (if cl<231 then (h98_6) else (if cl<561 then (h98_7) else (h98_8))))
private theorem k98_1_0 : check w98 pick98 1 t5236 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k98_1_1 : check w98 pick98 1 t5243 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k98_1_2 : check w98 pick98 1 t5244 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w98 pick98 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5236 t5243 k98_1_0 k98_1_1
private theorem k98_1_3 : check w98 pick98 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k98_1_4 : check w98 pick98 1 t4252 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k98_1_5 : check w98 pick98 1 t4253 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w98 pick98 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t4252 k98_1_3 k98_1_4
private theorem k98_1_6 : check w98 pick98 1 t5245 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w98 pick98 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5244 t4253 k98_1_2 k98_1_5
private theorem k98_1_7 : check w98 pick98 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k98_1_8 : check w98 pick98 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k98_1_9 : check w98 pick98 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w98 pick98 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k98_1_7 k98_1_8
private theorem k98_1_10 : check w98 pick98 1 t5264 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k98_1_11 : check w98 pick98 1 t5265 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w98 pick98 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5264 k98_1_9 k98_1_10
private theorem k98_1_12 : check w98 pick98 1 t5266 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w98 pick98 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5245 t5265 k98_1_6 k98_1_11
theorem cov98_1 : PA.Covered 1 (OZ.Valid 1 w98.low w98.t w98.y w98.r w98.cap) (P33.root 1) :=
  Night6836Tree.sound w98 pick98 1 t5266 _ k98_1_12
theorem cov98_2 : PA.Covered 2 (OZ.Valid 2 w98.low w98.t w98.y w98.r w98.cap) (P33.root 2) :=
  Night6836Tree.sound w98 pick98 2 t5222 _ (by decide +kernel)
theorem cov98_3 : PA.Covered 3 (OZ.Valid 3 w98.low w98.t w98.y w98.r w98.cap) (P33.root 3) :=
  Night6836Tree.sound w98 pick98 3 t564 _ (by decide +kernel)
theorem cov98_4 : PA.Covered 4 (OZ.Valid 4 w98.low w98.t w98.y w98.r w98.cap) (P33.root 4) :=
  Night6836Tree.sound w98 pick98 4 t565 _ (by decide +kernel)
theorem cov98_5 : PA.Covered 5 (OZ.Valid 5 w98.low w98.t w98.y w98.r w98.cap) (P33.root 5) :=
  Night6836Tree.sound w98 pick98 5 t566 _ (by decide +kernel)
theorem cov98_6 : PA.Covered 6 (OZ.Valid 6 w98.low w98.t w98.y w98.r w98.cap) (P33.root 6) :=
  Night6836Tree.sound w98 pick98 6 t567 _ (by decide +kernel)
theorem cov98_7 : PA.Covered 7 (OZ.Valid 7 w98.low w98.t w98.y w98.r w98.cap) (P33.root 7) :=
  Night6836Tree.sound w98 pick98 7 t2134 _ (by decide +kernel)
theorem window98 : P33.WindowCount w98 := by
  apply P33.window_count w98 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov98_1
  · exact cov98_2
  · exact cov98_3
  · exact cov98_4
  · exact cov98_5
  · exact cov98_6
  · exact cov98_7
def w99 : P33.Window := ⟨10,60,2685,2254,223379842365203713,126913,81000,5000000,81920000000⟩
def h99_0 : Height w99 := ⟨126913,81000,by decide +kernel⟩
def h99_1 : Height w99 := ⟨130813,78000,by decide +kernel⟩
def h99_2 : Height w99 := ⟨134982,75000,by decide +kernel⟩
def h99_3 : Height w99 := ⟨139467,72000,by decide +kernel⟩
def h99_4 : Height w99 := ⟨144327,69000,by decide +kernel⟩
def h99_5 : Height w99 := ⟨149638,66000,by decide +kernel⟩
def h99_6 : Height w99 := ⟨155498,63000,by decide +kernel⟩
def h99_7 : Height w99 := ⟨162032,60000,by decide +kernel⟩
def h99_8 : Height w99 := ⟨169410,57000,by decide +kernel⟩
def h99_9 : Height w99 := ⟨177862,54000,by decide +kernel⟩
def h99_10 : Height w99 := ⟨187710,51000,by decide +kernel⟩
def pick99 (cl : ℕ) : Height w99 := if cl<32 then (if cl<4 then (if cl<2 then (h99_0) else (h99_1)) else (if cl<5 then (h99_2) else (if cl<13 then (h99_3) else (h99_4)))) else (if cl<120 then (if cl<36 then (h99_5) else (if cl<62 then (h99_6) else (h99_7))) else (if cl<236 then (h99_8) else (if cl<431 then (h99_9) else (h99_10))))
private theorem k99_1_0 : check w99 pick99 1 t5236 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k99_1_1 : check w99 pick99 1 t5243 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k99_1_2 : check w99 pick99 1 t5244 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w99 pick99 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5236 t5243 k99_1_0 k99_1_1
private theorem k99_1_3 : check w99 pick99 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k99_1_4 : check w99 pick99 1 t4252 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k99_1_5 : check w99 pick99 1 t4253 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w99 pick99 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t4252 k99_1_3 k99_1_4
private theorem k99_1_6 : check w99 pick99 1 t5245 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w99 pick99 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5244 t4253 k99_1_2 k99_1_5
private theorem k99_1_7 : check w99 pick99 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k99_1_8 : check w99 pick99 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k99_1_9 : check w99 pick99 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w99 pick99 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k99_1_7 k99_1_8
private theorem k99_1_10 : check w99 pick99 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k99_1_11 : check w99 pick99 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w99 pick99 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k99_1_9 k99_1_10
private theorem k99_1_12 : check w99 pick99 1 t5277 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w99 pick99 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5245 t5276 k99_1_6 k99_1_11
theorem cov99_1 : PA.Covered 1 (OZ.Valid 1 w99.low w99.t w99.y w99.r w99.cap) (P33.root 1) :=
  Night6836Tree.sound w99 pick99 1 t5277 _ k99_1_12
theorem cov99_2 : PA.Covered 2 (OZ.Valid 2 w99.low w99.t w99.y w99.r w99.cap) (P33.root 2) :=
  Night6836Tree.sound w99 pick99 2 t5222 _ (by decide +kernel)
theorem cov99_3 : PA.Covered 3 (OZ.Valid 3 w99.low w99.t w99.y w99.r w99.cap) (P33.root 3) :=
  Night6836Tree.sound w99 pick99 3 t564 _ (by decide +kernel)
theorem cov99_4 : PA.Covered 4 (OZ.Valid 4 w99.low w99.t w99.y w99.r w99.cap) (P33.root 4) :=
  Night6836Tree.sound w99 pick99 4 t565 _ (by decide +kernel)
theorem cov99_5 : PA.Covered 5 (OZ.Valid 5 w99.low w99.t w99.y w99.r w99.cap) (P33.root 5) :=
  Night6836Tree.sound w99 pick99 5 t566 _ (by decide +kernel)
theorem cov99_6 : PA.Covered 6 (OZ.Valid 6 w99.low w99.t w99.y w99.r w99.cap) (P33.root 6) :=
  Night6836Tree.sound w99 pick99 6 t567 _ (by decide +kernel)
theorem cov99_7 : PA.Covered 7 (OZ.Valid 7 w99.low w99.t w99.y w99.r w99.cap) (P33.root 7) :=
  Night6836Tree.sound w99 pick99 7 t2134 _ (by decide +kernel)
theorem window99 : P33.WindowCount w99 := by
  apply P33.window_count w99 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov99_1
  · exact cov99_2
  · exact cov99_3
  · exact cov99_4
  · exact cov99_5
  · exact cov99_6
  · exact cov99_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w100 : P33.Window := ⟨10,61,2253,1810,203689045811941769,164027,99000,5000000,81920000000⟩
def h100_0 : Height w100 := ⟨164027,99000,by decide +kernel⟩
def h100_1 : Height w100 := ⟨168054,96000,by decide +kernel⟩
def h100_2 : Height w100 := ⟨172309,93000,by decide +kernel⟩
def h100_3 : Height w100 := ⟨176822,90000,by decide +kernel⟩
def h100_4 : Height w100 := ⟨181634,87000,by decide +kernel⟩
def h100_5 : Height w100 := ⟨186789,84000,by decide +kernel⟩
def h100_6 : Height w100 := ⟨192344,81000,by decide +kernel⟩
def h100_7 : Height w100 := ⟨198369,78000,by decide +kernel⟩
def h100_8 : Height w100 := ⟨204949,75000,by decide +kernel⟩
def h100_9 : Height w100 := ⟨212194,72000,by decide +kernel⟩
def h100_10 : Height w100 := ⟨220241,69000,by decide +kernel⟩
def h100_11 : Height w100 := ⟨229269,66000,by decide +kernel⟩
def h100_12 : Height w100 := ⟨239517,63000,by decide +kernel⟩
def pick100 (cl : ℕ) : Height w100 := if cl<32 then (if cl<6 then (if cl<2 then (h100_0) else (if cl<4 then (h100_1) else (h100_2))) else (if cl<10 then (h100_3) else (if cl<18 then (h100_4) else (h100_5)))) else (if cl<107 then (if cl<40 then (h100_6) else (if cl<62 then (h100_7) else (h100_8))) else (if cl<282 then (if cl<192 then (h100_9) else (h100_10)) else (if cl<615 then (h100_11) else (h100_12))))
private theorem k100_1_0 : check w100 pick100 1 t5236 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k100_1_1 : check w100 pick100 1 t5243 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k100_1_2 : check w100 pick100 1 t5244 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w100 pick100 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5236 t5243 k100_1_0 k100_1_1
private theorem k100_1_3 : check w100 pick100 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k100_1_4 : check w100 pick100 1 t4252 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k100_1_5 : check w100 pick100 1 t4253 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w100 pick100 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t4252 k100_1_3 k100_1_4
private theorem k100_1_6 : check w100 pick100 1 t5245 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w100 pick100 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5244 t4253 k100_1_2 k100_1_5
private theorem k100_1_7 : check w100 pick100 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k100_1_8 : check w100 pick100 1 t5255 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k100_1_9 : check w100 pick100 1 t5256 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w100 pick100 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t5246 t5255 k100_1_7 k100_1_8
private theorem k100_1_10 : check w100 pick100 1 t5275 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k100_1_11 : check w100 pick100 1 t5276 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w100 pick100 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5256 t5275 k100_1_9 k100_1_10
private theorem k100_1_12 : check w100 pick100 1 t5277 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w100 pick100 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5245 t5276 k100_1_6 k100_1_11
theorem cov100_1 : PA.Covered 1 (OZ.Valid 1 w100.low w100.t w100.y w100.r w100.cap) (P33.root 1) :=
  Night6836Tree.sound w100 pick100 1 t5277 _ k100_1_12
theorem cov100_2 : PA.Covered 2 (OZ.Valid 2 w100.low w100.t w100.y w100.r w100.cap) (P33.root 2) :=
  Night6836Tree.sound w100 pick100 2 t5283 _ (by decide +kernel)
theorem cov100_3 : PA.Covered 3 (OZ.Valid 3 w100.low w100.t w100.y w100.r w100.cap) (P33.root 3) :=
  Night6836Tree.sound w100 pick100 3 t564 _ (by decide +kernel)
theorem cov100_4 : PA.Covered 4 (OZ.Valid 4 w100.low w100.t w100.y w100.r w100.cap) (P33.root 4) :=
  Night6836Tree.sound w100 pick100 4 t565 _ (by decide +kernel)
theorem cov100_5 : PA.Covered 5 (OZ.Valid 5 w100.low w100.t w100.y w100.r w100.cap) (P33.root 5) :=
  Night6836Tree.sound w100 pick100 5 t566 _ (by decide +kernel)
theorem cov100_6 : PA.Covered 6 (OZ.Valid 6 w100.low w100.t w100.y w100.r w100.cap) (P33.root 6) :=
  Night6836Tree.sound w100 pick100 6 t567 _ (by decide +kernel)
theorem cov100_7 : PA.Covered 7 (OZ.Valid 7 w100.low w100.t w100.y w100.r w100.cap) (P33.root 7) :=
  Night6836Tree.sound w100 pick100 7 t2134 _ (by decide +kernel)
theorem window100 : P33.WindowCount w100 := by
  apply P33.window_count w100 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov100_1
  · exact cov100_2
  · exact cov100_3
  · exact cov100_4
  · exact cov100_5
  · exact cov100_6
  · exact cov100_7
def w101 : P33.Window := ⟨11,19,7706,7673,236407173059072464,9341,15000,5000000,81920000000⟩
def h101_0 : Height w101 := ⟨9341,15000,by decide +kernel⟩
def h101_1 : Height w101 := ⟨15811,12000,by decide +kernel⟩
def pick101 (cl : ℕ) : Height w101 := if cl<55 then (h101_0) else (h101_1)
private theorem k101_1_0 : check w101 pick101 1 t5290 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k101_1_1 : check w101 pick101 1 t5292 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k101_1_2 : check w101 pick101 1 t5293 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w101 pick101 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t5290 t5292 k101_1_0 k101_1_1
private theorem k101_1_3 : check w101 pick101 1 t5308 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k101_1_4 : check w101 pick101 1 t5309 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w101 pick101 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t5293 t5308 k101_1_2 k101_1_3
private theorem k101_1_5 : check w101 pick101 1 t325 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k101_1_6 : check w101 pick101 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k101_1_7 : check w101 pick101 1 t383 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w101 pick101 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t325 t382 k101_1_5 k101_1_6
private theorem k101_1_8 : check w101 pick101 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k101_1_9 : check w101 pick101 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k101_1_10 : check w101 pick101 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w101 pick101 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k101_1_8 k101_1_9
private theorem k101_1_11 : check w101 pick101 1 t500 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w101 pick101 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t383 t499 k101_1_7 k101_1_10
private theorem k101_1_12 : check w101 pick101 1 t5310 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w101 pick101 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5309 t500 k101_1_4 k101_1_11
theorem cov101_1 : PA.Covered 1 (OZ.Valid 1 w101.low w101.t w101.y w101.r w101.cap) (P33.root 1) :=
  Night6836Tree.sound w101 pick101 1 t5310 _ k101_1_12
theorem cov101_2 : PA.Covered 2 (OZ.Valid 2 w101.low w101.t w101.y w101.r w101.cap) (P33.root 2) :=
  Night6836Tree.sound w101 pick101 2 t5320 _ (by decide +kernel)
theorem cov101_3 : PA.Covered 3 (OZ.Valid 3 w101.low w101.t w101.y w101.r w101.cap) (P33.root 3) :=
  Night6836Tree.sound w101 pick101 3 t564 _ (by decide +kernel)
theorem cov101_4 : PA.Covered 4 (OZ.Valid 4 w101.low w101.t w101.y w101.r w101.cap) (P33.root 4) :=
  Night6836Tree.sound w101 pick101 4 t565 _ (by decide +kernel)
theorem cov101_5 : PA.Covered 5 (OZ.Valid 5 w101.low w101.t w101.y w101.r w101.cap) (P33.root 5) :=
  Night6836Tree.sound w101 pick101 5 t566 _ (by decide +kernel)
theorem cov101_6 : PA.Covered 6 (OZ.Valid 6 w101.low w101.t w101.y w101.r w101.cap) (P33.root 6) :=
  Night6836Tree.sound w101 pick101 6 t567 _ (by decide +kernel)
theorem cov101_7 : PA.Covered 7 (OZ.Valid 7 w101.low w101.t w101.y w101.r w101.cap) (P33.root 7) :=
  Night6836Tree.sound w101 pick101 7 t568 _ (by decide +kernel)
theorem window101 : P33.WindowCount w101 := by
  apply P33.window_count w101 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov101_1
  · exact cov101_2
  · exact cov101_3
  · exact cov101_4
  · exact cov101_5
  · exact cov101_6
  · exact cov101_7
def w102 : P33.Window := ⟨11,20,7672,7512,240506177983533674,7266,18000,5000000,81920000000⟩
def h102_0 : Height w102 := ⟨7266,18000,by decide +kernel⟩
def h102_1 : Height w102 := ⟨11343,15000,by decide +kernel⟩
def h102_2 : Height w102 := ⟨18702,12000,by decide +kernel⟩
def pick102 (cl : ℕ) : Height w102 := if cl<2 then (h102_0) else (if cl<117 then (h102_1) else (h102_2))
private theorem k102_1_0 : check w102 pick102 1 t5290 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k102_1_1 : check w102 pick102 1 t5292 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k102_1_2 : check w102 pick102 1 t5293 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w102 pick102 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t5290 t5292 k102_1_0 k102_1_1
private theorem k102_1_3 : check w102 pick102 1 t5308 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k102_1_4 : check w102 pick102 1 t5309 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w102 pick102 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t5293 t5308 k102_1_2 k102_1_3
private theorem k102_1_5 : check w102 pick102 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k102_1_6 : check w102 pick102 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k102_1_7 : check w102 pick102 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w102 pick102 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k102_1_5 k102_1_6
private theorem k102_1_8 : check w102 pick102 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k102_1_9 : check w102 pick102 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k102_1_10 : check w102 pick102 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w102 pick102 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k102_1_8 k102_1_9
private theorem k102_1_11 : check w102 pick102 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w102 pick102 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k102_1_7 k102_1_10
private theorem k102_1_12 : check w102 pick102 1 t5321 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w102 pick102 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5309 t2461 k102_1_4 k102_1_11
theorem cov102_1 : PA.Covered 1 (OZ.Valid 1 w102.low w102.t w102.y w102.r w102.cap) (P33.root 1) :=
  Night6836Tree.sound w102 pick102 1 t5321 _ k102_1_12
theorem cov102_2 : PA.Covered 2 (OZ.Valid 2 w102.low w102.t w102.y w102.r w102.cap) (P33.root 2) :=
  Night6836Tree.sound w102 pick102 2 t5320 _ (by decide +kernel)
theorem cov102_3 : PA.Covered 3 (OZ.Valid 3 w102.low w102.t w102.y w102.r w102.cap) (P33.root 3) :=
  Night6836Tree.sound w102 pick102 3 t564 _ (by decide +kernel)
theorem cov102_4 : PA.Covered 4 (OZ.Valid 4 w102.low w102.t w102.y w102.r w102.cap) (P33.root 4) :=
  Night6836Tree.sound w102 pick102 4 t565 _ (by decide +kernel)
theorem cov102_5 : PA.Covered 5 (OZ.Valid 5 w102.low w102.t w102.y w102.r w102.cap) (P33.root 5) :=
  Night6836Tree.sound w102 pick102 5 t566 _ (by decide +kernel)
theorem cov102_6 : PA.Covered 6 (OZ.Valid 6 w102.low w102.t w102.y w102.r w102.cap) (P33.root 6) :=
  Night6836Tree.sound w102 pick102 6 t567 _ (by decide +kernel)
theorem cov102_7 : PA.Covered 7 (OZ.Valid 7 w102.low w102.t w102.y w102.r w102.cap) (P33.root 7) :=
  Night6836Tree.sound w102 pick102 7 t568 _ (by decide +kernel)
theorem window102 : P33.WindowCount w102 := by
  apply P33.window_count w102 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov102_1
  · exact cov102_2
  · exact cov102_3
  · exact cov102_4
  · exact cov102_5
  · exact cov102_6
  · exact cov102_7
def w103 : P33.Window := ⟨11,21,7637,7602,239792310823328380,8043,18000,5000000,81920000000⟩
def h103_0 : Height w103 := ⟨8043,18000,by decide +kernel⟩
def h103_1 : Height w103 := ⟨12181,15000,by decide +kernel⟩
def h103_2 : Height w103 := ⟨19616,12000,by decide +kernel⟩
def pick103 (cl : ℕ) : Height w103 := if cl<3 then (h103_0) else (if cl<132 then (h103_1) else (h103_2))
private theorem k103_1_0 : check w103 pick103 1 t5326 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k103_1_1 : check w103 pick103 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k103_1_2 : check w103 pick103 1 t5327 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w103 pick103 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5326 t2652 k103_1_0 k103_1_1
private theorem k103_1_3 : check w103 pick103 1 t2676 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k103_1_4 : check w103 pick103 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k103_1_5 : check w103 pick103 1 t5328 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w103 pick103 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2676 t5307 k103_1_3 k103_1_4
private theorem k103_1_6 : check w103 pick103 1 t5329 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w103 pick103 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5327 t5328 k103_1_2 k103_1_5
private theorem k103_1_7 : check w103 pick103 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k103_1_8 : check w103 pick103 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k103_1_9 : check w103 pick103 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w103 pick103 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k103_1_7 k103_1_8
private theorem k103_1_10 : check w103 pick103 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k103_1_11 : check w103 pick103 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k103_1_12 : check w103 pick103 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w103 pick103 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k103_1_10 k103_1_11
private theorem k103_1_13 : check w103 pick103 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w103 pick103 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k103_1_9 k103_1_12
private theorem k103_1_14 : check w103 pick103 1 t5330 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w103 pick103 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5329 t2461 k103_1_6 k103_1_13
theorem cov103_1 : PA.Covered 1 (OZ.Valid 1 w103.low w103.t w103.y w103.r w103.cap) (P33.root 1) :=
  Night6836Tree.sound w103 pick103 1 t5330 _ k103_1_14
theorem cov103_2 : PA.Covered 2 (OZ.Valid 2 w103.low w103.t w103.y w103.r w103.cap) (P33.root 2) :=
  Night6836Tree.sound w103 pick103 2 t5320 _ (by decide +kernel)
theorem cov103_3 : PA.Covered 3 (OZ.Valid 3 w103.low w103.t w103.y w103.r w103.cap) (P33.root 3) :=
  Night6836Tree.sound w103 pick103 3 t564 _ (by decide +kernel)
theorem cov103_4 : PA.Covered 4 (OZ.Valid 4 w103.low w103.t w103.y w103.r w103.cap) (P33.root 4) :=
  Night6836Tree.sound w103 pick103 4 t565 _ (by decide +kernel)
theorem cov103_5 : PA.Covered 5 (OZ.Valid 5 w103.low w103.t w103.y w103.r w103.cap) (P33.root 5) :=
  Night6836Tree.sound w103 pick103 5 t566 _ (by decide +kernel)
theorem cov103_6 : PA.Covered 6 (OZ.Valid 6 w103.low w103.t w103.y w103.r w103.cap) (P33.root 6) :=
  Night6836Tree.sound w103 pick103 6 t567 _ (by decide +kernel)
theorem cov103_7 : PA.Covered 7 (OZ.Valid 7 w103.low w103.t w103.y w103.r w103.cap) (P33.root 7) :=
  Night6836Tree.sound w103 pick103 7 t568 _ (by decide +kernel)
theorem window103 : P33.WindowCount w103 := by
  apply P33.window_count w103 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov103_1
  · exact cov103_2
  · exact cov103_3
  · exact cov103_4
  · exact cov103_5
  · exact cov103_6
  · exact cov103_7
def w104 : P33.Window := ⟨11,22,7601,7567,241628225236091553,9282,18000,5000000,81920000000⟩
def h104_0 : Height w104 := ⟨9282,18000,by decide +kernel⟩
def h104_1 : Height w104 := ⟨13636,15000,by decide +kernel⟩
def h104_2 : Height w104 := ⟨21580,12000,by decide +kernel⟩
def pick104 (cl : ℕ) : Height w104 := if cl<5 then (h104_0) else (if cl<181 then (h104_1) else (h104_2))
private theorem k104_1_0 : check w104 pick104 1 t5331 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k104_1_1 : check w104 pick104 1 t5340 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k104_1_2 : check w104 pick104 1 t5341 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w104 pick104 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5331 t5340 k104_1_0 k104_1_1
private theorem k104_1_3 : check w104 pick104 1 t2676 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k104_1_4 : check w104 pick104 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k104_1_5 : check w104 pick104 1 t5328 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w104 pick104 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2676 t5307 k104_1_3 k104_1_4
private theorem k104_1_6 : check w104 pick104 1 t5342 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w104 pick104 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5341 t5328 k104_1_2 k104_1_5
private theorem k104_1_7 : check w104 pick104 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k104_1_8 : check w104 pick104 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k104_1_9 : check w104 pick104 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w104 pick104 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k104_1_7 k104_1_8
private theorem k104_1_10 : check w104 pick104 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k104_1_11 : check w104 pick104 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k104_1_12 : check w104 pick104 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w104 pick104 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k104_1_10 k104_1_11
private theorem k104_1_13 : check w104 pick104 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w104 pick104 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k104_1_9 k104_1_12
private theorem k104_1_14 : check w104 pick104 1 t5343 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w104 pick104 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5342 t2461 k104_1_6 k104_1_13
theorem cov104_1 : PA.Covered 1 (OZ.Valid 1 w104.low w104.t w104.y w104.r w104.cap) (P33.root 1) :=
  Night6836Tree.sound w104 pick104 1 t5343 _ k104_1_14
theorem cov104_2 : PA.Covered 2 (OZ.Valid 2 w104.low w104.t w104.y w104.r w104.cap) (P33.root 2) :=
  Night6836Tree.sound w104 pick104 2 t5366 _ (by decide +kernel)
theorem cov104_3 : PA.Covered 3 (OZ.Valid 3 w104.low w104.t w104.y w104.r w104.cap) (P33.root 3) :=
  Night6836Tree.sound w104 pick104 3 t564 _ (by decide +kernel)
theorem cov104_4 : PA.Covered 4 (OZ.Valid 4 w104.low w104.t w104.y w104.r w104.cap) (P33.root 4) :=
  Night6836Tree.sound w104 pick104 4 t565 _ (by decide +kernel)
theorem cov104_5 : PA.Covered 5 (OZ.Valid 5 w104.low w104.t w104.y w104.r w104.cap) (P33.root 5) :=
  Night6836Tree.sound w104 pick104 5 t566 _ (by decide +kernel)
theorem cov104_6 : PA.Covered 6 (OZ.Valid 6 w104.low w104.t w104.y w104.r w104.cap) (P33.root 6) :=
  Night6836Tree.sound w104 pick104 6 t567 _ (by decide +kernel)
theorem cov104_7 : PA.Covered 7 (OZ.Valid 7 w104.low w104.t w104.y w104.r w104.cap) (P33.root 7) :=
  Night6836Tree.sound w104 pick104 7 t568 _ (by decide +kernel)
theorem window104 : P33.WindowCount w104 := by
  apply P33.window_count w104 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov104_1
  · exact cov104_2
  · exact cov104_3
  · exact cov104_4
  · exact cov104_5
  · exact cov104_6
  · exact cov104_7
def w105 : P33.Window := ⟨11,23,5822,4823,194201724636757617,17885,27000,5000000,81920000000⟩
def h105_0 : Height w105 := ⟨17885,27000,by decide +kernel⟩
def h105_1 : Height w105 := ⟨24425,23000,by decide +kernel⟩
def h105_2 : Height w105 := ⟨35687,19000,by decide +kernel⟩
def pick105 (cl : ℕ) : Height w105 := if cl<12 then (h105_0) else (if cl<232 then (h105_1) else (h105_2))
private theorem k105_1_0 : check w105 pick105 1 t5290 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k105_1_1 : check w105 pick105 1 t5292 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k105_1_2 : check w105 pick105 1 t5293 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w105 pick105 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t5290 t5292 k105_1_0 k105_1_1
private theorem k105_1_3 : check w105 pick105 1 t5369 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k105_1_4 : check w105 pick105 1 t5370 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w105 pick105 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t5293 t5369 k105_1_2 k105_1_3
private theorem k105_1_5 : check w105 pick105 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k105_1_6 : check w105 pick105 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k105_1_7 : check w105 pick105 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w105 pick105 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k105_1_5 k105_1_6
private theorem k105_1_8 : check w105 pick105 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k105_1_9 : check w105 pick105 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k105_1_10 : check w105 pick105 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w105 pick105 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k105_1_8 k105_1_9
private theorem k105_1_11 : check w105 pick105 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w105 pick105 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k105_1_7 k105_1_10
private theorem k105_1_12 : check w105 pick105 1 t5371 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w105 pick105 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5370 t2461 k105_1_4 k105_1_11
theorem cov105_1 : PA.Covered 1 (OZ.Valid 1 w105.low w105.t w105.y w105.r w105.cap) (P33.root 1) :=
  Night6836Tree.sound w105 pick105 1 t5371 _ k105_1_12
theorem cov105_2 : PA.Covered 2 (OZ.Valid 2 w105.low w105.t w105.y w105.r w105.cap) (P33.root 2) :=
  Night6836Tree.sound w105 pick105 2 t5320 _ (by decide +kernel)
theorem cov105_3 : PA.Covered 3 (OZ.Valid 3 w105.low w105.t w105.y w105.r w105.cap) (P33.root 3) :=
  Night6836Tree.sound w105 pick105 3 t564 _ (by decide +kernel)
theorem cov105_4 : PA.Covered 4 (OZ.Valid 4 w105.low w105.t w105.y w105.r w105.cap) (P33.root 4) :=
  Night6836Tree.sound w105 pick105 4 t565 _ (by decide +kernel)
theorem cov105_5 : PA.Covered 5 (OZ.Valid 5 w105.low w105.t w105.y w105.r w105.cap) (P33.root 5) :=
  Night6836Tree.sound w105 pick105 5 t566 _ (by decide +kernel)
theorem cov105_6 : PA.Covered 6 (OZ.Valid 6 w105.low w105.t w105.y w105.r w105.cap) (P33.root 6) :=
  Night6836Tree.sound w105 pick105 6 t567 _ (by decide +kernel)
theorem cov105_7 : PA.Covered 7 (OZ.Valid 7 w105.low w105.t w105.y w105.r w105.cap) (P33.root 7) :=
  Night6836Tree.sound w105 pick105 7 t2134 _ (by decide +kernel)
theorem window105 : P33.WindowCount w105 := by
  apply P33.window_count w105 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov105_1
  · exact cov105_2
  · exact cov105_3
  · exact cov105_4
  · exact cov105_5
  · exact cov105_6
  · exact cov105_7
def w106 : P33.Window := ⟨11,23,7415,6466,240994077299177207,12236,21000,5000000,81920000000⟩
def h106_0 : Height w106 := ⟨12236,21000,by decide +kernel⟩
def h106_1 : Height w106 := ⟨16633,18000,by decide +kernel⟩
def h106_2 : Height w106 := ⟨23685,15000,by decide +kernel⟩
def h106_3 : Height w106 := ⟨40087,12000,by decide +kernel⟩
def pick106 (cl : ℕ) : Height w106 := if cl<100 then (if cl<5 then (h106_0) else (h106_1)) else (if cl<1021 then (h106_2) else (h106_3))
private theorem k106_1_0 : check w106 pick106 1 t5331 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k106_1_1 : check w106 pick106 1 t5340 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k106_1_2 : check w106 pick106 1 t5341 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w106 pick106 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5331 t5340 k106_1_0 k106_1_1
private theorem k106_1_3 : check w106 pick106 1 t2676 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k106_1_4 : check w106 pick106 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k106_1_5 : check w106 pick106 1 t5328 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w106 pick106 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2676 t5307 k106_1_3 k106_1_4
private theorem k106_1_6 : check w106 pick106 1 t5342 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w106 pick106 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5341 t5328 k106_1_2 k106_1_5
private theorem k106_1_7 : check w106 pick106 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k106_1_8 : check w106 pick106 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k106_1_9 : check w106 pick106 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w106 pick106 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k106_1_7 k106_1_8
private theorem k106_1_10 : check w106 pick106 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k106_1_11 : check w106 pick106 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k106_1_12 : check w106 pick106 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w106 pick106 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k106_1_10 k106_1_11
private theorem k106_1_13 : check w106 pick106 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w106 pick106 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k106_1_9 k106_1_12
private theorem k106_1_14 : check w106 pick106 1 t5343 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w106 pick106 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5342 t2461 k106_1_6 k106_1_13
theorem cov106_1 : PA.Covered 1 (OZ.Valid 1 w106.low w106.t w106.y w106.r w106.cap) (P33.root 1) :=
  Night6836Tree.sound w106 pick106 1 t5343 _ k106_1_14
theorem cov106_2 : PA.Covered 2 (OZ.Valid 2 w106.low w106.t w106.y w106.r w106.cap) (P33.root 2) :=
  Night6836Tree.sound w106 pick106 2 t5366 _ (by decide +kernel)
theorem cov106_3 : PA.Covered 3 (OZ.Valid 3 w106.low w106.t w106.y w106.r w106.cap) (P33.root 3) :=
  Night6836Tree.sound w106 pick106 3 t564 _ (by decide +kernel)
theorem cov106_4 : PA.Covered 4 (OZ.Valid 4 w106.low w106.t w106.y w106.r w106.cap) (P33.root 4) :=
  Night6836Tree.sound w106 pick106 4 t565 _ (by decide +kernel)
theorem cov106_5 : PA.Covered 5 (OZ.Valid 5 w106.low w106.t w106.y w106.r w106.cap) (P33.root 5) :=
  Night6836Tree.sound w106 pick106 5 t566 _ (by decide +kernel)
theorem cov106_6 : PA.Covered 6 (OZ.Valid 6 w106.low w106.t w106.y w106.r w106.cap) (P33.root 6) :=
  Night6836Tree.sound w106 pick106 6 t567 _ (by decide +kernel)
theorem cov106_7 : PA.Covered 7 (OZ.Valid 7 w106.low w106.t w106.y w106.r w106.cap) (P33.root 7) :=
  Night6836Tree.sound w106 pick106 7 t568 _ (by decide +kernel)
theorem window106 : P33.WindowCount w106 := by
  apply P33.window_count w106 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov106_1
  · exact cov106_2
  · exact cov106_3
  · exact cov106_4
  · exact cov106_5
  · exact cov106_6
  · exact cov106_7
def w107 : P33.Window := ⟨11,23,7566,7491,243930674116209925,10720,18000,5000000,81920000000⟩
def h107_0 : Height w107 := ⟨10720,18000,by decide +kernel⟩
def h107_1 : Height w107 := ⟨15358,15000,by decide +kernel⟩
def h107_2 : Height w107 := ⟨24003,12000,by decide +kernel⟩
def pick107 (cl : ℕ) : Height w107 := if cl<6 then (h107_0) else (if cl<257 then (h107_1) else (h107_2))
private theorem k107_1_0 : check w107 pick107 1 t5331 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k107_1_1 : check w107 pick107 1 t5340 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k107_1_2 : check w107 pick107 1 t5341 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w107 pick107 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5331 t5340 k107_1_0 k107_1_1
private theorem k107_1_3 : check w107 pick107 1 t2805 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k107_1_4 : check w107 pick107 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k107_1_5 : check w107 pick107 1 t5372 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w107 pick107 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2805 t5307 k107_1_3 k107_1_4
private theorem k107_1_6 : check w107 pick107 1 t5373 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w107 pick107 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5341 t5372 k107_1_2 k107_1_5
private theorem k107_1_7 : check w107 pick107 1 t5246 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k107_1_8 : check w107 pick107 1 t2846 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k107_1_9 : check w107 pick107 1 t5374 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w107 pick107 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t5246 t2846 k107_1_7 k107_1_8
private theorem k107_1_10 : check w107 pick107 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k107_1_11 : check w107 pick107 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k107_1_12 : check w107 pick107 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w107 pick107 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k107_1_10 k107_1_11
private theorem k107_1_13 : check w107 pick107 1 t5375 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w107 pick107 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t5374 t2855 k107_1_9 k107_1_12
private theorem k107_1_14 : check w107 pick107 1 t5376 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w107 pick107 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5373 t5375 k107_1_6 k107_1_13
theorem cov107_1 : PA.Covered 1 (OZ.Valid 1 w107.low w107.t w107.y w107.r w107.cap) (P33.root 1) :=
  Night6836Tree.sound w107 pick107 1 t5376 _ k107_1_14
theorem cov107_2 : PA.Covered 2 (OZ.Valid 2 w107.low w107.t w107.y w107.r w107.cap) (P33.root 2) :=
  Night6836Tree.sound w107 pick107 2 t5379 _ (by decide +kernel)
theorem cov107_3 : PA.Covered 3 (OZ.Valid 3 w107.low w107.t w107.y w107.r w107.cap) (P33.root 3) :=
  Night6836Tree.sound w107 pick107 3 t564 _ (by decide +kernel)
theorem cov107_4 : PA.Covered 4 (OZ.Valid 4 w107.low w107.t w107.y w107.r w107.cap) (P33.root 4) :=
  Night6836Tree.sound w107 pick107 4 t565 _ (by decide +kernel)
theorem cov107_5 : PA.Covered 5 (OZ.Valid 5 w107.low w107.t w107.y w107.r w107.cap) (P33.root 5) :=
  Night6836Tree.sound w107 pick107 5 t566 _ (by decide +kernel)
theorem cov107_6 : PA.Covered 6 (OZ.Valid 6 w107.low w107.t w107.y w107.r w107.cap) (P33.root 6) :=
  Night6836Tree.sound w107 pick107 6 t567 _ (by decide +kernel)
theorem cov107_7 : PA.Covered 7 (OZ.Valid 7 w107.low w107.t w107.y w107.r w107.cap) (P33.root 7) :=
  Night6836Tree.sound w107 pick107 7 t568 _ (by decide +kernel)
theorem window107 : P33.WindowCount w107 := by
  apply P33.window_count w107 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov107_1
  · exact cov107_2
  · exact cov107_3
  · exact cov107_4
  · exact cov107_5
  · exact cov107_6
  · exact cov107_7
def w108 : P33.Window := ⟨11,24,5823,4824,198847979367304340,19663,27000,5000000,81920000000⟩
def h108_0 : Height w108 := ⟨19663,27000,by decide +kernel⟩
def h108_1 : Height w108 := ⟨26456,23000,by decide +kernel⟩
def h108_2 : Height w108 := ⟨38227,19000,by decide +kernel⟩
def pick108 (cl : ℕ) : Height w108 := if cl<18 then (h108_0) else (if cl<269 then (h108_1) else (h108_2))
private theorem k108_1_0 : check w108 pick108 1 t5290 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k108_1_1 : check w108 pick108 1 t5292 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k108_1_2 : check w108 pick108 1 t5293 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w108 pick108 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t5290 t5292 k108_1_0 k108_1_1
private theorem k108_1_3 : check w108 pick108 1 t5369 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k108_1_4 : check w108 pick108 1 t5370 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w108 pick108 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t5293 t5369 k108_1_2 k108_1_3
private theorem k108_1_5 : check w108 pick108 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k108_1_6 : check w108 pick108 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k108_1_7 : check w108 pick108 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w108 pick108 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k108_1_5 k108_1_6
private theorem k108_1_8 : check w108 pick108 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k108_1_9 : check w108 pick108 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k108_1_10 : check w108 pick108 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w108 pick108 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k108_1_8 k108_1_9
private theorem k108_1_11 : check w108 pick108 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w108 pick108 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k108_1_7 k108_1_10
private theorem k108_1_12 : check w108 pick108 1 t5371 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w108 pick108 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5370 t2461 k108_1_4 k108_1_11
theorem cov108_1 : PA.Covered 1 (OZ.Valid 1 w108.low w108.t w108.y w108.r w108.cap) (P33.root 1) :=
  Night6836Tree.sound w108 pick108 1 t5371 _ k108_1_12
theorem cov108_2 : PA.Covered 2 (OZ.Valid 2 w108.low w108.t w108.y w108.r w108.cap) (P33.root 2) :=
  Night6836Tree.sound w108 pick108 2 t5320 _ (by decide +kernel)
theorem cov108_3 : PA.Covered 3 (OZ.Valid 3 w108.low w108.t w108.y w108.r w108.cap) (P33.root 3) :=
  Night6836Tree.sound w108 pick108 3 t564 _ (by decide +kernel)
theorem cov108_4 : PA.Covered 4 (OZ.Valid 4 w108.low w108.t w108.y w108.r w108.cap) (P33.root 4) :=
  Night6836Tree.sound w108 pick108 4 t565 _ (by decide +kernel)
theorem cov108_5 : PA.Covered 5 (OZ.Valid 5 w108.low w108.t w108.y w108.r w108.cap) (P33.root 5) :=
  Night6836Tree.sound w108 pick108 5 t566 _ (by decide +kernel)
theorem cov108_6 : PA.Covered 6 (OZ.Valid 6 w108.low w108.t w108.y w108.r w108.cap) (P33.root 6) :=
  Night6836Tree.sound w108 pick108 6 t567 _ (by decide +kernel)
theorem cov108_7 : PA.Covered 7 (OZ.Valid 7 w108.low w108.t w108.y w108.r w108.cap) (P33.root 7) :=
  Night6836Tree.sound w108 pick108 7 t2134 _ (by decide +kernel)
theorem window108 : P33.WindowCount w108 := by
  apply P33.window_count w108 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov108_1
  · exact cov108_2
  · exact cov108_3
  · exact cov108_4
  · exact cov108_5
  · exact cov108_6
  · exact cov108_7
def w109 : P33.Window := ⟨11,24,7530,7491,244496139528588804,11846,18000,5000000,81920000000⟩
def h109_0 : Height w109 := ⟨11846,18000,by decide +kernel⟩
def h109_1 : Height w109 := ⟨16662,15000,by decide +kernel⟩
def h109_2 : Height w109 := ⟨25709,12000,by decide +kernel⟩
def pick109 (cl : ℕ) : Height w109 := if cl<10 then (h109_0) else (if cl<282 then (h109_1) else (h109_2))
private theorem k109_1_0 : check w109 pick109 1 t5384 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k109_1_1 : check w109 pick109 1 t5390 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k109_1_2 : check w109 pick109 1 t5391 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w109 pick109 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5384 t5390 k109_1_0 k109_1_1
private theorem k109_1_3 : check w109 pick109 1 t5393 ⟨1,7,2,16,1,20,77,138⟩ = true := by decide +kernel
private theorem k109_1_4 : check w109 pick109 1 t5403 ⟨1,7,2,16,21,52,77,138⟩ = true := by decide +kernel
private theorem k109_1_5 : check w109 pick109 1 t5404 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w109 pick109 1 ⟨1,7,2,16,1,52,77,138⟩ 2 20 t5393 t5403 k109_1_3 k109_1_4
private theorem k109_1_6 : check w109 pick109 1 t5405 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w109 pick109 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5391 t5404 k109_1_2 k109_1_5
private theorem k109_1_7 : check w109 pick109 1 t2839 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k109_1_8 : check w109 pick109 1 t2846 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k109_1_9 : check w109 pick109 1 t2847 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w109 pick109 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t2839 t2846 k109_1_7 k109_1_8
private theorem k109_1_10 : check w109 pick109 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k109_1_11 : check w109 pick109 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k109_1_12 : check w109 pick109 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w109 pick109 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k109_1_10 k109_1_11
private theorem k109_1_13 : check w109 pick109 1 t2856 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w109 pick109 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t2847 t2855 k109_1_9 k109_1_12
private theorem k109_1_14 : check w109 pick109 1 t5406 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w109 pick109 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5405 t2856 k109_1_6 k109_1_13
theorem cov109_1 : PA.Covered 1 (OZ.Valid 1 w109.low w109.t w109.y w109.r w109.cap) (P33.root 1) :=
  Night6836Tree.sound w109 pick109 1 t5406 _ k109_1_14
private theorem k109_2_0 : check w109 pick109 2 t5409 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k109_2_1 : check w109 pick109 2 t5411 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k109_2_2 : check w109 pick109 2 t5412 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w109 pick109 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5409 t5411 k109_2_0 k109_2_1
theorem cov109_2 : PA.Covered 2 (OZ.Valid 2 w109.low w109.t w109.y w109.r w109.cap) (P33.root 2) :=
  Night6836Tree.sound w109 pick109 2 t5412 _ k109_2_2
theorem cov109_3 : PA.Covered 3 (OZ.Valid 3 w109.low w109.t w109.y w109.r w109.cap) (P33.root 3) :=
  Night6836Tree.sound w109 pick109 3 t564 _ (by decide +kernel)
theorem cov109_4 : PA.Covered 4 (OZ.Valid 4 w109.low w109.t w109.y w109.r w109.cap) (P33.root 4) :=
  Night6836Tree.sound w109 pick109 4 t565 _ (by decide +kernel)
theorem cov109_5 : PA.Covered 5 (OZ.Valid 5 w109.low w109.t w109.y w109.r w109.cap) (P33.root 5) :=
  Night6836Tree.sound w109 pick109 5 t566 _ (by decide +kernel)
theorem cov109_6 : PA.Covered 6 (OZ.Valid 6 w109.low w109.t w109.y w109.r w109.cap) (P33.root 6) :=
  Night6836Tree.sound w109 pick109 6 t567 _ (by decide +kernel)
theorem cov109_7 : PA.Covered 7 (OZ.Valid 7 w109.low w109.t w109.y w109.r w109.cap) (P33.root 7) :=
  Night6836Tree.sound w109 pick109 7 t568 _ (by decide +kernel)
theorem window109 : P33.WindowCount w109 := by
  apply P33.window_count w109 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov109_1
  · exact cov109_2
  · exact cov109_3
  · exact cov109_4
  · exact cov109_5
  · exact cov109_6
  · exact cov109_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w110 : P33.Window := ⟨11,25,5824,4825,203782154834488169,21439,27000,5000000,81920000000⟩
def h110_0 : Height w110 := ⟨21439,27000,by decide +kernel⟩
def h110_1 : Height w110 := ⟨28484,23000,by decide +kernel⟩
def h110_2 : Height w110 := ⟨40763,19000,by decide +kernel⟩
def pick110 (cl : ℕ) : Height w110 := if cl<32 then (h110_0) else (if cl<302 then (h110_1) else (h110_2))
private theorem k110_1_0 : check w110 pick110 1 t5413 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k110_1_1 : check w110 pick110 1 t2652 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k110_1_2 : check w110 pick110 1 t5414 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w110 pick110 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5413 t2652 k110_1_0 k110_1_1
private theorem k110_1_3 : check w110 pick110 1 t2805 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k110_1_4 : check w110 pick110 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k110_1_5 : check w110 pick110 1 t5372 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w110 pick110 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2805 t5307 k110_1_3 k110_1_4
private theorem k110_1_6 : check w110 pick110 1 t5415 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w110 pick110 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5414 t5372 k110_1_2 k110_1_5
private theorem k110_1_7 : check w110 pick110 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k110_1_8 : check w110 pick110 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k110_1_9 : check w110 pick110 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w110 pick110 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k110_1_7 k110_1_8
private theorem k110_1_10 : check w110 pick110 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k110_1_11 : check w110 pick110 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k110_1_12 : check w110 pick110 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w110 pick110 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k110_1_10 k110_1_11
private theorem k110_1_13 : check w110 pick110 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w110 pick110 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k110_1_9 k110_1_12
private theorem k110_1_14 : check w110 pick110 1 t5416 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w110 pick110 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5415 t2461 k110_1_6 k110_1_13
theorem cov110_1 : PA.Covered 1 (OZ.Valid 1 w110.low w110.t w110.y w110.r w110.cap) (P33.root 1) :=
  Night6836Tree.sound w110 pick110 1 t5416 _ k110_1_14
theorem cov110_2 : PA.Covered 2 (OZ.Valid 2 w110.low w110.t w110.y w110.r w110.cap) (P33.root 2) :=
  Night6836Tree.sound w110 pick110 2 t5320 _ (by decide +kernel)
theorem cov110_3 : PA.Covered 3 (OZ.Valid 3 w110.low w110.t w110.y w110.r w110.cap) (P33.root 3) :=
  Night6836Tree.sound w110 pick110 3 t564 _ (by decide +kernel)
theorem cov110_4 : PA.Covered 4 (OZ.Valid 4 w110.low w110.t w110.y w110.r w110.cap) (P33.root 4) :=
  Night6836Tree.sound w110 pick110 4 t565 _ (by decide +kernel)
theorem cov110_5 : PA.Covered 5 (OZ.Valid 5 w110.low w110.t w110.y w110.r w110.cap) (P33.root 5) :=
  Night6836Tree.sound w110 pick110 5 t566 _ (by decide +kernel)
theorem cov110_6 : PA.Covered 6 (OZ.Valid 6 w110.low w110.t w110.y w110.r w110.cap) (P33.root 6) :=
  Night6836Tree.sound w110 pick110 6 t567 _ (by decide +kernel)
theorem cov110_7 : PA.Covered 7 (OZ.Valid 7 w110.low w110.t w110.y w110.r w110.cap) (P33.root 7) :=
  Night6836Tree.sound w110 pick110 7 t2134 _ (by decide +kernel)
theorem window110 : P33.WindowCount w110 := by
  apply P33.window_count w110 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov110_1
  · exact cov110_2
  · exact cov110_3
  · exact cov110_4
  · exact cov110_5
  · exact cov110_6
  · exact cov110_7
def w111 : P33.Window := ⟨11,25,7490,7451,230064781700249495,13171,18000,5000000,81920000000⟩
def h111_0 : Height w111 := ⟨13171,18000,by decide +kernel⟩
def h111_1 : Height w111 := ⟨18233,15000,by decide +kernel⟩
def h111_2 : Height w111 := ⟨27877,12000,by decide +kernel⟩
def pick111 (cl : ℕ) : Height w111 := if cl<18 then (h111_0) else (if cl<343 then (h111_1) else (h111_2))
private theorem k111_1_0 : check w111 pick111 1 t5418 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k111_1_1 : check w111 pick111 1 t5421 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k111_1_2 : check w111 pick111 1 t5422 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w111 pick111 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5418 t5421 k111_1_0 k111_1_1
private theorem k111_1_3 : check w111 pick111 1 t5426 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k111_1_4 : check w111 pick111 1 t5435 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k111_1_5 : check w111 pick111 1 t5436 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w111 pick111 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t5426 t5435 k111_1_3 k111_1_4
private theorem k111_1_6 : check w111 pick111 1 t5437 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w111 pick111 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5422 t5436 k111_1_2 k111_1_5
private theorem k111_1_7 : check w111 pick111 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k111_1_8 : check w111 pick111 1 t5455 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k111_1_9 : check w111 pick111 1 t5456 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w111 pick111 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t5455 k111_1_7 k111_1_8
private theorem k111_1_10 : check w111 pick111 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k111_1_11 : check w111 pick111 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k111_1_12 : check w111 pick111 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w111 pick111 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k111_1_10 k111_1_11
private theorem k111_1_13 : check w111 pick111 1 t5457 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w111 pick111 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5456 t2855 k111_1_9 k111_1_12
private theorem k111_1_14 : check w111 pick111 1 t5458 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w111 pick111 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5437 t5457 k111_1_6 k111_1_13
theorem cov111_1 : PA.Covered 1 (OZ.Valid 1 w111.low w111.t w111.y w111.r w111.cap) (P33.root 1) :=
  Night6836Tree.sound w111 pick111 1 t5458 _ k111_1_14
private theorem k111_2_0 : check w111 pick111 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k111_2_1 : check w111 pick111 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k111_2_2 : check w111 pick111 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w111 pick111 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k111_2_0 k111_2_1
theorem cov111_2 : PA.Covered 2 (OZ.Valid 2 w111.low w111.t w111.y w111.r w111.cap) (P33.root 2) :=
  Night6836Tree.sound w111 pick111 2 t5461 _ k111_2_2
theorem cov111_3 : PA.Covered 3 (OZ.Valid 3 w111.low w111.t w111.y w111.r w111.cap) (P33.root 3) :=
  Night6836Tree.sound w111 pick111 3 t564 _ (by decide +kernel)
theorem cov111_4 : PA.Covered 4 (OZ.Valid 4 w111.low w111.t w111.y w111.r w111.cap) (P33.root 4) :=
  Night6836Tree.sound w111 pick111 4 t565 _ (by decide +kernel)
theorem cov111_5 : PA.Covered 5 (OZ.Valid 5 w111.low w111.t w111.y w111.r w111.cap) (P33.root 5) :=
  Night6836Tree.sound w111 pick111 5 t566 _ (by decide +kernel)
theorem cov111_6 : PA.Covered 6 (OZ.Valid 6 w111.low w111.t w111.y w111.r w111.cap) (P33.root 6) :=
  Night6836Tree.sound w111 pick111 6 t567 _ (by decide +kernel)
theorem cov111_7 : PA.Covered 7 (OZ.Valid 7 w111.low w111.t w111.y w111.r w111.cap) (P33.root 7) :=
  Night6836Tree.sound w111 pick111 7 t568 _ (by decide +kernel)
theorem window111 : P33.WindowCount w111 := by
  apply P33.window_count w111 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov111_1
  · exact cov111_2
  · exact cov111_3
  · exact cov111_4
  · exact cov111_5
  · exact cov111_6
  · exact cov111_7
def w112 : P33.Window := ⟨11,26,7450,7409,234763309985020763,14531,18000,5000000,81920000000⟩
def h112_0 : Height w112 := ⟨14531,18000,by decide +kernel⟩
def h112_1 : Height w112 := ⟨19852,15000,by decide +kernel⟩
def h112_2 : Height w112 := ⟨30128,12000,by decide +kernel⟩
def pick112 (cl : ℕ) : Height w112 := if cl<32 then (h112_0) else (if cl<615 then (h112_1) else (h112_2))
private theorem k112_1_0 : check w112 pick112 1 t5418 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k112_1_1 : check w112 pick112 1 t5421 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k112_1_2 : check w112 pick112 1 t5422 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w112 pick112 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5418 t5421 k112_1_0 k112_1_1
private theorem k112_1_3 : check w112 pick112 1 t5426 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k112_1_4 : check w112 pick112 1 t5435 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k112_1_5 : check w112 pick112 1 t5436 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w112 pick112 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t5426 t5435 k112_1_3 k112_1_4
private theorem k112_1_6 : check w112 pick112 1 t5437 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w112 pick112 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5422 t5436 k112_1_2 k112_1_5
private theorem k112_1_7 : check w112 pick112 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k112_1_8 : check w112 pick112 1 t5455 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k112_1_9 : check w112 pick112 1 t5456 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w112 pick112 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t5455 k112_1_7 k112_1_8
private theorem k112_1_10 : check w112 pick112 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k112_1_11 : check w112 pick112 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k112_1_12 : check w112 pick112 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w112 pick112 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k112_1_10 k112_1_11
private theorem k112_1_13 : check w112 pick112 1 t5457 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w112 pick112 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5456 t2855 k112_1_9 k112_1_12
private theorem k112_1_14 : check w112 pick112 1 t5458 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w112 pick112 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5437 t5457 k112_1_6 k112_1_13
theorem cov112_1 : PA.Covered 1 (OZ.Valid 1 w112.low w112.t w112.y w112.r w112.cap) (P33.root 1) :=
  Night6836Tree.sound w112 pick112 1 t5458 _ k112_1_14
private theorem k112_2_0 : check w112 pick112 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k112_2_1 : check w112 pick112 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k112_2_2 : check w112 pick112 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w112 pick112 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k112_2_0 k112_2_1
theorem cov112_2 : PA.Covered 2 (OZ.Valid 2 w112.low w112.t w112.y w112.r w112.cap) (P33.root 2) :=
  Night6836Tree.sound w112 pick112 2 t5461 _ k112_2_2
theorem cov112_3 : PA.Covered 3 (OZ.Valid 3 w112.low w112.t w112.y w112.r w112.cap) (P33.root 3) :=
  Night6836Tree.sound w112 pick112 3 t564 _ (by decide +kernel)
theorem cov112_4 : PA.Covered 4 (OZ.Valid 4 w112.low w112.t w112.y w112.r w112.cap) (P33.root 4) :=
  Night6836Tree.sound w112 pick112 4 t565 _ (by decide +kernel)
theorem cov112_5 : PA.Covered 5 (OZ.Valid 5 w112.low w112.t w112.y w112.r w112.cap) (P33.root 5) :=
  Night6836Tree.sound w112 pick112 5 t566 _ (by decide +kernel)
theorem cov112_6 : PA.Covered 6 (OZ.Valid 6 w112.low w112.t w112.y w112.r w112.cap) (P33.root 6) :=
  Night6836Tree.sound w112 pick112 6 t567 _ (by decide +kernel)
theorem cov112_7 : PA.Covered 7 (OZ.Valid 7 w112.low w112.t w112.y w112.r w112.cap) (P33.root 7) :=
  Night6836Tree.sound w112 pick112 7 t568 _ (by decide +kernel)
theorem window112 : P33.WindowCount w112 := by
  apply P33.window_count w112 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov112_1
  · exact cov112_2
  · exact cov112_3
  · exact cov112_4
  · exact cov112_5
  · exact cov112_6
  · exact cov112_7
def w113 : P33.Window := ⟨11,27,7408,7233,239333075545528601,12790,21000,5000000,81920000000⟩
def h113_0 : Height w113 := ⟨12790,21000,by decide +kernel⟩
def h113_1 : Height w113 := ⟨16714,18000,by decide +kernel⟩
def h113_2 : Height w113 := ⟨22591,15000,by decide +kernel⟩
def h113_3 : Height w113 := ⟨34368,12000,by decide +kernel⟩
def pick113 (cl : ℕ) : Height w113 := if cl<36 then (if cl<2 then (h113_0) else (h113_1)) else (if cl<922 then (h113_2) else (h113_3))
private theorem k113_1_0 : check w113 pick113 1 t5418 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k113_1_1 : check w113 pick113 1 t5421 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k113_1_2 : check w113 pick113 1 t5422 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w113 pick113 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5418 t5421 k113_1_0 k113_1_1
private theorem k113_1_3 : check w113 pick113 1 t5426 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k113_1_4 : check w113 pick113 1 t5472 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k113_1_5 : check w113 pick113 1 t5473 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w113 pick113 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t5426 t5472 k113_1_3 k113_1_4
private theorem k113_1_6 : check w113 pick113 1 t5474 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w113 pick113 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5422 t5473 k113_1_2 k113_1_5
private theorem k113_1_7 : check w113 pick113 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k113_1_8 : check w113 pick113 1 t5455 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k113_1_9 : check w113 pick113 1 t5456 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w113 pick113 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t5455 k113_1_7 k113_1_8
private theorem k113_1_10 : check w113 pick113 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k113_1_11 : check w113 pick113 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k113_1_12 : check w113 pick113 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w113 pick113 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k113_1_10 k113_1_11
private theorem k113_1_13 : check w113 pick113 1 t5457 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w113 pick113 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5456 t2855 k113_1_9 k113_1_12
private theorem k113_1_14 : check w113 pick113 1 t5475 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w113 pick113 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5474 t5457 k113_1_6 k113_1_13
theorem cov113_1 : PA.Covered 1 (OZ.Valid 1 w113.low w113.t w113.y w113.r w113.cap) (P33.root 1) :=
  Night6836Tree.sound w113 pick113 1 t5475 _ k113_1_14
private theorem k113_2_0 : check w113 pick113 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k113_2_1 : check w113 pick113 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k113_2_2 : check w113 pick113 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w113 pick113 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k113_2_0 k113_2_1
theorem cov113_2 : PA.Covered 2 (OZ.Valid 2 w113.low w113.t w113.y w113.r w113.cap) (P33.root 2) :=
  Night6836Tree.sound w113 pick113 2 t5461 _ k113_2_2
theorem cov113_3 : PA.Covered 3 (OZ.Valid 3 w113.low w113.t w113.y w113.r w113.cap) (P33.root 3) :=
  Night6836Tree.sound w113 pick113 3 t564 _ (by decide +kernel)
theorem cov113_4 : PA.Covered 4 (OZ.Valid 4 w113.low w113.t w113.y w113.r w113.cap) (P33.root 4) :=
  Night6836Tree.sound w113 pick113 4 t565 _ (by decide +kernel)
theorem cov113_5 : PA.Covered 5 (OZ.Valid 5 w113.low w113.t w113.y w113.r w113.cap) (P33.root 5) :=
  Night6836Tree.sound w113 pick113 5 t566 _ (by decide +kernel)
theorem cov113_6 : PA.Covered 6 (OZ.Valid 6 w113.low w113.t w113.y w113.r w113.cap) (P33.root 6) :=
  Night6836Tree.sound w113 pick113 6 t567 _ (by decide +kernel)
theorem cov113_7 : PA.Covered 7 (OZ.Valid 7 w113.low w113.t w113.y w113.r w113.cap) (P33.root 7) :=
  Night6836Tree.sound w113 pick113 7 t568 _ (by decide +kernel)
theorem window113 : P33.WindowCount w113 := by
  apply P33.window_count w113 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov113_1
  · exact cov113_2
  · exact cov113_3
  · exact cov113_4
  · exact cov113_5
  · exact cov113_6
  · exact cov113_7
def w114 : P33.Window := ⟨11,28,7367,7326,243868357158330522,13392,21000,5000000,81920000000⟩
def h114_0 : Height w114 := ⟨13392,21000,by decide +kernel⟩
def h114_1 : Height w114 := ⟨17323,18000,by decide +kernel⟩
def h114_2 : Height w114 := ⟨23190,15000,by decide +kernel⟩
def h114_3 : Height w114 := ⟨34817,12000,by decide +kernel⟩
def pick114 (cl : ℕ) : Height w114 := if cl<36 then (if cl<2 then (h114_0) else (h114_1)) else (if cl<922 then (h114_2) else (h114_3))
private theorem k114_1_0 : check w114 pick114 1 t5418 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k114_1_1 : check w114 pick114 1 t5421 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k114_1_2 : check w114 pick114 1 t5422 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w114 pick114 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5418 t5421 k114_1_0 k114_1_1
private theorem k114_1_3 : check w114 pick114 1 t5426 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k114_1_4 : check w114 pick114 1 t5472 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k114_1_5 : check w114 pick114 1 t5473 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w114 pick114 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t5426 t5472 k114_1_3 k114_1_4
private theorem k114_1_6 : check w114 pick114 1 t5474 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w114 pick114 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5422 t5473 k114_1_2 k114_1_5
private theorem k114_1_7 : check w114 pick114 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k114_1_8 : check w114 pick114 1 t5455 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k114_1_9 : check w114 pick114 1 t5456 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w114 pick114 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t5455 k114_1_7 k114_1_8
private theorem k114_1_10 : check w114 pick114 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k114_1_11 : check w114 pick114 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k114_1_12 : check w114 pick114 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w114 pick114 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k114_1_10 k114_1_11
private theorem k114_1_13 : check w114 pick114 1 t5457 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w114 pick114 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5456 t2855 k114_1_9 k114_1_12
private theorem k114_1_14 : check w114 pick114 1 t5475 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w114 pick114 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5474 t5457 k114_1_6 k114_1_13
theorem cov114_1 : PA.Covered 1 (OZ.Valid 1 w114.low w114.t w114.y w114.r w114.cap) (P33.root 1) :=
  Night6836Tree.sound w114 pick114 1 t5475 _ k114_1_14
private theorem k114_2_0 : check w114 pick114 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k114_2_1 : check w114 pick114 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k114_2_2 : check w114 pick114 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w114 pick114 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k114_2_0 k114_2_1
theorem cov114_2 : PA.Covered 2 (OZ.Valid 2 w114.low w114.t w114.y w114.r w114.cap) (P33.root 2) :=
  Night6836Tree.sound w114 pick114 2 t5461 _ k114_2_2
theorem cov114_3 : PA.Covered 3 (OZ.Valid 3 w114.low w114.t w114.y w114.r w114.cap) (P33.root 3) :=
  Night6836Tree.sound w114 pick114 3 t564 _ (by decide +kernel)
theorem cov114_4 : PA.Covered 4 (OZ.Valid 4 w114.low w114.t w114.y w114.r w114.cap) (P33.root 4) :=
  Night6836Tree.sound w114 pick114 4 t565 _ (by decide +kernel)
theorem cov114_5 : PA.Covered 5 (OZ.Valid 5 w114.low w114.t w114.y w114.r w114.cap) (P33.root 5) :=
  Night6836Tree.sound w114 pick114 5 t566 _ (by decide +kernel)
theorem cov114_6 : PA.Covered 6 (OZ.Valid 6 w114.low w114.t w114.y w114.r w114.cap) (P33.root 6) :=
  Night6836Tree.sound w114 pick114 6 t567 _ (by decide +kernel)
theorem cov114_7 : PA.Covered 7 (OZ.Valid 7 w114.low w114.t w114.y w114.r w114.cap) (P33.root 7) :=
  Night6836Tree.sound w114 pick114 7 t568 _ (by decide +kernel)
theorem window114 : P33.WindowCount w114 := by
  apply P33.window_count w114 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov114_1
  · exact cov114_2
  · exact cov114_3
  · exact cov114_4
  · exact cov114_5
  · exact cov114_6
  · exact cov114_7
def w115 : P33.Window := ⟨11,29,7325,7283,242582650085619162,14682,21000,5000000,81920000000⟩
def h115_0 : Height w115 := ⟨14682,21000,by decide +kernel⟩
def h115_1 : Height w115 := ⟨18770,18000,by decide +kernel⟩
def h115_2 : Height w115 := ⟨24929,15000,by decide +kernel⟩
def h115_3 : Height w115 := ⟨37289,12000,by decide +kernel⟩
def pick115 (cl : ℕ) : Height w115 := if cl<43 then (if cl<2 then (h115_0) else (h115_1)) else (if cl<926 then (h115_2) else (h115_3))
private theorem k115_1_0 : check w115 pick115 1 t5482 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k115_1_1 : check w115 pick115 1 t5492 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k115_1_2 : check w115 pick115 1 t5493 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w115 pick115 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5482 t5492 k115_1_0 k115_1_1
private theorem k115_1_3 : check w115 pick115 1 t5495 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k115_1_4 : check w115 pick115 1 t5435 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k115_1_5 : check w115 pick115 1 t5496 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w115 pick115 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t5495 t5435 k115_1_3 k115_1_4
private theorem k115_1_6 : check w115 pick115 1 t5497 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w115 pick115 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5493 t5496 k115_1_2 k115_1_5
private theorem k115_1_7 : check w115 pick115 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k115_1_8 : check w115 pick115 1 t5455 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k115_1_9 : check w115 pick115 1 t5456 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w115 pick115 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t5455 k115_1_7 k115_1_8
private theorem k115_1_10 : check w115 pick115 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k115_1_11 : check w115 pick115 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k115_1_12 : check w115 pick115 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w115 pick115 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k115_1_10 k115_1_11
private theorem k115_1_13 : check w115 pick115 1 t5457 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w115 pick115 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5456 t2855 k115_1_9 k115_1_12
private theorem k115_1_14 : check w115 pick115 1 t5498 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w115 pick115 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5497 t5457 k115_1_6 k115_1_13
theorem cov115_1 : PA.Covered 1 (OZ.Valid 1 w115.low w115.t w115.y w115.r w115.cap) (P33.root 1) :=
  Night6836Tree.sound w115 pick115 1 t5498 _ k115_1_14
private theorem k115_2_0 : check w115 pick115 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k115_2_1 : check w115 pick115 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k115_2_2 : check w115 pick115 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w115 pick115 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k115_2_0 k115_2_1
theorem cov115_2 : PA.Covered 2 (OZ.Valid 2 w115.low w115.t w115.y w115.r w115.cap) (P33.root 2) :=
  Night6836Tree.sound w115 pick115 2 t5461 _ k115_2_2
theorem cov115_3 : PA.Covered 3 (OZ.Valid 3 w115.low w115.t w115.y w115.r w115.cap) (P33.root 3) :=
  Night6836Tree.sound w115 pick115 3 t564 _ (by decide +kernel)
theorem cov115_4 : PA.Covered 4 (OZ.Valid 4 w115.low w115.t w115.y w115.r w115.cap) (P33.root 4) :=
  Night6836Tree.sound w115 pick115 4 t565 _ (by decide +kernel)
theorem cov115_5 : PA.Covered 5 (OZ.Valid 5 w115.low w115.t w115.y w115.r w115.cap) (P33.root 5) :=
  Night6836Tree.sound w115 pick115 5 t566 _ (by decide +kernel)
theorem cov115_6 : PA.Covered 6 (OZ.Valid 6 w115.low w115.t w115.y w115.r w115.cap) (P33.root 6) :=
  Night6836Tree.sound w115 pick115 6 t567 _ (by decide +kernel)
theorem cov115_7 : PA.Covered 7 (OZ.Valid 7 w115.low w115.t w115.y w115.r w115.cap) (P33.root 7) :=
  Night6836Tree.sound w115 pick115 7 t568 _ (by decide +kernel)
theorem window115 : P33.WindowCount w115 := by
  apply P33.window_count w115 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov115_1
  · exact cov115_2
  · exact cov115_3
  · exact cov115_4
  · exact cov115_5
  · exact cov115_6
  · exact cov115_7
def w116 : P33.Window := ⟨11,30,7232,6283,244172265364484971,18672,24000,5000000,81920000000⟩
def h116_0 : Height w116 := ⟨18672,24000,by decide +kernel⟩
def h116_1 : Height w116 := ⟨22897,21000,by decide +kernel⟩
def h116_2 : Height w116 := ⟨28878,18000,by decide +kernel⟩
def h116_3 : Height w116 := ⟨39108,15000,by decide +kernel⟩
def pick116 (cl : ℕ) : Height w116 := if cl<37 then (if cl<4 then (h116_0) else (h116_1)) else (if cl<600 then (h116_2) else (h116_3))
private theorem k116_1_0 : check w116 pick116 1 t5482 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k116_1_1 : check w116 pick116 1 t5492 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k116_1_2 : check w116 pick116 1 t5493 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w116 pick116 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5482 t5492 k116_1_0 k116_1_1
private theorem k116_1_3 : check w116 pick116 1 t5495 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k116_1_4 : check w116 pick116 1 t5435 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k116_1_5 : check w116 pick116 1 t5496 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w116 pick116 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t5495 t5435 k116_1_3 k116_1_4
private theorem k116_1_6 : check w116 pick116 1 t5497 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w116 pick116 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5493 t5496 k116_1_2 k116_1_5
private theorem k116_1_7 : check w116 pick116 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k116_1_8 : check w116 pick116 1 t5455 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k116_1_9 : check w116 pick116 1 t5456 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w116 pick116 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t5455 k116_1_7 k116_1_8
private theorem k116_1_10 : check w116 pick116 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k116_1_11 : check w116 pick116 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k116_1_12 : check w116 pick116 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w116 pick116 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k116_1_10 k116_1_11
private theorem k116_1_13 : check w116 pick116 1 t5457 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w116 pick116 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5456 t2855 k116_1_9 k116_1_12
private theorem k116_1_14 : check w116 pick116 1 t5498 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w116 pick116 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5497 t5457 k116_1_6 k116_1_13
theorem cov116_1 : PA.Covered 1 (OZ.Valid 1 w116.low w116.t w116.y w116.r w116.cap) (P33.root 1) :=
  Night6836Tree.sound w116 pick116 1 t5498 _ k116_1_14
private theorem k116_2_0 : check w116 pick116 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k116_2_1 : check w116 pick116 2 t3115 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k116_2_2 : check w116 pick116 2 t5499 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w116 pick116 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3115 k116_2_0 k116_2_1
theorem cov116_2 : PA.Covered 2 (OZ.Valid 2 w116.low w116.t w116.y w116.r w116.cap) (P33.root 2) :=
  Night6836Tree.sound w116 pick116 2 t5499 _ k116_2_2
theorem cov116_3 : PA.Covered 3 (OZ.Valid 3 w116.low w116.t w116.y w116.r w116.cap) (P33.root 3) :=
  Night6836Tree.sound w116 pick116 3 t564 _ (by decide +kernel)
theorem cov116_4 : PA.Covered 4 (OZ.Valid 4 w116.low w116.t w116.y w116.r w116.cap) (P33.root 4) :=
  Night6836Tree.sound w116 pick116 4 t565 _ (by decide +kernel)
theorem cov116_5 : PA.Covered 5 (OZ.Valid 5 w116.low w116.t w116.y w116.r w116.cap) (P33.root 5) :=
  Night6836Tree.sound w116 pick116 5 t566 _ (by decide +kernel)
theorem cov116_6 : PA.Covered 6 (OZ.Valid 6 w116.low w116.t w116.y w116.r w116.cap) (P33.root 6) :=
  Night6836Tree.sound w116 pick116 6 t567 _ (by decide +kernel)
theorem cov116_7 : PA.Covered 7 (OZ.Valid 7 w116.low w116.t w116.y w116.r w116.cap) (P33.root 7) :=
  Night6836Tree.sound w116 pick116 7 t568 _ (by decide +kernel)
theorem window116 : P33.WindowCount w116 := by
  apply P33.window_count w116 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov116_1
  · exact cov116_2
  · exact cov116_3
  · exact cov116_4
  · exact cov116_5
  · exact cov116_6
  · exact cov116_7
def w117 : P33.Window := ⟨11,30,7282,7240,245283960553341730,15996,21000,5000000,81920000000⟩
def h117_0 : Height w117 := ⟨15996,21000,by decide +kernel⟩
def h117_1 : Height w117 := ⟨20246,18000,by decide +kernel⟩
def h117_2 : Height w117 := ⟨26709,15000,by decide +kernel⟩
def h117_3 : Height w117 := ⟨39838,12000,by decide +kernel⟩
def pick117 (cl : ℕ) : Height w117 := if cl<55 then (if cl<4 then (h117_0) else (h117_1)) else (if cl<961 then (h117_2) else (h117_3))
private theorem k117_1_0 : check w117 pick117 1 t5482 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k117_1_1 : check w117 pick117 1 t5492 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k117_1_2 : check w117 pick117 1 t5493 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w117 pick117 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5482 t5492 k117_1_0 k117_1_1
private theorem k117_1_3 : check w117 pick117 1 t5495 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k117_1_4 : check w117 pick117 1 t5435 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k117_1_5 : check w117 pick117 1 t5496 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w117 pick117 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t5495 t5435 k117_1_3 k117_1_4
private theorem k117_1_6 : check w117 pick117 1 t5497 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w117 pick117 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5493 t5496 k117_1_2 k117_1_5
private theorem k117_1_7 : check w117 pick117 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k117_1_8 : check w117 pick117 1 t5455 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k117_1_9 : check w117 pick117 1 t5456 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w117 pick117 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t5455 k117_1_7 k117_1_8
private theorem k117_1_10 : check w117 pick117 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k117_1_11 : check w117 pick117 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k117_1_12 : check w117 pick117 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w117 pick117 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k117_1_10 k117_1_11
private theorem k117_1_13 : check w117 pick117 1 t5457 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w117 pick117 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5456 t2855 k117_1_9 k117_1_12
private theorem k117_1_14 : check w117 pick117 1 t5498 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w117 pick117 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5497 t5457 k117_1_6 k117_1_13
theorem cov117_1 : PA.Covered 1 (OZ.Valid 1 w117.low w117.t w117.y w117.r w117.cap) (P33.root 1) :=
  Night6836Tree.sound w117 pick117 1 t5498 _ k117_1_14
private theorem k117_2_0 : check w117 pick117 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k117_2_1 : check w117 pick117 2 t3115 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k117_2_2 : check w117 pick117 2 t5499 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w117 pick117 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3115 k117_2_0 k117_2_1
theorem cov117_2 : PA.Covered 2 (OZ.Valid 2 w117.low w117.t w117.y w117.r w117.cap) (P33.root 2) :=
  Night6836Tree.sound w117 pick117 2 t5499 _ k117_2_2
theorem cov117_3 : PA.Covered 3 (OZ.Valid 3 w117.low w117.t w117.y w117.r w117.cap) (P33.root 3) :=
  Night6836Tree.sound w117 pick117 3 t564 _ (by decide +kernel)
theorem cov117_4 : PA.Covered 4 (OZ.Valid 4 w117.low w117.t w117.y w117.r w117.cap) (P33.root 4) :=
  Night6836Tree.sound w117 pick117 4 t565 _ (by decide +kernel)
theorem cov117_5 : PA.Covered 5 (OZ.Valid 5 w117.low w117.t w117.y w117.r w117.cap) (P33.root 5) :=
  Night6836Tree.sound w117 pick117 5 t566 _ (by decide +kernel)
theorem cov117_6 : PA.Covered 6 (OZ.Valid 6 w117.low w117.t w117.y w117.r w117.cap) (P33.root 6) :=
  Night6836Tree.sound w117 pick117 6 t567 _ (by decide +kernel)
theorem cov117_7 : PA.Covered 7 (OZ.Valid 7 w117.low w117.t w117.y w117.r w117.cap) (P33.root 7) :=
  Night6836Tree.sound w117 pick117 7 t568 _ (by decide +kernel)
theorem window117 : P33.WindowCount w117 := by
  apply P33.window_count w117 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov117_1
  · exact cov117_2
  · exact cov117_3
  · exact cov117_4
  · exact cov117_5
  · exact cov117_6
  · exact cov117_7
def w118 : P33.Window := ⟨11,31,7239,7051,245315141538842061,18250,21000,5000000,81920000000⟩
def h118_0 : Height w118 := ⟨18250,21000,by decide +kernel⟩
def h118_1 : Height w118 := ⟨22872,18000,by decide +kernel⟩
def h118_2 : Height w118 := ⟨30077,15000,by decide +kernel⟩
def h118_3 : Height w118 := ⟨45288,12000,by decide +kernel⟩
def pick118 (cl : ℕ) : Height w118 := if cl<104 then (if cl<6 then (h118_0) else (h118_1)) else (if cl<1007 then (h118_2) else (h118_3))
private theorem k118_1_0 : check w118 pick118 1 t5501 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k118_1_1 : check w118 pick118 1 t5492 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k118_1_2 : check w118 pick118 1 t5502 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w118 pick118 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5501 t5492 k118_1_0 k118_1_1
private theorem k118_1_3 : check w118 pick118 1 t5495 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k118_1_4 : check w118 pick118 1 t5435 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k118_1_5 : check w118 pick118 1 t5496 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w118 pick118 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t5495 t5435 k118_1_3 k118_1_4
private theorem k118_1_6 : check w118 pick118 1 t5503 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w118 pick118 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5502 t5496 k118_1_2 k118_1_5
private theorem k118_1_7 : check w118 pick118 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k118_1_8 : check w118 pick118 1 t5455 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k118_1_9 : check w118 pick118 1 t5456 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w118 pick118 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t5455 k118_1_7 k118_1_8
private theorem k118_1_10 : check w118 pick118 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k118_1_11 : check w118 pick118 1 t5505 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k118_1_12 : check w118 pick118 1 t5506 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w118 pick118 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t5505 k118_1_10 k118_1_11
private theorem k118_1_13 : check w118 pick118 1 t5507 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w118 pick118 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5456 t5506 k118_1_9 k118_1_12
private theorem k118_1_14 : check w118 pick118 1 t5508 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w118 pick118 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5503 t5507 k118_1_6 k118_1_13
theorem cov118_1 : PA.Covered 1 (OZ.Valid 1 w118.low w118.t w118.y w118.r w118.cap) (P33.root 1) :=
  Night6836Tree.sound w118 pick118 1 t5508 _ k118_1_14
private theorem k118_2_0 : check w118 pick118 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k118_2_1 : check w118 pick118 2 t5524 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k118_2_2 : check w118 pick118 2 t5525 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w118 pick118 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t5524 k118_2_0 k118_2_1
theorem cov118_2 : PA.Covered 2 (OZ.Valid 2 w118.low w118.t w118.y w118.r w118.cap) (P33.root 2) :=
  Night6836Tree.sound w118 pick118 2 t5525 _ k118_2_2
theorem cov118_3 : PA.Covered 3 (OZ.Valid 3 w118.low w118.t w118.y w118.r w118.cap) (P33.root 3) :=
  Night6836Tree.sound w118 pick118 3 t564 _ (by decide +kernel)
theorem cov118_4 : PA.Covered 4 (OZ.Valid 4 w118.low w118.t w118.y w118.r w118.cap) (P33.root 4) :=
  Night6836Tree.sound w118 pick118 4 t565 _ (by decide +kernel)
theorem cov118_5 : PA.Covered 5 (OZ.Valid 5 w118.low w118.t w118.y w118.r w118.cap) (P33.root 5) :=
  Night6836Tree.sound w118 pick118 5 t566 _ (by decide +kernel)
theorem cov118_6 : PA.Covered 6 (OZ.Valid 6 w118.low w118.t w118.y w118.r w118.cap) (P33.root 6) :=
  Night6836Tree.sound w118 pick118 6 t567 _ (by decide +kernel)
theorem cov118_7 : PA.Covered 7 (OZ.Valid 7 w118.low w118.t w118.y w118.r w118.cap) (P33.root 7) :=
  Night6836Tree.sound w118 pick118 7 t568 _ (by decide +kernel)
theorem window118 : P33.WindowCount w118 := by
  apply P33.window_count w118 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov118_1
  · exact cov118_2
  · exact cov118_3
  · exact cov118_4
  · exact cov118_5
  · exact cov118_6
  · exact cov118_7
def w119 : P33.Window := ⟨11,32,5431,4432,200186312277989498,28775,35000,5000000,81920000000⟩
def h119_0 : Height w119 := ⟨28775,35000,by decide +kernel⟩
def h119_1 : Height w119 := ⟨34275,31000,by decide +kernel⟩
def h119_2 : Height w119 := ⟨41677,27000,by decide +kernel⟩
def h119_3 : Height w119 := ⟨53099,23000,by decide +kernel⟩
def h119_4 : Height w119 := ⟨75616,19000,by decide +kernel⟩
def pick119 (cl : ℕ) : Height w119 := if cl<32 then (if cl<3 then (h119_0) else (h119_1)) else (if cl<257 then (h119_2) else (if cl<1021 then (h119_3) else (h119_4)))
private theorem k119_1_0 : check w119 pick119 1 t5418 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k119_1_1 : check w119 pick119 1 t5421 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k119_1_2 : check w119 pick119 1 t5422 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w119 pick119 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5418 t5421 k119_1_0 k119_1_1
private theorem k119_1_3 : check w119 pick119 1 t5495 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k119_1_4 : check w119 pick119 1 t5435 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k119_1_5 : check w119 pick119 1 t5496 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w119 pick119 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t5495 t5435 k119_1_3 k119_1_4
private theorem k119_1_6 : check w119 pick119 1 t5526 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w119 pick119 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5422 t5496 k119_1_2 k119_1_5
private theorem k119_1_7 : check w119 pick119 1 t5441 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k119_1_8 : check w119 pick119 1 t5455 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k119_1_9 : check w119 pick119 1 t5456 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w119 pick119 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t5441 t5455 k119_1_7 k119_1_8
private theorem k119_1_10 : check w119 pick119 1 t2854 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k119_1_11 : check w119 pick119 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k119_1_12 : check w119 pick119 1 t2855 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w119 pick119 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2854 t498 k119_1_10 k119_1_11
private theorem k119_1_13 : check w119 pick119 1 t5457 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w119 pick119 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5456 t2855 k119_1_9 k119_1_12
private theorem k119_1_14 : check w119 pick119 1 t5527 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w119 pick119 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5526 t5457 k119_1_6 k119_1_13
theorem cov119_1 : PA.Covered 1 (OZ.Valid 1 w119.low w119.t w119.y w119.r w119.cap) (P33.root 1) :=
  Night6836Tree.sound w119 pick119 1 t5527 _ k119_1_14
private theorem k119_2_0 : check w119 pick119 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k119_2_1 : check w119 pick119 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k119_2_2 : check w119 pick119 2 t5528 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w119 pick119 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t3303 k119_2_0 k119_2_1
theorem cov119_2 : PA.Covered 2 (OZ.Valid 2 w119.low w119.t w119.y w119.r w119.cap) (P33.root 2) :=
  Night6836Tree.sound w119 pick119 2 t5528 _ k119_2_2
theorem cov119_3 : PA.Covered 3 (OZ.Valid 3 w119.low w119.t w119.y w119.r w119.cap) (P33.root 3) :=
  Night6836Tree.sound w119 pick119 3 t564 _ (by decide +kernel)
theorem cov119_4 : PA.Covered 4 (OZ.Valid 4 w119.low w119.t w119.y w119.r w119.cap) (P33.root 4) :=
  Night6836Tree.sound w119 pick119 4 t565 _ (by decide +kernel)
theorem cov119_5 : PA.Covered 5 (OZ.Valid 5 w119.low w119.t w119.y w119.r w119.cap) (P33.root 5) :=
  Night6836Tree.sound w119 pick119 5 t566 _ (by decide +kernel)
theorem cov119_6 : PA.Covered 6 (OZ.Valid 6 w119.low w119.t w119.y w119.r w119.cap) (P33.root 6) :=
  Night6836Tree.sound w119 pick119 6 t567 _ (by decide +kernel)
theorem cov119_7 : PA.Covered 7 (OZ.Valid 7 w119.low w119.t w119.y w119.r w119.cap) (P33.root 7) :=
  Night6836Tree.sound w119 pick119 7 t2134 _ (by decide +kernel)
theorem window119 : P33.WindowCount w119 := by
  apply P33.window_count w119 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov119_1
  · exact cov119_2
  · exact cov119_3
  · exact cov119_4
  · exact cov119_5
  · exact cov119_6
  · exact cov119_7
end ProximityPrize.SubmissionLower.Night6836Bank
