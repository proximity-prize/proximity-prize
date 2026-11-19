/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT02
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w240 : P33.Window := ⟨13,39,5789,5187,246386880367974336,30009,36000,5000000,81920000000⟩
def h240_0 : Height w240 := ⟨30009,36000,by decide +kernel⟩
def h240_1 : Height w240 := ⟨33938,33000,by decide +kernel⟩
def h240_2 : Height w240 := ⟨38695,30000,by decide +kernel⟩
def h240_3 : Height w240 := ⟨44789,27000,by decide +kernel⟩
def h240_4 : Height w240 := ⟨53250,24000,by decide +kernel⟩
def h240_5 : Height w240 := ⟨66532,21000,by decide +kernel⟩
def pick240 (cl : ℕ) : Height w240 := if cl<41 then (if cl<2 then (h240_0) else (if cl<10 then (h240_1) else (h240_2))) else (if cl<236 then (h240_3) else (if cl<961 then (h240_4) else (h240_5)))
private theorem k240_1_0 : check w240 pick240 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k240_1_1 : check w240 pick240 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k240_1_2 : check w240 pick240 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w240 pick240 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k240_1_0 k240_1_1
private theorem k240_1_3 : check w240 pick240 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k240_1_4 : check w240 pick240 1 t8081 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k240_1_5 : check w240 pick240 1 t8082 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w240 pick240 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t8081 k240_1_3 k240_1_4
private theorem k240_1_6 : check w240 pick240 1 t8083 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w240 pick240 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t8082 k240_1_2 k240_1_5
private theorem k240_1_7 : check w240 pick240 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k240_1_8 : check w240 pick240 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k240_1_9 : check w240 pick240 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w240 pick240 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k240_1_7 k240_1_8
private theorem k240_1_10 : check w240 pick240 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k240_1_11 : check w240 pick240 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k240_1_12 : check w240 pick240 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w240 pick240 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k240_1_10 k240_1_11
private theorem k240_1_13 : check w240 pick240 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w240 pick240 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k240_1_9 k240_1_12
private theorem k240_1_14 : check w240 pick240 1 t8096 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w240 pick240 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8083 t7649 k240_1_6 k240_1_13
theorem cov240_1 : PA.Covered 1 (OZ.Valid 1 w240.low w240.t w240.y w240.r w240.cap) (P33.root 1) :=
  Night6836Tree.sound w240 pick240 1 t8096 _ k240_1_14
private theorem k240_2_0 : check w240 pick240 2 t5616 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k240_2_1 : check w240 pick240 2 t7677 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k240_2_2 : check w240 pick240 2 t7678 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w240 pick240 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t5616 t7677 k240_2_0 k240_2_1
private theorem k240_2_3 : check w240 pick240 2 t8632 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k240_2_4 : check w240 pick240 2 t8633 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w240 pick240 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t7678 t8632 k240_2_2 k240_2_3
theorem cov240_2 : PA.Covered 2 (OZ.Valid 2 w240.low w240.t w240.y w240.r w240.cap) (P33.root 2) :=
  Night6836Tree.sound w240 pick240 2 t8633 _ k240_2_4
theorem cov240_3 : PA.Covered 3 (OZ.Valid 3 w240.low w240.t w240.y w240.r w240.cap) (P33.root 3) :=
  Night6836Tree.sound w240 pick240 3 t564 _ (by decide +kernel)
theorem cov240_4 : PA.Covered 4 (OZ.Valid 4 w240.low w240.t w240.y w240.r w240.cap) (P33.root 4) :=
  Night6836Tree.sound w240 pick240 4 t565 _ (by decide +kernel)
theorem cov240_5 : PA.Covered 5 (OZ.Valid 5 w240.low w240.t w240.y w240.r w240.cap) (P33.root 5) :=
  Night6836Tree.sound w240 pick240 5 t566 _ (by decide +kernel)
theorem cov240_6 : PA.Covered 6 (OZ.Valid 6 w240.low w240.t w240.y w240.r w240.cap) (P33.root 6) :=
  Night6836Tree.sound w240 pick240 6 t567 _ (by decide +kernel)
theorem cov240_7 : PA.Covered 7 (OZ.Valid 7 w240.low w240.t w240.y w240.r w240.cap) (P33.root 7) :=
  Night6836Tree.sound w240 pick240 7 t2134 _ (by decide +kernel)
theorem window240 : P33.WindowCount w240 := by
  apply P33.window_count w240 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov240_1
  · exact cov240_2
  · exact cov240_3
  · exact cov240_4
  · exact cov240_5
  · exact cov240_6
  · exact cov240_7
def w241 : P33.Window := ⟨13,40,5571,5348,245698759031284664,33018,33000,5000000,81920000000⟩
def h241_0 : Height w241 := ⟨33018,33000,by decide +kernel⟩
def h241_1 : Height w241 := ⟨37556,30000,by decide +kernel⟩
def h241_2 : Height w241 := ⟨43309,27000,by decide +kernel⟩
def h241_3 : Height w241 := ⟨51187,24000,by decide +kernel⟩
def h241_4 : Height w241 := ⟨63303,21000,by decide +kernel⟩
def pick241 (cl : ℕ) : Height w241 := if cl<32 then (if cl<6 then (h241_0) else (h241_1)) else (if cl<164 then (h241_2) else (if cl<922 then (h241_3) else (h241_4)))
private theorem k241_1_0 : check w241 pick241 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k241_1_1 : check w241 pick241 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k241_1_2 : check w241 pick241 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w241 pick241 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k241_1_0 k241_1_1
private theorem k241_1_3 : check w241 pick241 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k241_1_4 : check w241 pick241 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k241_1_5 : check w241 pick241 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w241 pick241 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k241_1_3 k241_1_4
private theorem k241_1_6 : check w241 pick241 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w241 pick241 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k241_1_2 k241_1_5
private theorem k241_1_7 : check w241 pick241 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k241_1_8 : check w241 pick241 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k241_1_9 : check w241 pick241 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w241 pick241 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k241_1_7 k241_1_8
private theorem k241_1_10 : check w241 pick241 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k241_1_11 : check w241 pick241 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k241_1_12 : check w241 pick241 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w241 pick241 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k241_1_10 k241_1_11
private theorem k241_1_13 : check w241 pick241 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w241 pick241 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k241_1_9 k241_1_12
private theorem k241_1_14 : check w241 pick241 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w241 pick241 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k241_1_6 k241_1_13
theorem cov241_1 : PA.Covered 1 (OZ.Valid 1 w241.low w241.t w241.y w241.r w241.cap) (P33.root 1) :=
  Night6836Tree.sound w241 pick241 1 t7674 _ k241_1_14
private theorem k241_2_0 : check w241 pick241 2 t5566 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k241_2_1 : check w241 pick241 2 t5541 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k241_2_2 : check w241 pick241 2 t5567 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w241 pick241 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5566 t5541 k241_2_0 k241_2_1
theorem cov241_2 : PA.Covered 2 (OZ.Valid 2 w241.low w241.t w241.y w241.r w241.cap) (P33.root 2) :=
  Night6836Tree.sound w241 pick241 2 t5567 _ k241_2_2
theorem cov241_3 : PA.Covered 3 (OZ.Valid 3 w241.low w241.t w241.y w241.r w241.cap) (P33.root 3) :=
  Night6836Tree.sound w241 pick241 3 t564 _ (by decide +kernel)
theorem cov241_4 : PA.Covered 4 (OZ.Valid 4 w241.low w241.t w241.y w241.r w241.cap) (P33.root 4) :=
  Night6836Tree.sound w241 pick241 4 t565 _ (by decide +kernel)
theorem cov241_5 : PA.Covered 5 (OZ.Valid 5 w241.low w241.t w241.y w241.r w241.cap) (P33.root 5) :=
  Night6836Tree.sound w241 pick241 5 t566 _ (by decide +kernel)
theorem cov241_6 : PA.Covered 6 (OZ.Valid 6 w241.low w241.t w241.y w241.r w241.cap) (P33.root 6) :=
  Night6836Tree.sound w241 pick241 6 t567 _ (by decide +kernel)
theorem cov241_7 : PA.Covered 7 (OZ.Valid 7 w241.low w241.t w241.y w241.r w241.cap) (P33.root 7) :=
  Night6836Tree.sound w241 pick241 7 t2134 _ (by decide +kernel)
theorem window241 : P33.WindowCount w241 := by
  apply P33.window_count w241 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov241_1
  · exact cov241_2
  · exact cov241_3
  · exact cov241_4
  · exact cov241_5
  · exact cov241_6
  · exact cov241_7
def w242 : P33.Window := ⟨13,41,5186,4237,245632838613060578,43035,42000,5000000,81920000000⟩
def h242_0 : Height w242 := ⟨43035,42000,by decide +kernel⟩
def h242_1 : Height w242 := ⟨47467,39000,by decide +kernel⟩
def h242_2 : Height w242 := ⟨52740,36000,by decide +kernel⟩
def h242_3 : Height w242 := ⟨59277,33000,by decide +kernel⟩
def h242_4 : Height w242 := ⟨67839,30000,by decide +kernel⟩
def h242_5 : Height w242 := ⟨79943,27000,by decide +kernel⟩
def pick242 (cl : ℕ) : Height w242 := if cl<62 then (if cl<5 then (h242_0) else (if cl<32 then (h242_1) else (h242_2))) else (if cl<253 then (h242_3) else (if cl<922 then (h242_4) else (h242_5)))
private theorem k242_1_0 : check w242 pick242 1 t8634 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k242_1_1 : check w242 pick242 1 t8386 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k242_1_2 : check w242 pick242 1 t8635 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w242 pick242 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t8634 t8386 k242_1_0 k242_1_1
private theorem k242_1_3 : check w242 pick242 1 t8641 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k242_1_4 : check w242 pick242 1 t8643 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k242_1_5 : check w242 pick242 1 t8644 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w242 pick242 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t8641 t8643 k242_1_3 k242_1_4
private theorem k242_1_6 : check w242 pick242 1 t8645 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w242 pick242 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8635 t8644 k242_1_2 k242_1_5
private theorem k242_1_7 : check w242 pick242 1 t7489 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k242_1_8 : check w242 pick242 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k242_1_9 : check w242 pick242 1 t7490 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w242 pick242 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7489 t6872 k242_1_7 k242_1_8
private theorem k242_1_10 : check w242 pick242 1 t6924 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k242_1_11 : check w242 pick242 1 t8648 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k242_1_12 : check w242 pick242 1 t8649 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w242 pick242 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6924 t8648 k242_1_10 k242_1_11
private theorem k242_1_13 : check w242 pick242 1 t8650 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w242 pick242 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7490 t8649 k242_1_9 k242_1_12
private theorem k242_1_14 : check w242 pick242 1 t8651 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w242 pick242 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8645 t8650 k242_1_6 k242_1_13
theorem cov242_1 : PA.Covered 1 (OZ.Valid 1 w242.low w242.t w242.y w242.r w242.cap) (P33.root 1) :=
  Night6836Tree.sound w242 pick242 1 t8651 _ k242_1_14
private theorem k242_2_0 : check w242 pick242 2 t5566 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k242_2_1 : check w242 pick242 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k242_2_2 : check w242 pick242 2 t8216 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w242 pick242 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5566 t3303 k242_2_0 k242_2_1
theorem cov242_2 : PA.Covered 2 (OZ.Valid 2 w242.low w242.t w242.y w242.r w242.cap) (P33.root 2) :=
  Night6836Tree.sound w242 pick242 2 t8216 _ k242_2_2
theorem cov242_3 : PA.Covered 3 (OZ.Valid 3 w242.low w242.t w242.y w242.r w242.cap) (P33.root 3) :=
  Night6836Tree.sound w242 pick242 3 t564 _ (by decide +kernel)
theorem cov242_4 : PA.Covered 4 (OZ.Valid 4 w242.low w242.t w242.y w242.r w242.cap) (P33.root 4) :=
  Night6836Tree.sound w242 pick242 4 t565 _ (by decide +kernel)
theorem cov242_5 : PA.Covered 5 (OZ.Valid 5 w242.low w242.t w242.y w242.r w242.cap) (P33.root 5) :=
  Night6836Tree.sound w242 pick242 5 t566 _ (by decide +kernel)
theorem cov242_6 : PA.Covered 6 (OZ.Valid 6 w242.low w242.t w242.y w242.r w242.cap) (P33.root 6) :=
  Night6836Tree.sound w242 pick242 6 t567 _ (by decide +kernel)
theorem cov242_7 : PA.Covered 7 (OZ.Valid 7 w242.low w242.t w242.y w242.r w242.cap) (P33.root 7) :=
  Night6836Tree.sound w242 pick242 7 t2134 _ (by decide +kernel)
theorem window242 : P33.WindowCount w242 := by
  apply P33.window_count w242 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov242_1
  · exact cov242_2
  · exact cov242_3
  · exact cov242_4
  · exact cov242_5
  · exact cov242_6
  · exact cov242_7
def w243 : P33.Window := ⟨13,41,5347,5117,246944739923144878,34030,36000,5000000,81920000000⟩
def h243_0 : Height w243 := ⟨34030,36000,by decide +kernel⟩
def h243_1 : Height w243 := ⟨38218,33000,by decide +kernel⟩
def h243_2 : Height w243 := ⟨43331,30000,by decide +kernel⟩
def h243_3 : Height w243 := ⟨49942,27000,by decide +kernel⟩
def h243_4 : Height w243 := ⟨59223,24000,by decide +kernel⟩
def h243_5 : Height w243 := ⟨73985,21000,by decide +kernel⟩
def pick243 (cl : ℕ) : Height w243 := if cl<70 then (if cl<4 then (h243_0) else (if cl<18 then (h243_1) else (h243_2))) else (if cl<302 then (h243_3) else (if cl<998 then (h243_4) else (h243_5)))
private theorem k243_1_0 : check w243 pick243 1 t7551 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k243_1_1 : check w243 pick243 1 t7555 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k243_1_2 : check w243 pick243 1 t7556 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w243 pick243 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7551 t7555 k243_1_0 k243_1_1
private theorem k243_1_3 : check w243 pick243 1 t7559 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k243_1_4 : check w243 pick243 1 t8652 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k243_1_5 : check w243 pick243 1 t8653 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w243 pick243 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7559 t8652 k243_1_3 k243_1_4
private theorem k243_1_6 : check w243 pick243 1 t8654 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w243 pick243 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7556 t8653 k243_1_2 k243_1_5
private theorem k243_1_7 : check w243 pick243 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k243_1_8 : check w243 pick243 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k243_1_9 : check w243 pick243 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w243 pick243 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k243_1_7 k243_1_8
private theorem k243_1_10 : check w243 pick243 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k243_1_11 : check w243 pick243 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k243_1_12 : check w243 pick243 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w243 pick243 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k243_1_10 k243_1_11
private theorem k243_1_13 : check w243 pick243 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w243 pick243 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k243_1_9 k243_1_12
private theorem k243_1_14 : check w243 pick243 1 t8655 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w243 pick243 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8654 t7649 k243_1_6 k243_1_13
theorem cov243_1 : PA.Covered 1 (OZ.Valid 1 w243.low w243.t w243.y w243.r w243.cap) (P33.root 1) :=
  Night6836Tree.sound w243 pick243 1 t8655 _ k243_1_14
private theorem k243_2_0 : check w243 pick243 2 t5566 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k243_2_1 : check w243 pick243 2 t5541 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k243_2_2 : check w243 pick243 2 t5567 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w243 pick243 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5566 t5541 k243_2_0 k243_2_1
theorem cov243_2 : PA.Covered 2 (OZ.Valid 2 w243.low w243.t w243.y w243.r w243.cap) (P33.root 2) :=
  Night6836Tree.sound w243 pick243 2 t5567 _ k243_2_2
theorem cov243_3 : PA.Covered 3 (OZ.Valid 3 w243.low w243.t w243.y w243.r w243.cap) (P33.root 3) :=
  Night6836Tree.sound w243 pick243 3 t564 _ (by decide +kernel)
theorem cov243_4 : PA.Covered 4 (OZ.Valid 4 w243.low w243.t w243.y w243.r w243.cap) (P33.root 4) :=
  Night6836Tree.sound w243 pick243 4 t565 _ (by decide +kernel)
theorem cov243_5 : PA.Covered 5 (OZ.Valid 5 w243.low w243.t w243.y w243.r w243.cap) (P33.root 5) :=
  Night6836Tree.sound w243 pick243 5 t566 _ (by decide +kernel)
theorem cov243_6 : PA.Covered 6 (OZ.Valid 6 w243.low w243.t w243.y w243.r w243.cap) (P33.root 6) :=
  Night6836Tree.sound w243 pick243 6 t567 _ (by decide +kernel)
theorem cov243_7 : PA.Covered 7 (OZ.Valid 7 w243.low w243.t w243.y w243.r w243.cap) (P33.root 7) :=
  Night6836Tree.sound w243 pick243 7 t2134 _ (by decide +kernel)
theorem window243 : P33.WindowCount w243 := by
  apply P33.window_count w243 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov243_1
  · exact cov243_2
  · exact cov243_3
  · exact cov243_4
  · exact cov243_5
  · exact cov243_6
  · exact cov243_7
def w244 : P33.Window := ⟨13,42,5116,4879,246460188934184202,35690,39000,5000000,81920000000⟩
def h244_0 : Height w244 := ⟨35690,39000,by decide +kernel⟩
def h244_1 : Height w244 := ⟨39661,36000,by decide +kernel⟩
def h244_2 : Height w244 := ⟨44379,33000,by decide +kernel⟩
def h244_3 : Height w244 := ⟨50241,30000,by decide +kernel⟩
def h244_4 : Height w244 := ⟨57989,27000,by decide +kernel⟩
def h244_5 : Height w244 := ⟨69176,24000,by decide +kernel⟩
def pick244 (cl : ℕ) : Height w244 := if cl<36 then (if cl<2 then (h244_0) else (if cl<10 then (h244_1) else (h244_2))) else (if cl<154 then (h244_3) else (if cl<853 then (h244_4) else (h244_5)))
private theorem k244_1_0 : check w244 pick244 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k244_1_1 : check w244 pick244 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k244_1_2 : check w244 pick244 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w244 pick244 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k244_1_0 k244_1_1
private theorem k244_1_3 : check w244 pick244 1 t7559 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k244_1_4 : check w244 pick244 1 t7482 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k244_1_5 : check w244 pick244 1 t7560 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w244 pick244 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7559 t7482 k244_1_3 k244_1_4
private theorem k244_1_6 : check w244 pick244 1 t8656 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w244 pick244 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t6708 t7560 k244_1_2 k244_1_5
private theorem k244_1_7 : check w244 pick244 1 t7489 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k244_1_8 : check w244 pick244 1 t8659 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k244_1_9 : check w244 pick244 1 t8660 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w244 pick244 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t7489 t8659 k244_1_7 k244_1_8
private theorem k244_1_10 : check w244 pick244 1 t8663 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k244_1_11 : check w244 pick244 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k244_1_12 : check w244 pick244 1 t8664 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w244 pick244 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t8663 t7590 k244_1_10 k244_1_11
private theorem k244_1_13 : check w244 pick244 1 t8665 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w244 pick244 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t8660 t8664 k244_1_9 k244_1_12
private theorem k244_1_14 : check w244 pick244 1 t8666 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w244 pick244 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8656 t8665 k244_1_6 k244_1_13
theorem cov244_1 : PA.Covered 1 (OZ.Valid 1 w244.low w244.t w244.y w244.r w244.cap) (P33.root 1) :=
  Night6836Tree.sound w244 pick244 1 t8666 _ k244_1_14
private theorem k244_2_0 : check w244 pick244 2 t5566 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k244_2_1 : check w244 pick244 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k244_2_2 : check w244 pick244 2 t8216 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w244 pick244 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5566 t3303 k244_2_0 k244_2_1
theorem cov244_2 : PA.Covered 2 (OZ.Valid 2 w244.low w244.t w244.y w244.r w244.cap) (P33.root 2) :=
  Night6836Tree.sound w244 pick244 2 t8216 _ k244_2_2
theorem cov244_3 : PA.Covered 3 (OZ.Valid 3 w244.low w244.t w244.y w244.r w244.cap) (P33.root 3) :=
  Night6836Tree.sound w244 pick244 3 t564 _ (by decide +kernel)
theorem cov244_4 : PA.Covered 4 (OZ.Valid 4 w244.low w244.t w244.y w244.r w244.cap) (P33.root 4) :=
  Night6836Tree.sound w244 pick244 4 t565 _ (by decide +kernel)
theorem cov244_5 : PA.Covered 5 (OZ.Valid 5 w244.low w244.t w244.y w244.r w244.cap) (P33.root 5) :=
  Night6836Tree.sound w244 pick244 5 t566 _ (by decide +kernel)
theorem cov244_6 : PA.Covered 6 (OZ.Valid 6 w244.low w244.t w244.y w244.r w244.cap) (P33.root 6) :=
  Night6836Tree.sound w244 pick244 6 t567 _ (by decide +kernel)
theorem cov244_7 : PA.Covered 7 (OZ.Valid 7 w244.low w244.t w244.y w244.r w244.cap) (P33.root 7) :=
  Night6836Tree.sound w244 pick244 7 t2134 _ (by decide +kernel)
theorem window244 : P33.WindowCount w244 := by
  apply P33.window_count w244 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov244_1
  · exact cov244_2
  · exact cov244_3
  · exact cov244_4
  · exact cov244_5
  · exact cov244_6
  · exact cov244_7
def w245 : P33.Window := ⟨13,43,4878,4634,246302339160866752,41905,39000,5000000,81920000000⟩
def h245_0 : Height w245 := ⟨41905,39000,by decide +kernel⟩
def h245_1 : Height w245 := ⟨46386,36000,by decide +kernel⟩
def h245_2 : Height w245 := ⟨51801,33000,by decide +kernel⟩
def h245_3 : Height w245 := ⟨58665,30000,by decide +kernel⟩
def h245_4 : Height w245 := ⟨67965,27000,by decide +kernel⟩
def h245_5 : Height w245 := ⟨81831,24000,by decide +kernel⟩
def pick245 (cl : ℕ) : Height w245 := if cl<83 then (if cl<5 then (h245_0) else (if cl<32 then (h245_1) else (h245_2))) else (if cl<302 then (h245_3) else (if cl<976 then (h245_4) else (h245_5)))
private theorem k245_1_0 : check w245 pick245 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k245_1_1 : check w245 pick245 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k245_1_2 : check w245 pick245 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w245 pick245 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k245_1_0 k245_1_1
private theorem k245_1_3 : check w245 pick245 1 t8669 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k245_1_4 : check w245 pick245 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k245_1_5 : check w245 pick245 1 t8670 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w245 pick245 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t8669 t7348 k245_1_3 k245_1_4
private theorem k245_1_6 : check w245 pick245 1 t8671 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w245 pick245 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t8670 k245_1_2 k245_1_5
private theorem k245_1_7 : check w245 pick245 1 t7489 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k245_1_8 : check w245 pick245 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k245_1_9 : check w245 pick245 1 t7490 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w245 pick245 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7489 t6872 k245_1_7 k245_1_8
private theorem k245_1_10 : check w245 pick245 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k245_1_11 : check w245 pick245 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k245_1_12 : check w245 pick245 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w245 pick245 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k245_1_10 k245_1_11
private theorem k245_1_13 : check w245 pick245 1 t7491 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w245 pick245 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7490 t7190 k245_1_9 k245_1_12
private theorem k245_1_14 : check w245 pick245 1 t8672 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w245 pick245 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8671 t7491 k245_1_6 k245_1_13
theorem cov245_1 : PA.Covered 1 (OZ.Valid 1 w245.low w245.t w245.y w245.r w245.cap) (P33.root 1) :=
  Night6836Tree.sound w245 pick245 1 t8672 _ k245_1_14
private theorem k245_2_0 : check w245 pick245 2 t5566 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k245_2_1 : check w245 pick245 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k245_2_2 : check w245 pick245 2 t8216 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w245 pick245 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5566 t3303 k245_2_0 k245_2_1
theorem cov245_2 : PA.Covered 2 (OZ.Valid 2 w245.low w245.t w245.y w245.r w245.cap) (P33.root 2) :=
  Night6836Tree.sound w245 pick245 2 t8216 _ k245_2_2
theorem cov245_3 : PA.Covered 3 (OZ.Valid 3 w245.low w245.t w245.y w245.r w245.cap) (P33.root 3) :=
  Night6836Tree.sound w245 pick245 3 t564 _ (by decide +kernel)
theorem cov245_4 : PA.Covered 4 (OZ.Valid 4 w245.low w245.t w245.y w245.r w245.cap) (P33.root 4) :=
  Night6836Tree.sound w245 pick245 4 t565 _ (by decide +kernel)
theorem cov245_5 : PA.Covered 5 (OZ.Valid 5 w245.low w245.t w245.y w245.r w245.cap) (P33.root 5) :=
  Night6836Tree.sound w245 pick245 5 t566 _ (by decide +kernel)
theorem cov245_6 : PA.Covered 6 (OZ.Valid 6 w245.low w245.t w245.y w245.r w245.cap) (P33.root 6) :=
  Night6836Tree.sound w245 pick245 6 t567 _ (by decide +kernel)
theorem cov245_7 : PA.Covered 7 (OZ.Valid 7 w245.low w245.t w245.y w245.r w245.cap) (P33.root 7) :=
  Night6836Tree.sound w245 pick245 7 t2134 _ (by decide +kernel)
theorem window245 : P33.WindowCount w245 := by
  apply P33.window_count w245 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov245_1
  · exact cov245_2
  · exact cov245_3
  · exact cov245_4
  · exact cov245_5
  · exact cov245_6
  · exact cov245_7
def w246 : P33.Window := ⟨13,44,4236,3287,244853468438288430,58663,57000,5000000,81920000000⟩
def h246_0 : Height w246 := ⟨58663,57000,by decide +kernel⟩
def h246_1 : Height w246 := ⟨62775,54000,by decide +kernel⟩
def h246_2 : Height w246 := ⟨67381,51000,by decide +kernel⟩
def h246_3 : Height w246 := ⟨72639,48000,by decide +kernel⟩
def h246_4 : Height w246 := ⟨78775,45000,by decide +kernel⟩
def h246_5 : Height w246 := ⟨86138,42000,by decide +kernel⟩
def h246_6 : Height w246 := ⟨95284,39000,by decide +kernel⟩
def h246_7 : Height w246 := ⟨107167,36000,by decide +kernel⟩
def pick246 (cl : ℕ) : Height w246 := if cl<43 then (if cl<6 then (if cl<3 then (h246_0) else (h246_1)) else (if cl<32 then (h246_2) else (h246_3))) else (if cl<299 then (if cl<117 then (h246_4) else (h246_5)) else (if cl<989 then (h246_6) else (h246_7)))
private theorem k246_1_0 : check w246 pick246 1 t8105 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k246_1_1 : check w246 pick246 1 t8694 ⟨1,7,2,16,1,52,56,90⟩ = true := by decide +kernel
private theorem k246_1_2 : check w246 pick246 1 t8695 ⟨1,7,2,16,1,52,1,90⟩ = true := glue w246 pick246 1 ⟨1,7,2,16,1,52,1,90⟩ 3 55 t8105 t8694 k246_1_0 k246_1_1
private theorem k246_1_3 : check w246 pick246 1 t8700 ⟨1,7,2,16,1,20,91,145⟩ = true := by decide +kernel
private theorem k246_1_4 : check w246 pick246 1 t8713 ⟨1,7,2,16,21,52,91,145⟩ = true := by decide +kernel
private theorem k246_1_5 : check w246 pick246 1 t8714 ⟨1,7,2,16,1,52,91,145⟩ = true := glue w246 pick246 1 ⟨1,7,2,16,1,52,91,145⟩ 2 20 t8700 t8713 k246_1_3 k246_1_4
private theorem k246_1_6 : check w246 pick246 1 t8715 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w246 pick246 1 ⟨1,7,2,16,1,52,1,145⟩ 3 90 t8695 t8714 k246_1_2 k246_1_5
private theorem k246_1_7 : check w246 pick246 1 t8136 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k246_1_8 : check w246 pick246 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k246_1_9 : check w246 pick246 1 t8137 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w246 pick246 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t8136 t7702 k246_1_7 k246_1_8
private theorem k246_1_10 : check w246 pick246 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k246_1_11 : check w246 pick246 1 t8139 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k246_1_12 : check w246 pick246 1 t8140 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w246 pick246 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t8139 k246_1_10 k246_1_11
private theorem k246_1_13 : check w246 pick246 1 t8141 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w246 pick246 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t8137 t8140 k246_1_9 k246_1_12
private theorem k246_1_14 : check w246 pick246 1 t8716 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w246 pick246 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t8715 t8141 k246_1_6 k246_1_13
theorem cov246_1 : PA.Covered 1 (OZ.Valid 1 w246.low w246.t w246.y w246.r w246.cap) (P33.root 1) :=
  Night6836Tree.sound w246 pick246 1 t8716 _ k246_1_14
theorem cov246_2 : PA.Covered 2 (OZ.Valid 2 w246.low w246.t w246.y w246.r w246.cap) (P33.root 2) :=
  Night6836Tree.sound w246 pick246 2 t8724 _ (by decide +kernel)
theorem cov246_3 : PA.Covered 3 (OZ.Valid 3 w246.low w246.t w246.y w246.r w246.cap) (P33.root 3) :=
  Night6836Tree.sound w246 pick246 3 t564 _ (by decide +kernel)
theorem cov246_4 : PA.Covered 4 (OZ.Valid 4 w246.low w246.t w246.y w246.r w246.cap) (P33.root 4) :=
  Night6836Tree.sound w246 pick246 4 t565 _ (by decide +kernel)
theorem cov246_5 : PA.Covered 5 (OZ.Valid 5 w246.low w246.t w246.y w246.r w246.cap) (P33.root 5) :=
  Night6836Tree.sound w246 pick246 5 t566 _ (by decide +kernel)
theorem cov246_6 : PA.Covered 6 (OZ.Valid 6 w246.low w246.t w246.y w246.r w246.cap) (P33.root 6) :=
  Night6836Tree.sound w246 pick246 6 t567 _ (by decide +kernel)
theorem cov246_7 : PA.Covered 7 (OZ.Valid 7 w246.low w246.t w246.y w246.r w246.cap) (P33.root 7) :=
  Night6836Tree.sound w246 pick246 7 t2134 _ (by decide +kernel)
theorem window246 : P33.WindowCount w246 := by
  apply P33.window_count w246 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov246_1
  · exact cov246_2
  · exact cov246_3
  · exact cov246_4
  · exact cov246_5
  · exact cov246_6
  · exact cov246_7
def w247 : P33.Window := ⟨13,44,4633,4382,246177842301956037,45042,42000,5000000,81920000000⟩
def h247_0 : Height w247 := ⟨45042,42000,by decide +kernel⟩
def h247_1 : Height w247 := ⟨49403,39000,by decide +kernel⟩
def h247_2 : Height w247 := ⟨54567,36000,by decide +kernel⟩
def h247_3 : Height w247 := ⟨60924,33000,by decide +kernel⟩
def h247_4 : Height w247 := ⟨69170,30000,by decide +kernel⟩
def h247_5 : Height w247 := ⟨80664,27000,by decide +kernel⟩
def pick247 (cl : ℕ) : Height w247 := if cl<49 then (if cl<5 then (h247_0) else (if cl<18 then (h247_1) else (h247_2))) else (if cl<210 then (h247_3) else (if cl<922 then (h247_4) else (h247_5)))
private theorem k247_1_0 : check w247 pick247 1 t7393 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k247_1_1 : check w247 pick247 1 t575 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k247_1_2 : check w247 pick247 1 t7394 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w247 pick247 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7393 t575 k247_1_0 k247_1_1
private theorem k247_1_3 : check w247 pick247 1 t7732 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k247_1_4 : check w247 pick247 1 t7403 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k247_1_5 : check w247 pick247 1 t7733 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w247 pick247 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7732 t7403 k247_1_3 k247_1_4
private theorem k247_1_6 : check w247 pick247 1 t8725 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w247 pick247 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7394 t7733 k247_1_2 k247_1_5
private theorem k247_1_7 : check w247 pick247 1 t7701 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k247_1_8 : check w247 pick247 1 t8730 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k247_1_9 : check w247 pick247 1 t8731 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w247 pick247 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7701 t8730 k247_1_7 k247_1_8
private theorem k247_1_10 : check w247 pick247 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k247_1_11 : check w247 pick247 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k247_1_12 : check w247 pick247 1 t7319 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w247 pick247 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t7318 k247_1_10 k247_1_11
private theorem k247_1_13 : check w247 pick247 1 t8732 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w247 pick247 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t8731 t7319 k247_1_9 k247_1_12
private theorem k247_1_14 : check w247 pick247 1 t8733 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w247 pick247 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8725 t8732 k247_1_6 k247_1_13
theorem cov247_1 : PA.Covered 1 (OZ.Valid 1 w247.low w247.t w247.y w247.r w247.cap) (P33.root 1) :=
  Night6836Tree.sound w247 pick247 1 t8733 _ k247_1_14
private theorem k247_2_0 : check w247 pick247 2 t6415 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k247_2_1 : check w247 pick247 2 t8252 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k247_2_2 : check w247 pick247 2 t8623 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w247 pick247 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t6415 t8252 k247_2_0 k247_2_1
theorem cov247_2 : PA.Covered 2 (OZ.Valid 2 w247.low w247.t w247.y w247.r w247.cap) (P33.root 2) :=
  Night6836Tree.sound w247 pick247 2 t8623 _ k247_2_2
theorem cov247_3 : PA.Covered 3 (OZ.Valid 3 w247.low w247.t w247.y w247.r w247.cap) (P33.root 3) :=
  Night6836Tree.sound w247 pick247 3 t564 _ (by decide +kernel)
theorem cov247_4 : PA.Covered 4 (OZ.Valid 4 w247.low w247.t w247.y w247.r w247.cap) (P33.root 4) :=
  Night6836Tree.sound w247 pick247 4 t565 _ (by decide +kernel)
theorem cov247_5 : PA.Covered 5 (OZ.Valid 5 w247.low w247.t w247.y w247.r w247.cap) (P33.root 5) :=
  Night6836Tree.sound w247 pick247 5 t566 _ (by decide +kernel)
theorem cov247_6 : PA.Covered 6 (OZ.Valid 6 w247.low w247.t w247.y w247.r w247.cap) (P33.root 6) :=
  Night6836Tree.sound w247 pick247 6 t567 _ (by decide +kernel)
theorem cov247_7 : PA.Covered 7 (OZ.Valid 7 w247.low w247.t w247.y w247.r w247.cap) (P33.root 7) :=
  Night6836Tree.sound w247 pick247 7 t2134 _ (by decide +kernel)
theorem window247 : P33.WindowCount w247 := by
  apply P33.window_count w247 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov247_1
  · exact cov247_2
  · exact cov247_3
  · exact cov247_4
  · exact cov247_5
  · exact cov247_6
  · exact cov247_7
def w248 : P33.Window := ⟨13,45,4381,4121,246228913705491625,49290,45000,5000000,81920000000⟩
def h248_0 : Height w248 := ⟨49290,45000,by decide +kernel⟩
def h248_1 : Height w248 := ⟨53632,42000,by decide +kernel⟩
def h248_2 : Height w248 := ⟨58699,39000,by decide +kernel⟩
def h248_3 : Height w248 := ⟨64811,36000,by decide +kernel⟩
def h248_4 : Height w248 := ⟨72500,33000,by decide +kernel⟩
def h248_5 : Height w248 := ⟨82741,30000,by decide +kernel⟩
def h248_6 : Height w248 := ⟨97502,27000,by decide +kernel⟩
def pick248 (cl : ℕ) : Height w248 := if cl<43 then (if cl<5 then (h248_0) else (if cl<18 then (h248_1) else (h248_2))) else (if cl<615 then (if cl<165 then (h248_3) else (h248_4)) else (if cl<998 then (h248_5) else (h248_6)))
private theorem k248_1_0 : check w248 pick248 1 t7724 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k248_1_1 : check w248 pick248 1 t7727 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k248_1_2 : check w248 pick248 1 t7728 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w248 pick248 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7724 t7727 k248_1_0 k248_1_1
private theorem k248_1_3 : check w248 pick248 1 t7732 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k248_1_4 : check w248 pick248 1 t7403 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k248_1_5 : check w248 pick248 1 t7733 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w248 pick248 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7732 t7403 k248_1_3 k248_1_4
private theorem k248_1_6 : check w248 pick248 1 t7734 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w248 pick248 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7728 t7733 k248_1_2 k248_1_5
private theorem k248_1_7 : check w248 pick248 1 t7701 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k248_1_8 : check w248 pick248 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k248_1_9 : check w248 pick248 1 t7703 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w248 pick248 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7701 t7702 k248_1_7 k248_1_8
private theorem k248_1_10 : check w248 pick248 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k248_1_11 : check w248 pick248 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k248_1_12 : check w248 pick248 1 t7319 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w248 pick248 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t7318 k248_1_10 k248_1_11
private theorem k248_1_13 : check w248 pick248 1 t7704 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w248 pick248 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7703 t7319 k248_1_9 k248_1_12
private theorem k248_1_14 : check w248 pick248 1 t7735 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w248 pick248 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7734 t7704 k248_1_6 k248_1_13
theorem cov248_1 : PA.Covered 1 (OZ.Valid 1 w248.low w248.t w248.y w248.r w248.cap) (P33.root 1) :=
  Night6836Tree.sound w248 pick248 1 t7735 _ k248_1_14
private theorem k248_2_0 : check w248 pick248 2 t6236 ⟨2,7,4,16,2,52,2,166⟩ = true := by decide +kernel
private theorem k248_2_1 : check w248 pick248 2 t8735 ⟨2,7,4,16,2,52,167,450⟩ = true := by decide +kernel
private theorem k248_2_2 : check w248 pick248 2 t8736 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w248 pick248 2 ⟨2,7,4,16,0,52,0,450⟩ 3 166 t6236 t8735 k248_2_0 k248_2_1
theorem cov248_2 : PA.Covered 2 (OZ.Valid 2 w248.low w248.t w248.y w248.r w248.cap) (P33.root 2) :=
  Night6836Tree.sound w248 pick248 2 t8736 _ k248_2_2
theorem cov248_3 : PA.Covered 3 (OZ.Valid 3 w248.low w248.t w248.y w248.r w248.cap) (P33.root 3) :=
  Night6836Tree.sound w248 pick248 3 t564 _ (by decide +kernel)
theorem cov248_4 : PA.Covered 4 (OZ.Valid 4 w248.low w248.t w248.y w248.r w248.cap) (P33.root 4) :=
  Night6836Tree.sound w248 pick248 4 t565 _ (by decide +kernel)
theorem cov248_5 : PA.Covered 5 (OZ.Valid 5 w248.low w248.t w248.y w248.r w248.cap) (P33.root 5) :=
  Night6836Tree.sound w248 pick248 5 t566 _ (by decide +kernel)
theorem cov248_6 : PA.Covered 6 (OZ.Valid 6 w248.low w248.t w248.y w248.r w248.cap) (P33.root 6) :=
  Night6836Tree.sound w248 pick248 6 t567 _ (by decide +kernel)
theorem cov248_7 : PA.Covered 7 (OZ.Valid 7 w248.low w248.t w248.y w248.r w248.cap) (P33.root 7) :=
  Night6836Tree.sound w248 pick248 7 t2134 _ (by decide +kernel)
theorem window248 : P33.WindowCount w248 := by
  apply P33.window_count w248 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov248_1
  · exact cov248_2
  · exact cov248_3
  · exact cov248_4
  · exact cov248_5
  · exact cov248_6
  · exact cov248_7
def w249 : P33.Window := ⟨13,46,4120,3852,246128147915825573,50997,51000,5000000,81920000000⟩
def h249_0 : Height w249 := ⟨50997,51000,by decide +kernel⟩
def h249_1 : Height w249 := ⟨54906,48000,by decide +kernel⟩
def h249_2 : Height w249 := ⟨59323,45000,by decide +kernel⟩
def h249_3 : Height w249 := ⟨64428,42000,by decide +kernel⟩
def h249_4 : Height w249 := ⟨70497,39000,by decide +kernel⟩
def h249_5 : Height w249 := ⟨77973,36000,by decide +kernel⟩
def h249_6 : Height w249 := ⟨87622,33000,by decide +kernel⟩
def h249_7 : Height w249 := ⟨100880,30000,by decide +kernel⟩
def pick249 (cl : ℕ) : Height w249 := if cl<40 then (if cl<5 then (if cl<2 then (h249_0) else (h249_1)) else (if cl<18 then (h249_2) else (h249_3))) else (if cl<343 then (if cl<132 then (h249_4) else (h249_5)) else (if cl<989 then (h249_6) else (h249_7)))
private theorem k249_1_0 : check w249 pick249 1 t8105 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k249_1_1 : check w249 pick249 1 t8277 ⟨1,7,2,16,1,52,56,90⟩ = true := by decide +kernel
private theorem k249_1_2 : check w249 pick249 1 t8278 ⟨1,7,2,16,1,52,1,90⟩ = true := glue w249 pick249 1 ⟨1,7,2,16,1,52,1,90⟩ 3 55 t8105 t8277 k249_1_0 k249_1_1
private theorem k249_1_3 : check w249 pick249 1 t8741 ⟨1,7,2,16,1,52,91,124⟩ = true := by decide +kernel
private theorem k249_1_4 : check w249 pick249 1 t8742 ⟨1,7,2,16,1,52,125,145⟩ = true := by decide +kernel
private theorem k249_1_5 : check w249 pick249 1 t8743 ⟨1,7,2,16,1,52,91,145⟩ = true := glue w249 pick249 1 ⟨1,7,2,16,1,52,91,145⟩ 3 124 t8741 t8742 k249_1_3 k249_1_4
private theorem k249_1_6 : check w249 pick249 1 t8744 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w249 pick249 1 ⟨1,7,2,16,1,52,1,145⟩ 3 90 t8278 t8743 k249_1_2 k249_1_5
private theorem k249_1_7 : check w249 pick249 1 t8136 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k249_1_8 : check w249 pick249 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k249_1_9 : check w249 pick249 1 t8137 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w249 pick249 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t8136 t7702 k249_1_7 k249_1_8
private theorem k249_1_10 : check w249 pick249 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k249_1_11 : check w249 pick249 1 t8139 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k249_1_12 : check w249 pick249 1 t8140 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w249 pick249 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t8139 k249_1_10 k249_1_11
private theorem k249_1_13 : check w249 pick249 1 t8141 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w249 pick249 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t8137 t8140 k249_1_9 k249_1_12
private theorem k249_1_14 : check w249 pick249 1 t8745 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w249 pick249 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t8744 t8141 k249_1_6 k249_1_13
theorem cov249_1 : PA.Covered 1 (OZ.Valid 1 w249.low w249.t w249.y w249.r w249.cap) (P33.root 1) :=
  Night6836Tree.sound w249 pick249 1 t8745 _ k249_1_14
theorem cov249_2 : PA.Covered 2 (OZ.Valid 2 w249.low w249.t w249.y w249.r w249.cap) (P33.root 2) :=
  Night6836Tree.sound w249 pick249 2 t8747 _ (by decide +kernel)
theorem cov249_3 : PA.Covered 3 (OZ.Valid 3 w249.low w249.t w249.y w249.r w249.cap) (P33.root 3) :=
  Night6836Tree.sound w249 pick249 3 t564 _ (by decide +kernel)
theorem cov249_4 : PA.Covered 4 (OZ.Valid 4 w249.low w249.t w249.y w249.r w249.cap) (P33.root 4) :=
  Night6836Tree.sound w249 pick249 4 t565 _ (by decide +kernel)
theorem cov249_5 : PA.Covered 5 (OZ.Valid 5 w249.low w249.t w249.y w249.r w249.cap) (P33.root 5) :=
  Night6836Tree.sound w249 pick249 5 t566 _ (by decide +kernel)
theorem cov249_6 : PA.Covered 6 (OZ.Valid 6 w249.low w249.t w249.y w249.r w249.cap) (P33.root 6) :=
  Night6836Tree.sound w249 pick249 6 t567 _ (by decide +kernel)
theorem cov249_7 : PA.Covered 7 (OZ.Valid 7 w249.low w249.t w249.y w249.r w249.cap) (P33.root 7) :=
  Night6836Tree.sound w249 pick249 7 t2134 _ (by decide +kernel)
theorem window249 : P33.WindowCount w249 := by
  apply P33.window_count w249 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov249_1
  · exact cov249_2
  · exact cov249_3
  · exact cov249_4
  · exact cov249_5
  · exact cov249_6
  · exact cov249_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w250 : P33.Window := ⟨13,47,3851,3574,245942585317201466,58261,54000,5000000,81920000000⟩
def h250_0 : Height w250 := ⟨58261,54000,by decide +kernel⟩
def h250_1 : Height w250 := ⟨62348,51000,by decide +kernel⟩
def h250_2 : Height w250 := ⟨66950,48000,by decide +kernel⟩
def h250_3 : Height w250 := ⟨72237,45000,by decide +kernel⟩
def h250_4 : Height w250 := ⟨78462,42000,by decide +kernel⟩
def h250_5 : Height w250 := ⟨86023,39000,by decide +kernel⟩
def h250_6 : Height w250 := ⟨95576,36000,by decide +kernel⟩
def pick250 (cl : ℕ) : Height w250 := if cl<32 then (if cl<2 then (h250_0) else (if cl<6 then (h250_1) else (h250_2))) else (if cl<145 then (if cl<44 then (h250_3) else (h250_4)) else (if cl<331 then (h250_5) else (h250_6)))
private theorem k250_1_0 : check w250 pick250 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k250_1_1 : check w250 pick250 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k250_1_2 : check w250 pick250 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w250 pick250 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k250_1_0 k250_1_1
private theorem k250_1_3 : check w250 pick250 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k250_1_4 : check w250 pick250 1 t8752 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k250_1_5 : check w250 pick250 1 t8753 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w250 pick250 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t8752 k250_1_3 k250_1_4
private theorem k250_1_6 : check w250 pick250 1 t8754 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w250 pick250 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8753 k250_1_2 k250_1_5
theorem cov250_1 : PA.Covered 1 (OZ.Valid 1 w250.low w250.t w250.y w250.r w250.cap) (P33.root 1) :=
  Night6836Tree.sound w250 pick250 1 t8754 _ k250_1_6
theorem cov250_2 : PA.Covered 2 (OZ.Valid 2 w250.low w250.t w250.y w250.r w250.cap) (P33.root 2) :=
  Night6836Tree.sound w250 pick250 2 t8756 _ (by decide +kernel)
theorem cov250_3 : PA.Covered 3 (OZ.Valid 3 w250.low w250.t w250.y w250.r w250.cap) (P33.root 3) :=
  Night6836Tree.sound w250 pick250 3 t564 _ (by decide +kernel)
theorem cov250_4 : PA.Covered 4 (OZ.Valid 4 w250.low w250.t w250.y w250.r w250.cap) (P33.root 4) :=
  Night6836Tree.sound w250 pick250 4 t565 _ (by decide +kernel)
theorem cov250_5 : PA.Covered 5 (OZ.Valid 5 w250.low w250.t w250.y w250.r w250.cap) (P33.root 5) :=
  Night6836Tree.sound w250 pick250 5 t566 _ (by decide +kernel)
theorem cov250_6 : PA.Covered 6 (OZ.Valid 6 w250.low w250.t w250.y w250.r w250.cap) (P33.root 6) :=
  Night6836Tree.sound w250 pick250 6 t567 _ (by decide +kernel)
theorem cov250_7 : PA.Covered 7 (OZ.Valid 7 w250.low w250.t w250.y w250.r w250.cap) (P33.root 7) :=
  Night6836Tree.sound w250 pick250 7 t2134 _ (by decide +kernel)
theorem window250 : P33.WindowCount w250 := by
  apply P33.window_count w250 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov250_1
  · exact cov250_2
  · exact cov250_3
  · exact cov250_4
  · exact cov250_5
  · exact cov250_6
  · exact cov250_7
def w251 : P33.Window := ⟨13,48,3573,3287,245615698316949362,63961,60000,5000000,81920000000⟩
def h251_0 : Height w251 := ⟨63961,60000,by decide +kernel⟩
def h251_1 : Height w251 := ⟨67918,57000,by decide +kernel⟩
def h251_2 : Height w251 := ⟨72300,54000,by decide +kernel⟩
def h251_3 : Height w251 := ⟨77229,51000,by decide +kernel⟩
def h251_4 : Height w251 := ⟨82875,48000,by decide +kernel⟩
def h251_5 : Height w251 := ⟨89488,45000,by decide +kernel⟩
def h251_6 : Height w251 := ⟨97451,42000,by decide +kernel⟩
def h251_7 : Height w251 := ⟨107375,39000,by decide +kernel⟩
def pick251 (cl : ℕ) : Height w251 := if cl<32 then (if cl<5 then (if cl<2 then (h251_0) else (h251_1)) else (if cl<12 then (h251_2) else (h251_3))) else (if cl<302 then (if cl<70 then (h251_4) else (h251_5)) else (if cl<498 then (h251_6) else (h251_7)))
private theorem k251_1_0 : check w251 pick251 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k251_1_1 : check w251 pick251 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k251_1_2 : check w251 pick251 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w251 pick251 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k251_1_0 k251_1_1
private theorem k251_1_3 : check w251 pick251 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k251_1_4 : check w251 pick251 1 t8752 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k251_1_5 : check w251 pick251 1 t8753 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w251 pick251 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t8752 k251_1_3 k251_1_4
private theorem k251_1_6 : check w251 pick251 1 t8754 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w251 pick251 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8753 k251_1_2 k251_1_5
theorem cov251_1 : PA.Covered 1 (OZ.Valid 1 w251.low w251.t w251.y w251.r w251.cap) (P33.root 1) :=
  Night6836Tree.sound w251 pick251 1 t8754 _ k251_1_6
theorem cov251_2 : PA.Covered 2 (OZ.Valid 2 w251.low w251.t w251.y w251.r w251.cap) (P33.root 2) :=
  Night6836Tree.sound w251 pick251 2 t6560 _ (by decide +kernel)
theorem cov251_3 : PA.Covered 3 (OZ.Valid 3 w251.low w251.t w251.y w251.r w251.cap) (P33.root 3) :=
  Night6836Tree.sound w251 pick251 3 t564 _ (by decide +kernel)
theorem cov251_4 : PA.Covered 4 (OZ.Valid 4 w251.low w251.t w251.y w251.r w251.cap) (P33.root 4) :=
  Night6836Tree.sound w251 pick251 4 t565 _ (by decide +kernel)
theorem cov251_5 : PA.Covered 5 (OZ.Valid 5 w251.low w251.t w251.y w251.r w251.cap) (P33.root 5) :=
  Night6836Tree.sound w251 pick251 5 t566 _ (by decide +kernel)
theorem cov251_6 : PA.Covered 6 (OZ.Valid 6 w251.low w251.t w251.y w251.r w251.cap) (P33.root 6) :=
  Night6836Tree.sound w251 pick251 6 t567 _ (by decide +kernel)
theorem cov251_7 : PA.Covered 7 (OZ.Valid 7 w251.low w251.t w251.y w251.r w251.cap) (P33.root 7) :=
  Night6836Tree.sound w251 pick251 7 t2134 _ (by decide +kernel)
theorem window251 : P33.WindowCount w251 := by
  apply P33.window_count w251 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov251_1
  · exact cov251_2
  · exact cov251_3
  · exact cov251_4
  · exact cov251_5
  · exact cov251_6
  · exact cov251_7
def w252 : P33.Window := ⟨13,49,3286,2990,245200460136548212,72718,66000,5000000,81920000000⟩
def h252_0 : Height w252 := ⟨72718,66000,by decide +kernel⟩
def h252_1 : Height w252 := ⟨76706,63000,by decide +kernel⟩
def h252_2 : Height w252 := ⟨81078,60000,by decide +kernel⟩
def h252_3 : Height w252 := ⟨85932,57000,by decide +kernel⟩
def h252_4 : Height w252 := ⟨91399,54000,by decide +kernel⟩
def h252_5 : Height w252 := ⟨97663,51000,by decide +kernel⟩
def h252_6 : Height w252 := ⟨104991,48000,by decide +kernel⟩
def h252_7 : Height w252 := ⟨113782,45000,by decide +kernel⟩
def pick252 (cl : ℕ) : Height w252 := if cl<32 then (if cl<5 then (if cl<2 then (h252_0) else (h252_1)) else (if cl<12 then (h252_2) else (h252_3))) else (if cl<117 then (if cl<46 then (h252_4) else (h252_5)) else (if cl<312 then (h252_6) else (h252_7)))
private theorem k252_1_0 : check w252 pick252 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k252_1_1 : check w252 pick252 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k252_1_2 : check w252 pick252 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w252 pick252 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k252_1_0 k252_1_1
private theorem k252_1_3 : check w252 pick252 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k252_1_4 : check w252 pick252 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k252_1_5 : check w252 pick252 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w252 pick252 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k252_1_3 k252_1_4
private theorem k252_1_6 : check w252 pick252 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w252 pick252 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k252_1_2 k252_1_5
theorem cov252_1 : PA.Covered 1 (OZ.Valid 1 w252.low w252.t w252.y w252.r w252.cap) (P33.root 1) :=
  Night6836Tree.sound w252 pick252 1 t8759 _ k252_1_6
theorem cov252_2 : PA.Covered 2 (OZ.Valid 2 w252.low w252.t w252.y w252.r w252.cap) (P33.root 2) :=
  Night6836Tree.sound w252 pick252 2 t6560 _ (by decide +kernel)
theorem cov252_3 : PA.Covered 3 (OZ.Valid 3 w252.low w252.t w252.y w252.r w252.cap) (P33.root 3) :=
  Night6836Tree.sound w252 pick252 3 t564 _ (by decide +kernel)
theorem cov252_4 : PA.Covered 4 (OZ.Valid 4 w252.low w252.t w252.y w252.r w252.cap) (P33.root 4) :=
  Night6836Tree.sound w252 pick252 4 t565 _ (by decide +kernel)
theorem cov252_5 : PA.Covered 5 (OZ.Valid 5 w252.low w252.t w252.y w252.r w252.cap) (P33.root 5) :=
  Night6836Tree.sound w252 pick252 5 t566 _ (by decide +kernel)
theorem cov252_6 : PA.Covered 6 (OZ.Valid 6 w252.low w252.t w252.y w252.r w252.cap) (P33.root 6) :=
  Night6836Tree.sound w252 pick252 6 t567 _ (by decide +kernel)
theorem cov252_7 : PA.Covered 7 (OZ.Valid 7 w252.low w252.t w252.y w252.r w252.cap) (P33.root 7) :=
  Night6836Tree.sound w252 pick252 7 t2134 _ (by decide +kernel)
theorem window252 : P33.WindowCount w252 := by
  apply P33.window_count w252 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov252_1
  · exact cov252_2
  · exact cov252_3
  · exact cov252_4
  · exact cov252_5
  · exact cov252_6
  · exact cov252_7
def w253 : P33.Window := ⟨13,50,2989,2683,239827082809402244,85803,72000,5000000,81920000000⟩
def h253_0 : Height w253 := ⟨85803,72000,by decide +kernel⟩
def h253_1 : Height w253 := ⟨89993,69000,by decide +kernel⟩
def h253_2 : Height w253 := ⟨94562,66000,by decide +kernel⟩
def h253_3 : Height w253 := ⟨99599,63000,by decide +kernel⟩
def h253_4 : Height w253 := ⟨105217,60000,by decide +kernel⟩
def h253_5 : Height w253 := ⟨111572,57000,by decide +kernel⟩
def h253_6 : Height w253 := ⟨118880,54000,by decide +kernel⟩
def h253_7 : Height w253 := ⟨127451,51000,by decide +kernel⟩
def h253_8 : Height w253 := ⟨137745,48000,by decide +kernel⟩
def pick253 (cl : ℕ) : Height w253 := if cl<32 then (if cl<6 then (if cl<4 then (h253_0) else (h253_1)) else (if cl<14 then (h253_2) else (h253_3))) else (if cl<117 then (if cl<49 then (h253_4) else (h253_5)) else (if cl<312 then (h253_6) else (if cl<644 then (h253_7) else (h253_8))))
private theorem k253_1_0 : check w253 pick253 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k253_1_1 : check w253 pick253 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k253_1_2 : check w253 pick253 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w253 pick253 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k253_1_0 k253_1_1
private theorem k253_1_3 : check w253 pick253 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k253_1_4 : check w253 pick253 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k253_1_5 : check w253 pick253 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w253 pick253 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k253_1_3 k253_1_4
private theorem k253_1_6 : check w253 pick253 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w253 pick253 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k253_1_2 k253_1_5
theorem cov253_1 : PA.Covered 1 (OZ.Valid 1 w253.low w253.t w253.y w253.r w253.cap) (P33.root 1) :=
  Night6836Tree.sound w253 pick253 1 t8759 _ k253_1_6
theorem cov253_2 : PA.Covered 2 (OZ.Valid 2 w253.low w253.t w253.y w253.r w253.cap) (P33.root 2) :=
  Night6836Tree.sound w253 pick253 2 t6560 _ (by decide +kernel)
theorem cov253_3 : PA.Covered 3 (OZ.Valid 3 w253.low w253.t w253.y w253.r w253.cap) (P33.root 3) :=
  Night6836Tree.sound w253 pick253 3 t564 _ (by decide +kernel)
theorem cov253_4 : PA.Covered 4 (OZ.Valid 4 w253.low w253.t w253.y w253.r w253.cap) (P33.root 4) :=
  Night6836Tree.sound w253 pick253 4 t565 _ (by decide +kernel)
theorem cov253_5 : PA.Covered 5 (OZ.Valid 5 w253.low w253.t w253.y w253.r w253.cap) (P33.root 5) :=
  Night6836Tree.sound w253 pick253 5 t566 _ (by decide +kernel)
theorem cov253_6 : PA.Covered 6 (OZ.Valid 6 w253.low w253.t w253.y w253.r w253.cap) (P33.root 6) :=
  Night6836Tree.sound w253 pick253 6 t567 _ (by decide +kernel)
theorem cov253_7 : PA.Covered 7 (OZ.Valid 7 w253.low w253.t w253.y w253.r w253.cap) (P33.root 7) :=
  Night6836Tree.sound w253 pick253 7 t2134 _ (by decide +kernel)
theorem window253 : P33.WindowCount w253 := by
  apply P33.window_count w253 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov253_1
  · exact cov253_2
  · exact cov253_3
  · exact cov253_4
  · exact cov253_5
  · exact cov253_6
  · exact cov253_7
def w254 : P33.Window := ⟨13,51,2682,2365,226917887164124258,97372,84000,5000000,81920000000⟩
def h254_0 : Height w254 := ⟨97372,84000,by decide +kernel⟩
def h254_1 : Height w254 := ⟨101370,81000,by decide +kernel⟩
def h254_2 : Height w254 := ⟨105660,78000,by decide +kernel⟩
def h254_3 : Height w254 := ⟨110295,75000,by decide +kernel⟩
def h254_4 : Height w254 := ⟨115345,72000,by decide +kernel⟩
def h254_5 : Height w254 := ⟨120896,69000,by decide +kernel⟩
def h254_6 : Height w254 := ⟨127063,66000,by decide +kernel⟩
def h254_7 : Height w254 := ⟨133996,63000,by decide +kernel⟩
def h254_8 : Height w254 := ⟨151060,57000,by decide +kernel⟩
def pick254 (cl : ℕ) : Height w254 := if cl<14 then (if cl<4 then (if cl<2 then (h254_0) else (h254_1)) else (if cl<6 then (h254_2) else (h254_3))) else (if cl<43 then (if cl<32 then (h254_4) else (h254_5)) else (if cl<92 then (h254_6) else (if cl<312 then (h254_7) else (h254_8))))
private theorem k254_1_0 : check w254 pick254 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k254_1_1 : check w254 pick254 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k254_1_2 : check w254 pick254 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w254 pick254 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k254_1_0 k254_1_1
private theorem k254_1_3 : check w254 pick254 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k254_1_4 : check w254 pick254 1 t8338 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k254_1_5 : check w254 pick254 1 t8339 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w254 pick254 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8338 k254_1_3 k254_1_4
private theorem k254_1_6 : check w254 pick254 1 t8760 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w254 pick254 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8339 k254_1_2 k254_1_5
theorem cov254_1 : PA.Covered 1 (OZ.Valid 1 w254.low w254.t w254.y w254.r w254.cap) (P33.root 1) :=
  Night6836Tree.sound w254 pick254 1 t8760 _ k254_1_6
theorem cov254_2 : PA.Covered 2 (OZ.Valid 2 w254.low w254.t w254.y w254.r w254.cap) (P33.root 2) :=
  Night6836Tree.sound w254 pick254 2 t6560 _ (by decide +kernel)
theorem cov254_3 : PA.Covered 3 (OZ.Valid 3 w254.low w254.t w254.y w254.r w254.cap) (P33.root 3) :=
  Night6836Tree.sound w254 pick254 3 t564 _ (by decide +kernel)
theorem cov254_4 : PA.Covered 4 (OZ.Valid 4 w254.low w254.t w254.y w254.r w254.cap) (P33.root 4) :=
  Night6836Tree.sound w254 pick254 4 t565 _ (by decide +kernel)
theorem cov254_5 : PA.Covered 5 (OZ.Valid 5 w254.low w254.t w254.y w254.r w254.cap) (P33.root 5) :=
  Night6836Tree.sound w254 pick254 5 t566 _ (by decide +kernel)
theorem cov254_6 : PA.Covered 6 (OZ.Valid 6 w254.low w254.t w254.y w254.r w254.cap) (P33.root 6) :=
  Night6836Tree.sound w254 pick254 6 t567 _ (by decide +kernel)
theorem cov254_7 : PA.Covered 7 (OZ.Valid 7 w254.low w254.t w254.y w254.r w254.cap) (P33.root 7) :=
  Night6836Tree.sound w254 pick254 7 t2134 _ (by decide +kernel)
theorem window254 : P33.WindowCount w254 := by
  apply P33.window_count w254 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov254_1
  · exact cov254_2
  · exact cov254_3
  · exact cov254_4
  · exact cov254_5
  · exact cov254_6
  · exact cov254_7
def w255 : P33.Window := ⟨13,52,2364,2036,212890365972902067,114796,99000,5000000,81920000000⟩
def h255_0 : Height w255 := ⟨114796,99000,by decide +kernel⟩
def h255_1 : Height w255 := ⟨118711,96000,by decide +kernel⟩
def h255_2 : Height w255 := ⟨122859,93000,by decide +kernel⟩
def h255_3 : Height w255 := ⟨127275,90000,by decide +kernel⟩
def h255_4 : Height w255 := ⟨132001,87000,by decide +kernel⟩
def h255_5 : Height w255 := ⟨137091,84000,by decide +kernel⟩
def h255_6 : Height w255 := ⟨142608,81000,by decide +kernel⟩
def h255_7 : Height w255 := ⟨148633,78000,by decide +kernel⟩
def h255_8 : Height w255 := ⟨155269,75000,by decide +kernel⟩
def h255_9 : Height w255 := ⟨162648,72000,by decide +kernel⟩
def h255_10 : Height w255 := ⟨180381,66000,by decide +kernel⟩
def pick255 (cl : ℕ) : Height w255 := if cl<18 then (if cl<3 then (if cl<2 then (h255_0) else (h255_1)) else (if cl<5 then (h255_2) else (if cl<10 then (h255_3) else (h255_4)))) else (if cl<70 then (if cl<32 then (h255_5) else (if cl<40 then (h255_6) else (h255_7))) else (if cl<120 then (h255_8) else (if cl<312 then (h255_9) else (h255_10))))
private theorem k255_1_0 : check w255 pick255 1 t8364 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k255_1_1 : check w255 pick255 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k255_1_2 : check w255 pick255 1 t8761 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w255 pick255 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t8364 t8748 k255_1_0 k255_1_1
private theorem k255_1_3 : check w255 pick255 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k255_1_4 : check w255 pick255 1 t8338 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k255_1_5 : check w255 pick255 1 t8339 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w255 pick255 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8338 k255_1_3 k255_1_4
private theorem k255_1_6 : check w255 pick255 1 t8762 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w255 pick255 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8761 t8339 k255_1_2 k255_1_5
theorem cov255_1 : PA.Covered 1 (OZ.Valid 1 w255.low w255.t w255.y w255.r w255.cap) (P33.root 1) :=
  Night6836Tree.sound w255 pick255 1 t8762 _ k255_1_6
theorem cov255_2 : PA.Covered 2 (OZ.Valid 2 w255.low w255.t w255.y w255.r w255.cap) (P33.root 2) :=
  Night6836Tree.sound w255 pick255 2 t6618 _ (by decide +kernel)
theorem cov255_3 : PA.Covered 3 (OZ.Valid 3 w255.low w255.t w255.y w255.r w255.cap) (P33.root 3) :=
  Night6836Tree.sound w255 pick255 3 t564 _ (by decide +kernel)
theorem cov255_4 : PA.Covered 4 (OZ.Valid 4 w255.low w255.t w255.y w255.r w255.cap) (P33.root 4) :=
  Night6836Tree.sound w255 pick255 4 t565 _ (by decide +kernel)
theorem cov255_5 : PA.Covered 5 (OZ.Valid 5 w255.low w255.t w255.y w255.r w255.cap) (P33.root 5) :=
  Night6836Tree.sound w255 pick255 5 t566 _ (by decide +kernel)
theorem cov255_6 : PA.Covered 6 (OZ.Valid 6 w255.low w255.t w255.y w255.r w255.cap) (P33.root 6) :=
  Night6836Tree.sound w255 pick255 6 t567 _ (by decide +kernel)
theorem cov255_7 : PA.Covered 7 (OZ.Valid 7 w255.low w255.t w255.y w255.r w255.cap) (P33.root 7) :=
  Night6836Tree.sound w255 pick255 7 t2134 _ (by decide +kernel)
theorem window255 : P33.WindowCount w255 := by
  apply P33.window_count w255 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov255_1
  · exact cov255_2
  · exact cov255_3
  · exact cov255_4
  · exact cov255_5
  · exact cov255_6
  · exact cov255_7
def w256 : P33.Window := ⟨13,53,2035,1695,226709582431281884,144529,117000,5000000,81920000000⟩
def h256_0 : Height w256 := ⟨144529,117000,by decide +kernel⟩
def h256_1 : Height w256 := ⟨148580,114000,by decide +kernel⟩
def h256_2 : Height w256 := ⟨152838,111000,by decide +kernel⟩
def h256_3 : Height w256 := ⟨157326,108000,by decide +kernel⟩
def h256_4 : Height w256 := ⟨162077,105000,by decide +kernel⟩
def h256_5 : Height w256 := ⟨167125,102000,by decide +kernel⟩
def h256_6 : Height w256 := ⟨178294,96000,by decide +kernel⟩
def h256_7 : Height w256 := ⟨184527,93000,by decide +kernel⟩
def h256_8 : Height w256 := ⟨191290,90000,by decide +kernel⟩
def h256_9 : Height w256 := ⟨198675,87000,by decide +kernel⟩
def h256_10 : Height w256 := ⟨215808,81000,by decide +kernel⟩
def h256_11 : Height w256 := ⟨225892,78000,by decide +kernel⟩
def pick256 (cl : ℕ) : Height w256 := if cl<32 then (if cl<5 then (if cl<2 then (h256_0) else (if cl<4 then (h256_1) else (h256_2))) else (if cl<10 then (h256_3) else (if cl<14 then (h256_4) else (h256_5)))) else (if cl<120 then (if cl<44 then (h256_6) else (if cl<83 then (h256_7) else (h256_8))) else (if cl<312 then (h256_9) else (if cl<524 then (h256_10) else (h256_11))))
private theorem k256_1_0 : check w256 pick256 1 t8364 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k256_1_1 : check w256 pick256 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k256_1_2 : check w256 pick256 1 t8761 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w256 pick256 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t8364 t8748 k256_1_0 k256_1_1
private theorem k256_1_3 : check w256 pick256 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k256_1_4 : check w256 pick256 1 t8767 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k256_1_5 : check w256 pick256 1 t8768 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w256 pick256 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8767 k256_1_3 k256_1_4
private theorem k256_1_6 : check w256 pick256 1 t8769 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w256 pick256 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8761 t8768 k256_1_2 k256_1_5
theorem cov256_1 : PA.Covered 1 (OZ.Valid 1 w256.low w256.t w256.y w256.r w256.cap) (P33.root 1) :=
  Night6836Tree.sound w256 pick256 1 t8769 _ k256_1_6
theorem cov256_2 : PA.Covered 2 (OZ.Valid 2 w256.low w256.t w256.y w256.r w256.cap) (P33.root 2) :=
  Night6836Tree.sound w256 pick256 2 t6618 _ (by decide +kernel)
theorem cov256_3 : PA.Covered 3 (OZ.Valid 3 w256.low w256.t w256.y w256.r w256.cap) (P33.root 3) :=
  Night6836Tree.sound w256 pick256 3 t564 _ (by decide +kernel)
theorem cov256_4 : PA.Covered 4 (OZ.Valid 4 w256.low w256.t w256.y w256.r w256.cap) (P33.root 4) :=
  Night6836Tree.sound w256 pick256 4 t565 _ (by decide +kernel)
theorem cov256_5 : PA.Covered 5 (OZ.Valid 5 w256.low w256.t w256.y w256.r w256.cap) (P33.root 5) :=
  Night6836Tree.sound w256 pick256 5 t566 _ (by decide +kernel)
theorem cov256_6 : PA.Covered 6 (OZ.Valid 6 w256.low w256.t w256.y w256.r w256.cap) (P33.root 6) :=
  Night6836Tree.sound w256 pick256 6 t567 _ (by decide +kernel)
theorem cov256_7 : PA.Covered 7 (OZ.Valid 7 w256.low w256.t w256.y w256.r w256.cap) (P33.root 7) :=
  Night6836Tree.sound w256 pick256 7 t2134 _ (by decide +kernel)
theorem window256 : P33.WindowCount w256 := by
  apply P33.window_count w256 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov256_1
  · exact cov256_2
  · exact cov256_3
  · exact cov256_4
  · exact cov256_5
  · exact cov256_6
  · exact cov256_7
def w257 : P33.Window := ⟨13,54,1694,1631,197417206474579842,152792,123000,5000000,81920000000⟩
def h257_0 : Height w257 := ⟨152792,123000,by decide +kernel⟩
def h257_1 : Height w257 := ⟨156801,120000,by decide +kernel⟩
def h257_2 : Height w257 := ⟨161000,117000,by decide +kernel⟩
def h257_3 : Height w257 := ⟨165412,114000,by decide +kernel⟩
def h257_4 : Height w257 := ⟨170063,111000,by decide +kernel⟩
def h257_5 : Height w257 := ⟨174983,108000,by decide +kernel⟩
def h257_6 : Height w257 := ⟨185782,102000,by decide +kernel⟩
def h257_7 : Height w257 := ⟨191754,99000,by decide +kernel⟩
def h257_8 : Height w257 := ⟨198186,96000,by decide +kernel⟩
def h257_9 : Height w257 := ⟨205152,93000,by decide +kernel⟩
def h257_10 : Height w257 := ⟨212744,90000,by decide +kernel⟩
def h257_11 : Height w257 := ⟨230281,84000,by decide +kernel⟩
def h257_12 : Height w257 := ⟨240548,81000,by decide +kernel⟩
def pick257 (cl : ℕ) : Height w257 := if cl<32 then (if cl<5 then (if cl<2 then (h257_0) else (if cl<4 then (h257_1) else (h257_2))) else (if cl<6 then (h257_3) else (if cl<13 then (h257_4) else (h257_5)))) else (if cl<92 then (if cl<37 then (h257_6) else (if cl<55 then (h257_7) else (h257_8))) else (if cl<312 then (if cl<145 then (h257_9) else (h257_10)) else (if cl<615 then (h257_11) else (h257_12))))
private theorem k257_1_0 : check w257 pick257 1 t8364 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k257_1_1 : check w257 pick257 1 t8359 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k257_1_2 : check w257 pick257 1 t8365 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w257 pick257 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t8364 t8359 k257_1_0 k257_1_1
private theorem k257_1_3 : check w257 pick257 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k257_1_4 : check w257 pick257 1 t8767 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k257_1_5 : check w257 pick257 1 t8768 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w257 pick257 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8767 k257_1_3 k257_1_4
private theorem k257_1_6 : check w257 pick257 1 t8770 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w257 pick257 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8365 t8768 k257_1_2 k257_1_5
theorem cov257_1 : PA.Covered 1 (OZ.Valid 1 w257.low w257.t w257.y w257.r w257.cap) (P33.root 1) :=
  Night6836Tree.sound w257 pick257 1 t8770 _ k257_1_6
theorem cov257_2 : PA.Covered 2 (OZ.Valid 2 w257.low w257.t w257.y w257.r w257.cap) (P33.root 2) :=
  Night6836Tree.sound w257 pick257 2 t6666 _ (by decide +kernel)
theorem cov257_3 : PA.Covered 3 (OZ.Valid 3 w257.low w257.t w257.y w257.r w257.cap) (P33.root 3) :=
  Night6836Tree.sound w257 pick257 3 t564 _ (by decide +kernel)
theorem cov257_4 : PA.Covered 4 (OZ.Valid 4 w257.low w257.t w257.y w257.r w257.cap) (P33.root 4) :=
  Night6836Tree.sound w257 pick257 4 t565 _ (by decide +kernel)
theorem cov257_5 : PA.Covered 5 (OZ.Valid 5 w257.low w257.t w257.y w257.r w257.cap) (P33.root 5) :=
  Night6836Tree.sound w257 pick257 5 t566 _ (by decide +kernel)
theorem cov257_6 : PA.Covered 6 (OZ.Valid 6 w257.low w257.t w257.y w257.r w257.cap) (P33.root 6) :=
  Night6836Tree.sound w257 pick257 6 t567 _ (by decide +kernel)
theorem cov257_7 : PA.Covered 7 (OZ.Valid 7 w257.low w257.t w257.y w257.r w257.cap) (P33.root 7) :=
  Night6836Tree.sound w257 pick257 7 t2134 _ (by decide +kernel)
theorem window257 : P33.WindowCount w257 := by
  apply P33.window_count w257 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov257_1
  · exact cov257_2
  · exact cov257_3
  · exact cov257_4
  · exact cov257_5
  · exact cov257_6
  · exact cov257_7
def w258 : P33.Window := ⟨14,18,7217,6218,203782093254746623,5823,23000,5000000,81920000000⟩
def h258_0 : Height w258 := ⟨5823,23000,by decide +kernel⟩
def h258_1 : Height w258 := ⟨12186,19000,by decide +kernel⟩
def h258_2 : Height w258 := ⟨27723,15000,by decide +kernel⟩
def pick258 (cl : ℕ) : Height w258 := if cl<8 then (h258_0) else (if cl<922 then (h258_1) else (h258_2))
private theorem k258_1_0 : check w258 pick258 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k258_1_1 : check w258 pick258 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k258_1_2 : check w258 pick258 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w258 pick258 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k258_1_0 k258_1_1
private theorem k258_1_3 : check w258 pick258 1 t6748 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k258_1_4 : check w258 pick258 1 t6792 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k258_1_5 : check w258 pick258 1 t6793 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w258 pick258 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t6748 t6792 k258_1_3 k258_1_4
private theorem k258_1_6 : check w258 pick258 1 t6794 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w258 pick258 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t6793 k258_1_2 k258_1_5
private theorem k258_1_7 : check w258 pick258 1 t6841 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k258_1_8 : check w258 pick258 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k258_1_9 : check w258 pick258 1 t6873 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w258 pick258 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t6841 t6872 k258_1_7 k258_1_8
private theorem k258_1_10 : check w258 pick258 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k258_1_11 : check w258 pick258 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k258_1_12 : check w258 pick258 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w258 pick258 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k258_1_10 k258_1_11
private theorem k258_1_13 : check w258 pick258 1 t8771 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w258 pick258 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t6873 t7190 k258_1_9 k258_1_12
private theorem k258_1_14 : check w258 pick258 1 t8772 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w258 pick258 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t6794 t8771 k258_1_6 k258_1_13
theorem cov258_1 : PA.Covered 1 (OZ.Valid 1 w258.low w258.t w258.y w258.r w258.cap) (P33.root 1) :=
  Night6836Tree.sound w258 pick258 1 t8772 _ k258_1_14
private theorem k258_2_0 : check w258 pick258 2 t8783 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k258_2_1 : check w258 pick258 2 t8803 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k258_2_2 : check w258 pick258 2 t8804 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w258 pick258 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t8783 t8803 k258_2_0 k258_2_1
theorem cov258_2 : PA.Covered 2 (OZ.Valid 2 w258.low w258.t w258.y w258.r w258.cap) (P33.root 2) :=
  Night6836Tree.sound w258 pick258 2 t8804 _ k258_2_2
theorem cov258_3 : PA.Covered 3 (OZ.Valid 3 w258.low w258.t w258.y w258.r w258.cap) (P33.root 3) :=
  Night6836Tree.sound w258 pick258 3 t564 _ (by decide +kernel)
theorem cov258_4 : PA.Covered 4 (OZ.Valid 4 w258.low w258.t w258.y w258.r w258.cap) (P33.root 4) :=
  Night6836Tree.sound w258 pick258 4 t565 _ (by decide +kernel)
theorem cov258_5 : PA.Covered 5 (OZ.Valid 5 w258.low w258.t w258.y w258.r w258.cap) (P33.root 5) :=
  Night6836Tree.sound w258 pick258 5 t566 _ (by decide +kernel)
theorem cov258_6 : PA.Covered 6 (OZ.Valid 6 w258.low w258.t w258.y w258.r w258.cap) (P33.root 6) :=
  Night6836Tree.sound w258 pick258 6 t567 _ (by decide +kernel)
theorem cov258_7 : PA.Covered 7 (OZ.Valid 7 w258.low w258.t w258.y w258.r w258.cap) (P33.root 7) :=
  Night6836Tree.sound w258 pick258 7 t568 _ (by decide +kernel)
theorem window258 : P33.WindowCount w258 := by
  apply P33.window_count w258 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov258_1
  · exact cov258_2
  · exact cov258_3
  · exact cov258_4
  · exact cov258_5
  · exact cov258_6
  · exact cov258_7
def w259 : P33.Window := ⟨14,19,7153,7108,244447997590448250,5394,21000,5000000,81920000000⟩
def h259_0 : Height w259 := ⟨5394,21000,by decide +kernel⟩
def h259_1 : Height w259 := ⟨9628,18000,by decide +kernel⟩
def h259_2 : Height w259 := ⟨17022,15000,by decide +kernel⟩
def pick259 (cl : ℕ) : Height w259 := if cl<4 then (h259_0) else (if cl<120 then (h259_1) else (h259_2))
private theorem k259_1_0 : check w259 pick259 1 t8810 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k259_1_1 : check w259 pick259 1 t8815 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k259_1_2 : check w259 pick259 1 t8816 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w259 pick259 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8810 t8815 k259_1_0 k259_1_1
private theorem k259_1_3 : check w259 pick259 1 t8821 ⟨1,7,2,16,1,52,139,192⟩ = true := by decide +kernel
private theorem k259_1_4 : check w259 pick259 1 t8824 ⟨1,7,2,16,1,52,193,450⟩ = true := by decide +kernel
private theorem k259_1_5 : check w259 pick259 1 t8825 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w259 pick259 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t8821 t8824 k259_1_3 k259_1_4
private theorem k259_1_6 : check w259 pick259 1 t8826 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w259 pick259 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8816 t8825 k259_1_2 k259_1_5
theorem cov259_1 : PA.Covered 1 (OZ.Valid 1 w259.low w259.t w259.y w259.r w259.cap) (P33.root 1) :=
  Night6836Tree.sound w259 pick259 1 t8826 _ k259_1_6
theorem cov259_2 : PA.Covered 2 (OZ.Valid 2 w259.low w259.t w259.y w259.r w259.cap) (P33.root 2) :=
  Night6836Tree.sound w259 pick259 2 t8398 _ (by decide +kernel)
theorem cov259_3 : PA.Covered 3 (OZ.Valid 3 w259.low w259.t w259.y w259.r w259.cap) (P33.root 3) :=
  Night6836Tree.sound w259 pick259 3 t564 _ (by decide +kernel)
theorem cov259_4 : PA.Covered 4 (OZ.Valid 4 w259.low w259.t w259.y w259.r w259.cap) (P33.root 4) :=
  Night6836Tree.sound w259 pick259 4 t565 _ (by decide +kernel)
theorem cov259_5 : PA.Covered 5 (OZ.Valid 5 w259.low w259.t w259.y w259.r w259.cap) (P33.root 5) :=
  Night6836Tree.sound w259 pick259 5 t566 _ (by decide +kernel)
theorem cov259_6 : PA.Covered 6 (OZ.Valid 6 w259.low w259.t w259.y w259.r w259.cap) (P33.root 6) :=
  Night6836Tree.sound w259 pick259 6 t567 _ (by decide +kernel)
theorem cov259_7 : PA.Covered 7 (OZ.Valid 7 w259.low w259.t w259.y w259.r w259.cap) (P33.root 7) :=
  Night6836Tree.sound w259 pick259 7 t568 _ (by decide +kernel)
theorem window259 : P33.WindowCount w259 := by
  apply P33.window_count w259 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov259_1
  · exact cov259_2
  · exact cov259_3
  · exact cov259_4
  · exact cov259_5
  · exact cov259_6
  · exact cov259_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w260 : P33.Window := ⟨14,20,7107,7061,244404843815419465,6934,21000,5000000,81920000000⟩
def h260_0 : Height w260 := ⟨6934,21000,by decide +kernel⟩
def h260_1 : Height w260 := ⟨11476,18000,by decide +kernel⟩
def h260_2 : Height w260 := ⟨19574,15000,by decide +kernel⟩
def pick260 (cl : ℕ) : Height w260 := if cl<6 then (h260_0) else (if cl<203 then (h260_1) else (h260_2))
private theorem k260_1_0 : check w260 pick260 1 t8828 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k260_1_1 : check w260 pick260 1 t8837 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k260_1_2 : check w260 pick260 1 t8838 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w260 pick260 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t8828 t8837 k260_1_0 k260_1_1
private theorem k260_1_3 : check w260 pick260 1 t8848 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k260_1_4 : check w260 pick260 1 t8814 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k260_1_5 : check w260 pick260 1 t8849 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w260 pick260 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t8848 t8814 k260_1_3 k260_1_4
private theorem k260_1_6 : check w260 pick260 1 t8850 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w260 pick260 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t8838 t8849 k260_1_2 k260_1_5
private theorem k260_1_7 : check w260 pick260 1 t8855 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k260_1_8 : check w260 pick260 1 t8864 ⟨1,7,2,16,1,52,173,206⟩ = true := by decide +kernel
private theorem k260_1_9 : check w260 pick260 1 t8865 ⟨1,7,2,16,1,52,139,206⟩ = true := glue w260 pick260 1 ⟨1,7,2,16,1,52,139,206⟩ 3 172 t8855 t8864 k260_1_7 k260_1_8
private theorem k260_1_10 : check w260 pick260 1 t8867 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k260_1_11 : check w260 pick260 1 t8455 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k260_1_12 : check w260 pick260 1 t8868 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w260 pick260 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t8867 t8455 k260_1_10 k260_1_11
private theorem k260_1_13 : check w260 pick260 1 t8869 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w260 pick260 1 ⟨1,7,2,16,1,52,139,450⟩ 3 206 t8865 t8868 k260_1_9 k260_1_12
private theorem k260_1_14 : check w260 pick260 1 t8870 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w260 pick260 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8850 t8869 k260_1_6 k260_1_13
theorem cov260_1 : PA.Covered 1 (OZ.Valid 1 w260.low w260.t w260.y w260.r w260.cap) (P33.root 1) :=
  Night6836Tree.sound w260 pick260 1 t8870 _ k260_1_14
theorem cov260_2 : PA.Covered 2 (OZ.Valid 2 w260.low w260.t w260.y w260.r w260.cap) (P33.root 2) :=
  Night6836Tree.sound w260 pick260 2 t8873 _ (by decide +kernel)
theorem cov260_3 : PA.Covered 3 (OZ.Valid 3 w260.low w260.t w260.y w260.r w260.cap) (P33.root 3) :=
  Night6836Tree.sound w260 pick260 3 t564 _ (by decide +kernel)
theorem cov260_4 : PA.Covered 4 (OZ.Valid 4 w260.low w260.t w260.y w260.r w260.cap) (P33.root 4) :=
  Night6836Tree.sound w260 pick260 4 t565 _ (by decide +kernel)
theorem cov260_5 : PA.Covered 5 (OZ.Valid 5 w260.low w260.t w260.y w260.r w260.cap) (P33.root 5) :=
  Night6836Tree.sound w260 pick260 5 t566 _ (by decide +kernel)
theorem cov260_6 : PA.Covered 6 (OZ.Valid 6 w260.low w260.t w260.y w260.r w260.cap) (P33.root 6) :=
  Night6836Tree.sound w260 pick260 6 t567 _ (by decide +kernel)
theorem cov260_7 : PA.Covered 7 (OZ.Valid 7 w260.low w260.t w260.y w260.r w260.cap) (P33.root 7) :=
  Night6836Tree.sound w260 pick260 7 t568 _ (by decide +kernel)
theorem window260 : P33.WindowCount w260 := by
  apply P33.window_count w260 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov260_1
  · exact cov260_2
  · exact cov260_3
  · exact cov260_4
  · exact cov260_5
  · exact cov260_6
  · exact cov260_7
def w261 : P33.Window := ⟨14,21,7060,6644,238520186305466417,10633,21000,5000000,81920000000⟩
def h261_0 : Height w261 := ⟨10633,21000,by decide +kernel⟩
def h261_1 : Height w261 := ⟨16370,18000,by decide +kernel⟩
def h261_2 : Height w261 := ⟨27721,15000,by decide +kernel⟩
def pick261 (cl : ℕ) : Height w261 := if cl<32 then (h261_0) else (if cl<853 then (h261_1) else (h261_2))
private theorem k261_1_0 : check w261 pick261 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k261_1_1 : check w261 pick261 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k261_1_2 : check w261 pick261 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w261 pick261 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k261_1_0 k261_1_1
private theorem k261_1_3 : check w261 pick261 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k261_1_4 : check w261 pick261 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k261_1_5 : check w261 pick261 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w261 pick261 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k261_1_3 k261_1_4
private theorem k261_1_6 : check w261 pick261 1 t7382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w261 pick261 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7381 k261_1_2 k261_1_5
private theorem k261_1_7 : check w261 pick261 1 t7356 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k261_1_8 : check w261 pick261 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k261_1_9 : check w261 pick261 1 t7363 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w261 pick261 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7356 t7362 k261_1_7 k261_1_8
private theorem k261_1_10 : check w261 pick261 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k261_1_11 : check w261 pick261 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k261_1_12 : check w261 pick261 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w261 pick261 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k261_1_10 k261_1_11
private theorem k261_1_13 : check w261 pick261 1 t7370 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w261 pick261 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7363 t7369 k261_1_9 k261_1_12
private theorem k261_1_14 : check w261 pick261 1 t8459 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w261 pick261 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7382 t7370 k261_1_6 k261_1_13
theorem cov261_1 : PA.Covered 1 (OZ.Valid 1 w261.low w261.t w261.y w261.r w261.cap) (P33.root 1) :=
  Night6836Tree.sound w261 pick261 1 t8459 _ k261_1_14
theorem cov261_2 : PA.Covered 2 (OZ.Valid 2 w261.low w261.t w261.y w261.r w261.cap) (P33.root 2) :=
  Night6836Tree.sound w261 pick261 2 t7377 _ (by decide +kernel)
theorem cov261_3 : PA.Covered 3 (OZ.Valid 3 w261.low w261.t w261.y w261.r w261.cap) (P33.root 3) :=
  Night6836Tree.sound w261 pick261 3 t564 _ (by decide +kernel)
theorem cov261_4 : PA.Covered 4 (OZ.Valid 4 w261.low w261.t w261.y w261.r w261.cap) (P33.root 4) :=
  Night6836Tree.sound w261 pick261 4 t565 _ (by decide +kernel)
theorem cov261_5 : PA.Covered 5 (OZ.Valid 5 w261.low w261.t w261.y w261.r w261.cap) (P33.root 5) :=
  Night6836Tree.sound w261 pick261 5 t566 _ (by decide +kernel)
theorem cov261_6 : PA.Covered 6 (OZ.Valid 6 w261.low w261.t w261.y w261.r w261.cap) (P33.root 6) :=
  Night6836Tree.sound w261 pick261 6 t567 _ (by decide +kernel)
theorem cov261_7 : PA.Covered 7 (OZ.Valid 7 w261.low w261.t w261.y w261.r w261.cap) (P33.root 7) :=
  Night6836Tree.sound w261 pick261 7 t568 _ (by decide +kernel)
theorem window261 : P33.WindowCount w261 := by
  apply P33.window_count w261 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov261_1
  · exact cov261_2
  · exact cov261_3
  · exact cov261_4
  · exact cov261_5
  · exact cov261_6
  · exact cov261_7
def w262 : P33.Window := ⟨14,22,7013,6807,242554992608182503,11080,21000,5000000,81920000000⟩
def h262_0 : Height w262 := ⟨11080,21000,by decide +kernel⟩
def h262_1 : Height w262 := ⟨16666,18000,by decide +kernel⟩
def h262_2 : Height w262 := ⟨27379,15000,by decide +kernel⟩
def pick262 (cl : ℕ) : Height w262 := if cl<32 then (h262_0) else (if cl<853 then (h262_1) else (h262_2))
private theorem k262_1_0 : check w262 pick262 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k262_1_1 : check w262 pick262 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k262_1_2 : check w262 pick262 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w262 pick262 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k262_1_0 k262_1_1
private theorem k262_1_3 : check w262 pick262 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k262_1_4 : check w262 pick262 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k262_1_5 : check w262 pick262 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w262 pick262 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k262_1_3 k262_1_4
private theorem k262_1_6 : check w262 pick262 1 t7382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w262 pick262 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7381 k262_1_2 k262_1_5
private theorem k262_1_7 : check w262 pick262 1 t7356 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k262_1_8 : check w262 pick262 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k262_1_9 : check w262 pick262 1 t7363 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w262 pick262 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7356 t7362 k262_1_7 k262_1_8
private theorem k262_1_10 : check w262 pick262 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k262_1_11 : check w262 pick262 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k262_1_12 : check w262 pick262 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w262 pick262 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k262_1_10 k262_1_11
private theorem k262_1_13 : check w262 pick262 1 t7370 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w262 pick262 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7363 t7369 k262_1_9 k262_1_12
private theorem k262_1_14 : check w262 pick262 1 t8459 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w262 pick262 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7382 t7370 k262_1_6 k262_1_13
theorem cov262_1 : PA.Covered 1 (OZ.Valid 1 w262.low w262.t w262.y w262.r w262.cap) (P33.root 1) :=
  Night6836Tree.sound w262 pick262 1 t8459 _ k262_1_14
theorem cov262_2 : PA.Covered 2 (OZ.Valid 2 w262.low w262.t w262.y w262.r w262.cap) (P33.root 2) :=
  Night6836Tree.sound w262 pick262 2 t7377 _ (by decide +kernel)
theorem cov262_3 : PA.Covered 3 (OZ.Valid 3 w262.low w262.t w262.y w262.r w262.cap) (P33.root 3) :=
  Night6836Tree.sound w262 pick262 3 t564 _ (by decide +kernel)
theorem cov262_4 : PA.Covered 4 (OZ.Valid 4 w262.low w262.t w262.y w262.r w262.cap) (P33.root 4) :=
  Night6836Tree.sound w262 pick262 4 t565 _ (by decide +kernel)
theorem cov262_5 : PA.Covered 5 (OZ.Valid 5 w262.low w262.t w262.y w262.r w262.cap) (P33.root 5) :=
  Night6836Tree.sound w262 pick262 5 t566 _ (by decide +kernel)
theorem cov262_6 : PA.Covered 6 (OZ.Valid 6 w262.low w262.t w262.y w262.r w262.cap) (P33.root 6) :=
  Night6836Tree.sound w262 pick262 6 t567 _ (by decide +kernel)
theorem cov262_7 : PA.Covered 7 (OZ.Valid 7 w262.low w262.t w262.y w262.r w262.cap) (P33.root 7) :=
  Night6836Tree.sound w262 pick262 7 t568 _ (by decide +kernel)
theorem window262 : P33.WindowCount w262 := by
  apply P33.window_count w262 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov262_1
  · exact cov262_2
  · exact cov262_3
  · exact cov262_4
  · exact cov262_5
  · exact cov262_6
  · exact cov262_7
def w263 : P33.Window := ⟨14,23,6965,6918,240146758974544262,11805,21000,5000000,81920000000⟩
def h263_0 : Height w263 := ⟨11805,21000,by decide +kernel⟩
def h263_1 : Height w263 := ⟨17373,18000,by decide +kernel⟩
def h263_2 : Height w263 := ⟨27875,15000,by decide +kernel⟩
def pick263 (cl : ℕ) : Height w263 := if cl<32 then (h263_0) else (if cl<685 then (h263_1) else (h263_2))
private theorem k263_1_0 : check w263 pick263 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k263_1_1 : check w263 pick263 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k263_1_2 : check w263 pick263 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w263 pick263 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k263_1_0 k263_1_1
private theorem k263_1_3 : check w263 pick263 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k263_1_4 : check w263 pick263 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k263_1_5 : check w263 pick263 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w263 pick263 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k263_1_3 k263_1_4
private theorem k263_1_6 : check w263 pick263 1 t7382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w263 pick263 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7381 k263_1_2 k263_1_5
private theorem k263_1_7 : check w263 pick263 1 t7356 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k263_1_8 : check w263 pick263 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k263_1_9 : check w263 pick263 1 t7363 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w263 pick263 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7356 t7362 k263_1_7 k263_1_8
private theorem k263_1_10 : check w263 pick263 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k263_1_11 : check w263 pick263 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k263_1_12 : check w263 pick263 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w263 pick263 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k263_1_10 k263_1_11
private theorem k263_1_13 : check w263 pick263 1 t7370 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w263 pick263 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7363 t7369 k263_1_9 k263_1_12
private theorem k263_1_14 : check w263 pick263 1 t8459 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w263 pick263 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7382 t7370 k263_1_6 k263_1_13
theorem cov263_1 : PA.Covered 1 (OZ.Valid 1 w263.low w263.t w263.y w263.r w263.cap) (P33.root 1) :=
  Night6836Tree.sound w263 pick263 1 t8459 _ k263_1_14
private theorem k263_2_0 : check w263 pick263 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k263_2_1 : check w263 pick263 2 t8875 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k263_2_2 : check w263 pick263 2 t8876 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w263 pick263 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t8875 k263_2_0 k263_2_1
theorem cov263_2 : PA.Covered 2 (OZ.Valid 2 w263.low w263.t w263.y w263.r w263.cap) (P33.root 2) :=
  Night6836Tree.sound w263 pick263 2 t8876 _ k263_2_2
theorem cov263_3 : PA.Covered 3 (OZ.Valid 3 w263.low w263.t w263.y w263.r w263.cap) (P33.root 3) :=
  Night6836Tree.sound w263 pick263 3 t564 _ (by decide +kernel)
theorem cov263_4 : PA.Covered 4 (OZ.Valid 4 w263.low w263.t w263.y w263.r w263.cap) (P33.root 4) :=
  Night6836Tree.sound w263 pick263 4 t565 _ (by decide +kernel)
theorem cov263_5 : PA.Covered 5 (OZ.Valid 5 w263.low w263.t w263.y w263.r w263.cap) (P33.root 5) :=
  Night6836Tree.sound w263 pick263 5 t566 _ (by decide +kernel)
theorem cov263_6 : PA.Covered 6 (OZ.Valid 6 w263.low w263.t w263.y w263.r w263.cap) (P33.root 6) :=
  Night6836Tree.sound w263 pick263 6 t567 _ (by decide +kernel)
theorem cov263_7 : PA.Covered 7 (OZ.Valid 7 w263.low w263.t w263.y w263.r w263.cap) (P33.root 7) :=
  Night6836Tree.sound w263 pick263 7 t568 _ (by decide +kernel)
theorem window263 : P33.WindowCount w263 := by
  apply P33.window_count w263 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov263_1
  · exact cov263_2
  · exact cov263_3
  · exact cov263_4
  · exact cov263_5
  · exact cov263_6
  · exact cov263_7
def w264 : P33.Window := ⟨14,24,5023,4024,201191540264089430,18604,39000,5000000,81920000000⟩
def h264_0 : Height w264 := ⟨18604,39000,by decide +kernel⟩
def h264_1 : Height w264 := ⟨24438,35000,by decide +kernel⟩
def h264_2 : Height w264 := ⟨32499,31000,by decide +kernel⟩
def h264_3 : Height w264 := ⟨45508,27000,by decide +kernel⟩
def pick264 (cl : ℕ) : Height w264 := if cl<40 then (if cl<5 then (h264_0) else (h264_1)) else (if cl<388 then (h264_2) else (h264_3))
private theorem k264_1_0 : check w264 pick264 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k264_1_1 : check w264 pick264 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k264_1_2 : check w264 pick264 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w264 pick264 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k264_1_0 k264_1_1
private theorem k264_1_3 : check w264 pick264 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k264_1_4 : check w264 pick264 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k264_1_5 : check w264 pick264 1 t7219 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w264 pick264 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t7097 k264_1_3 k264_1_4
private theorem k264_1_6 : check w264 pick264 1 t8460 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w264 pick264 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t7219 k264_1_2 k264_1_5
theorem cov264_1 : PA.Covered 1 (OZ.Valid 1 w264.low w264.t w264.y w264.r w264.cap) (P33.root 1) :=
  Night6836Tree.sound w264 pick264 1 t8460 _ k264_1_6
theorem cov264_2 : PA.Covered 2 (OZ.Valid 2 w264.low w264.t w264.y w264.r w264.cap) (P33.root 2) :=
  Night6836Tree.sound w264 pick264 2 t5320 _ (by decide +kernel)
theorem cov264_3 : PA.Covered 3 (OZ.Valid 3 w264.low w264.t w264.y w264.r w264.cap) (P33.root 3) :=
  Night6836Tree.sound w264 pick264 3 t564 _ (by decide +kernel)
theorem cov264_4 : PA.Covered 4 (OZ.Valid 4 w264.low w264.t w264.y w264.r w264.cap) (P33.root 4) :=
  Night6836Tree.sound w264 pick264 4 t565 _ (by decide +kernel)
theorem cov264_5 : PA.Covered 5 (OZ.Valid 5 w264.low w264.t w264.y w264.r w264.cap) (P33.root 5) :=
  Night6836Tree.sound w264 pick264 5 t566 _ (by decide +kernel)
theorem cov264_6 : PA.Covered 6 (OZ.Valid 6 w264.low w264.t w264.y w264.r w264.cap) (P33.root 6) :=
  Night6836Tree.sound w264 pick264 6 t567 _ (by decide +kernel)
theorem cov264_7 : PA.Covered 7 (OZ.Valid 7 w264.low w264.t w264.y w264.r w264.cap) (P33.root 7) :=
  Night6836Tree.sound w264 pick264 7 t2134 _ (by decide +kernel)
theorem window264 : P33.WindowCount w264 := by
  apply P33.window_count w264 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov264_1
  · exact cov264_2
  · exact cov264_3
  · exact cov264_4
  · exact cov264_5
  · exact cov264_6
  · exact cov264_7
def w265 : P33.Window := ⟨14,24,6917,6863,243490547527538317,9533,24000,5000000,81920000000⟩
def h265_0 : Height w265 := ⟨9533,24000,by decide +kernel⟩
def h265_1 : Height w265 := ⟨13565,21000,by decide +kernel⟩
def h265_2 : Height w265 := ⟨19531,18000,by decide +kernel⟩
def h265_3 : Height w265 := ⟨30998,15000,by decide +kernel⟩
def pick265 (cl : ℕ) : Height w265 := if cl<37 then (if cl<2 then (h265_0) else (h265_1)) else (if cl<922 then (h265_2) else (h265_3))
private theorem k265_1_0 : check w265 pick265 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k265_1_1 : check w265 pick265 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k265_1_2 : check w265 pick265 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w265 pick265 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k265_1_0 k265_1_1
private theorem k265_1_3 : check w265 pick265 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k265_1_4 : check w265 pick265 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k265_1_5 : check w265 pick265 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w265 pick265 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k265_1_3 k265_1_4
private theorem k265_1_6 : check w265 pick265 1 t7382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w265 pick265 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7381 k265_1_2 k265_1_5
private theorem k265_1_7 : check w265 pick265 1 t7356 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k265_1_8 : check w265 pick265 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k265_1_9 : check w265 pick265 1 t7363 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w265 pick265 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7356 t7362 k265_1_7 k265_1_8
private theorem k265_1_10 : check w265 pick265 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k265_1_11 : check w265 pick265 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k265_1_12 : check w265 pick265 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w265 pick265 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k265_1_10 k265_1_11
private theorem k265_1_13 : check w265 pick265 1 t7370 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w265 pick265 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7363 t7369 k265_1_9 k265_1_12
private theorem k265_1_14 : check w265 pick265 1 t8459 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w265 pick265 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7382 t7370 k265_1_6 k265_1_13
theorem cov265_1 : PA.Covered 1 (OZ.Valid 1 w265.low w265.t w265.y w265.r w265.cap) (P33.root 1) :=
  Night6836Tree.sound w265 pick265 1 t8459 _ k265_1_14
private theorem k265_2_0 : check w265 pick265 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k265_2_1 : check w265 pick265 2 t8875 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k265_2_2 : check w265 pick265 2 t8876 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w265 pick265 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t8875 k265_2_0 k265_2_1
theorem cov265_2 : PA.Covered 2 (OZ.Valid 2 w265.low w265.t w265.y w265.r w265.cap) (P33.root 2) :=
  Night6836Tree.sound w265 pick265 2 t8876 _ k265_2_2
theorem cov265_3 : PA.Covered 3 (OZ.Valid 3 w265.low w265.t w265.y w265.r w265.cap) (P33.root 3) :=
  Night6836Tree.sound w265 pick265 3 t564 _ (by decide +kernel)
theorem cov265_4 : PA.Covered 4 (OZ.Valid 4 w265.low w265.t w265.y w265.r w265.cap) (P33.root 4) :=
  Night6836Tree.sound w265 pick265 4 t565 _ (by decide +kernel)
theorem cov265_5 : PA.Covered 5 (OZ.Valid 5 w265.low w265.t w265.y w265.r w265.cap) (P33.root 5) :=
  Night6836Tree.sound w265 pick265 5 t566 _ (by decide +kernel)
theorem cov265_6 : PA.Covered 6 (OZ.Valid 6 w265.low w265.t w265.y w265.r w265.cap) (P33.root 6) :=
  Night6836Tree.sound w265 pick265 6 t567 _ (by decide +kernel)
theorem cov265_7 : PA.Covered 7 (OZ.Valid 7 w265.low w265.t w265.y w265.r w265.cap) (P33.root 7) :=
  Night6836Tree.sound w265 pick265 7 t568 _ (by decide +kernel)
theorem window265 : P33.WindowCount w265 := by
  apply P33.window_count w265 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov265_1
  · exact cov265_2
  · exact cov265_3
  · exact cov265_4
  · exact cov265_5
  · exact cov265_6
  · exact cov265_7
def w266 : P33.Window := ⟨14,25,6862,6807,245262585150900267,11126,24000,5000000,81920000000⟩
def h266_0 : Height w266 := ⟨11126,24000,by decide +kernel⟩
def h266_1 : Height w266 := ⟨15387,21000,by decide +kernel⟩
def h266_2 : Height w266 := ⟨21780,18000,by decide +kernel⟩
def h266_3 : Height w266 := ⟨34294,15000,by decide +kernel⟩
def pick266 (cl : ℕ) : Height w266 := if cl<51 then (if cl<4 then (h266_0) else (h266_1)) else (if cl<961 then (h266_2) else (h266_3))
private theorem k266_1_0 : check w266 pick266 1 t7124 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k266_1_1 : check w266 pick266 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k266_1_2 : check w266 pick266 1 t7132 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w266 pick266 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7124 t7131 k266_1_0 k266_1_1
private theorem k266_1_3 : check w266 pick266 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k266_1_4 : check w266 pick266 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k266_1_5 : check w266 pick266 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w266 pick266 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k266_1_3 k266_1_4
private theorem k266_1_6 : check w266 pick266 1 t7455 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w266 pick266 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7132 t7381 k266_1_2 k266_1_5
private theorem k266_1_7 : check w266 pick266 1 t7386 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k266_1_8 : check w266 pick266 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k266_1_9 : check w266 pick266 1 t7387 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w266 pick266 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7386 t7362 k266_1_7 k266_1_8
private theorem k266_1_10 : check w266 pick266 1 t8878 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k266_1_11 : check w266 pick266 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k266_1_12 : check w266 pick266 1 t8879 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w266 pick266 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t8878 t7318 k266_1_10 k266_1_11
private theorem k266_1_13 : check w266 pick266 1 t8880 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w266 pick266 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7387 t8879 k266_1_9 k266_1_12
private theorem k266_1_14 : check w266 pick266 1 t8881 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w266 pick266 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7455 t8880 k266_1_6 k266_1_13
theorem cov266_1 : PA.Covered 1 (OZ.Valid 1 w266.low w266.t w266.y w266.r w266.cap) (P33.root 1) :=
  Night6836Tree.sound w266 pick266 1 t8881 _ k266_1_14
private theorem k266_2_0 : check w266 pick266 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k266_2_1 : check w266 pick266 2 t8883 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k266_2_2 : check w266 pick266 2 t8884 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w266 pick266 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t8883 k266_2_0 k266_2_1
theorem cov266_2 : PA.Covered 2 (OZ.Valid 2 w266.low w266.t w266.y w266.r w266.cap) (P33.root 2) :=
  Night6836Tree.sound w266 pick266 2 t8884 _ k266_2_2
theorem cov266_3 : PA.Covered 3 (OZ.Valid 3 w266.low w266.t w266.y w266.r w266.cap) (P33.root 3) :=
  Night6836Tree.sound w266 pick266 3 t564 _ (by decide +kernel)
theorem cov266_4 : PA.Covered 4 (OZ.Valid 4 w266.low w266.t w266.y w266.r w266.cap) (P33.root 4) :=
  Night6836Tree.sound w266 pick266 4 t565 _ (by decide +kernel)
theorem cov266_5 : PA.Covered 5 (OZ.Valid 5 w266.low w266.t w266.y w266.r w266.cap) (P33.root 5) :=
  Night6836Tree.sound w266 pick266 5 t566 _ (by decide +kernel)
theorem cov266_6 : PA.Covered 6 (OZ.Valid 6 w266.low w266.t w266.y w266.r w266.cap) (P33.root 6) :=
  Night6836Tree.sound w266 pick266 6 t567 _ (by decide +kernel)
theorem cov266_7 : PA.Covered 7 (OZ.Valid 7 w266.low w266.t w266.y w266.r w266.cap) (P33.root 7) :=
  Night6836Tree.sound w266 pick266 7 t568 _ (by decide +kernel)
theorem window266 : P33.WindowCount w266 := by
  apply P33.window_count w266 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov266_1
  · exact cov266_2
  · exact cov266_3
  · exact cov266_4
  · exact cov266_5
  · exact cov266_6
  · exact cov266_7
def w267 : P33.Window := ⟨14,27,6746,6644,245679998404701636,14813,24000,5000000,81920000000⟩
def h267_0 : Height w267 := ⟨14813,24000,by decide +kernel⟩
def h267_1 : Height w267 := ⟨19667,21000,by decide +kernel⟩
def h267_2 : Height w267 := ⟨27193,18000,by decide +kernel⟩
def h267_3 : Height w267 := ⟨42645,15000,by decide +kernel⟩
def pick267 (cl : ℕ) : Height w267 := if cl<135 then (if cl<12 then (h267_0) else (h267_1)) else (if cl<1013 then (h267_2) else (h267_3))
private theorem k267_1_0 : check w267 pick267 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k267_1_1 : check w267 pick267 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k267_1_2 : check w267 pick267 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w267 pick267 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k267_1_0 k267_1_1
private theorem k267_1_3 : check w267 pick267 1 t8472 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k267_1_4 : check w267 pick267 1 t6792 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k267_1_5 : check w267 pick267 1 t8473 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w267 pick267 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t8472 t6792 k267_1_3 k267_1_4
private theorem k267_1_6 : check w267 pick267 1 t8474 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w267 pick267 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t8473 k267_1_2 k267_1_5
private theorem k267_1_7 : check w267 pick267 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k267_1_8 : check w267 pick267 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k267_1_9 : check w267 pick267 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w267 pick267 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k267_1_7 k267_1_8
private theorem k267_1_10 : check w267 pick267 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k267_1_11 : check w267 pick267 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k267_1_12 : check w267 pick267 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w267 pick267 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k267_1_10 k267_1_11
private theorem k267_1_13 : check w267 pick267 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w267 pick267 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k267_1_9 k267_1_12
private theorem k267_1_14 : check w267 pick267 1 t8475 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w267 pick267 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8474 t7519 k267_1_6 k267_1_13
theorem cov267_1 : PA.Covered 1 (OZ.Valid 1 w267.low w267.t w267.y w267.r w267.cap) (P33.root 1) :=
  Night6836Tree.sound w267 pick267 1 t8475 _ k267_1_14
private theorem k267_2_0 : check w267 pick267 2 t7548 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k267_2_1 : check w267 pick267 2 t8886 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k267_2_2 : check w267 pick267 2 t8887 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w267 pick267 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7548 t8886 k267_2_0 k267_2_1
theorem cov267_2 : PA.Covered 2 (OZ.Valid 2 w267.low w267.t w267.y w267.r w267.cap) (P33.root 2) :=
  Night6836Tree.sound w267 pick267 2 t8887 _ k267_2_2
theorem cov267_3 : PA.Covered 3 (OZ.Valid 3 w267.low w267.t w267.y w267.r w267.cap) (P33.root 3) :=
  Night6836Tree.sound w267 pick267 3 t564 _ (by decide +kernel)
theorem cov267_4 : PA.Covered 4 (OZ.Valid 4 w267.low w267.t w267.y w267.r w267.cap) (P33.root 4) :=
  Night6836Tree.sound w267 pick267 4 t565 _ (by decide +kernel)
theorem cov267_5 : PA.Covered 5 (OZ.Valid 5 w267.low w267.t w267.y w267.r w267.cap) (P33.root 5) :=
  Night6836Tree.sound w267 pick267 5 t566 _ (by decide +kernel)
theorem cov267_6 : PA.Covered 6 (OZ.Valid 6 w267.low w267.t w267.y w267.r w267.cap) (P33.root 6) :=
  Night6836Tree.sound w267 pick267 6 t567 _ (by decide +kernel)
theorem cov267_7 : PA.Covered 7 (OZ.Valid 7 w267.low w267.t w267.y w267.r w267.cap) (P33.root 7) :=
  Night6836Tree.sound w267 pick267 7 t568 _ (by decide +kernel)
theorem window267 : P33.WindowCount w267 := by
  apply P33.window_count w267 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov267_1
  · exact cov267_2
  · exact cov267_3
  · exact cov267_4
  · exact cov267_5
  · exact cov267_6
  · exact cov267_7
def w268 : P33.Window := ⟨14,28,6643,6466,243627979572204470,13596,27000,5000000,81920000000⟩
def h268_0 : Height w268 := ⟨13596,27000,by decide +kernel⟩
def h268_1 : Height w268 := ⟨17559,24000,by decide +kernel⟩
def h268_2 : Height w268 := ⟨22963,21000,by decide +kernel⟩
def h268_3 : Height w268 := ⟨31594,18000,by decide +kernel⟩
def h268_4 : Height w268 := ⟨50203,15000,by decide +kernel⟩
def pick268 (cl : ℕ) : Height w268 := if cl<32 then (if cl<2 then (h268_0) else (h268_1)) else (if cl<256 then (h268_2) else (if cl<1026 then (h268_3) else (h268_4)))
private theorem k268_1_0 : check w268 pick268 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k268_1_1 : check w268 pick268 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k268_1_2 : check w268 pick268 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w268 pick268 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k268_1_0 k268_1_1
private theorem k268_1_3 : check w268 pick268 1 t8472 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k268_1_4 : check w268 pick268 1 t6792 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k268_1_5 : check w268 pick268 1 t8473 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w268 pick268 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t8472 t6792 k268_1_3 k268_1_4
private theorem k268_1_6 : check w268 pick268 1 t8474 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w268 pick268 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t8473 k268_1_2 k268_1_5
private theorem k268_1_7 : check w268 pick268 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k268_1_8 : check w268 pick268 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k268_1_9 : check w268 pick268 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w268 pick268 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k268_1_7 k268_1_8
private theorem k268_1_10 : check w268 pick268 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k268_1_11 : check w268 pick268 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k268_1_12 : check w268 pick268 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w268 pick268 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k268_1_10 k268_1_11
private theorem k268_1_13 : check w268 pick268 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w268 pick268 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k268_1_9 k268_1_12
private theorem k268_1_14 : check w268 pick268 1 t8475 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w268 pick268 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8474 t7519 k268_1_6 k268_1_13
theorem cov268_1 : PA.Covered 1 (OZ.Valid 1 w268.low w268.t w268.y w268.r w268.cap) (P33.root 1) :=
  Night6836Tree.sound w268 pick268 1 t8475 _ k268_1_14
private theorem k268_2_0 : check w268 pick268 2 t7548 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k268_2_1 : check w268 pick268 2 t5624 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k268_2_2 : check w268 pick268 2 t7549 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w268 pick268 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7548 t5624 k268_2_0 k268_2_1
theorem cov268_2 : PA.Covered 2 (OZ.Valid 2 w268.low w268.t w268.y w268.r w268.cap) (P33.root 2) :=
  Night6836Tree.sound w268 pick268 2 t7549 _ k268_2_2
theorem cov268_3 : PA.Covered 3 (OZ.Valid 3 w268.low w268.t w268.y w268.r w268.cap) (P33.root 3) :=
  Night6836Tree.sound w268 pick268 3 t564 _ (by decide +kernel)
theorem cov268_4 : PA.Covered 4 (OZ.Valid 4 w268.low w268.t w268.y w268.r w268.cap) (P33.root 4) :=
  Night6836Tree.sound w268 pick268 4 t565 _ (by decide +kernel)
theorem cov268_5 : PA.Covered 5 (OZ.Valid 5 w268.low w268.t w268.y w268.r w268.cap) (P33.root 5) :=
  Night6836Tree.sound w268 pick268 5 t566 _ (by decide +kernel)
theorem cov268_6 : PA.Covered 6 (OZ.Valid 6 w268.low w268.t w268.y w268.r w268.cap) (P33.root 6) :=
  Night6836Tree.sound w268 pick268 6 t567 _ (by decide +kernel)
theorem cov268_7 : PA.Covered 7 (OZ.Valid 7 w268.low w268.t w268.y w268.r w268.cap) (P33.root 7) :=
  Night6836Tree.sound w268 pick268 7 t568 _ (by decide +kernel)
theorem window268 : P33.WindowCount w268 := by
  apply P33.window_count w268 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov268_1
  · exact cov268_2
  · exact cov268_3
  · exact cov268_4
  · exact cov268_5
  · exact cov268_6
  · exact cov268_7
def w269 : P33.Window := ⟨14,29,6465,6283,241961735534619572,16289,27000,5000000,81920000000⟩
def h269_0 : Height w269 := ⟨16289,27000,by decide +kernel⟩
def h269_1 : Height w269 := ⟨20640,24000,by decide +kernel⟩
def h269_2 : Height w269 := ⟨26713,21000,by decide +kernel⟩
def h269_3 : Height w269 := ⟨36728,18000,by decide +kernel⟩
def pick269 (cl : ℕ) : Height w269 := if cl<40 then (if cl<5 then (h269_0) else (h269_1)) else (if cl<493 then (h269_2) else (h269_3))
private theorem k269_1_0 : check w269 pick269 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k269_1_1 : check w269 pick269 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k269_1_2 : check w269 pick269 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w269 pick269 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k269_1_0 k269_1_1
private theorem k269_1_3 : check w269 pick269 1 t7526 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k269_1_4 : check w269 pick269 1 t7529 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k269_1_5 : check w269 pick269 1 t7530 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w269 pick269 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t7526 t7529 k269_1_3 k269_1_4
private theorem k269_1_6 : check w269 pick269 1 t7531 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w269 pick269 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t7530 k269_1_2 k269_1_5
private theorem k269_1_7 : check w269 pick269 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k269_1_8 : check w269 pick269 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k269_1_9 : check w269 pick269 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w269 pick269 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k269_1_7 k269_1_8
private theorem k269_1_10 : check w269 pick269 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k269_1_11 : check w269 pick269 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k269_1_12 : check w269 pick269 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w269 pick269 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k269_1_10 k269_1_11
private theorem k269_1_13 : check w269 pick269 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w269 pick269 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k269_1_9 k269_1_12
private theorem k269_1_14 : check w269 pick269 1 t7532 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w269 pick269 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t7531 t7519 k269_1_6 k269_1_13
theorem cov269_1 : PA.Covered 1 (OZ.Valid 1 w269.low w269.t w269.y w269.r w269.cap) (P33.root 1) :=
  Night6836Tree.sound w269 pick269 1 t7532 _ k269_1_14
private theorem k269_2_0 : check w269 pick269 2 t7548 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k269_2_1 : check w269 pick269 2 t5624 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k269_2_2 : check w269 pick269 2 t7549 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w269 pick269 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7548 t5624 k269_2_0 k269_2_1
theorem cov269_2 : PA.Covered 2 (OZ.Valid 2 w269.low w269.t w269.y w269.r w269.cap) (P33.root 2) :=
  Night6836Tree.sound w269 pick269 2 t7549 _ k269_2_2
theorem cov269_3 : PA.Covered 3 (OZ.Valid 3 w269.low w269.t w269.y w269.r w269.cap) (P33.root 3) :=
  Night6836Tree.sound w269 pick269 3 t564 _ (by decide +kernel)
theorem cov269_4 : PA.Covered 4 (OZ.Valid 4 w269.low w269.t w269.y w269.r w269.cap) (P33.root 4) :=
  Night6836Tree.sound w269 pick269 4 t565 _ (by decide +kernel)
theorem cov269_5 : PA.Covered 5 (OZ.Valid 5 w269.low w269.t w269.y w269.r w269.cap) (P33.root 5) :=
  Night6836Tree.sound w269 pick269 5 t566 _ (by decide +kernel)
theorem cov269_6 : PA.Covered 6 (OZ.Valid 6 w269.low w269.t w269.y w269.r w269.cap) (P33.root 6) :=
  Night6836Tree.sound w269 pick269 6 t567 _ (by decide +kernel)
theorem cov269_7 : PA.Covered 7 (OZ.Valid 7 w269.low w269.t w269.y w269.r w269.cap) (P33.root 7) :=
  Night6836Tree.sound w269 pick269 7 t568 _ (by decide +kernel)
theorem window269 : P33.WindowCount w269 := by
  apply P33.window_count w269 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov269_1
  · exact cov269_2
  · exact cov269_3
  · exact cov269_4
  · exact cov269_5
  · exact cov269_6
  · exact cov269_7
end ProximityPrize.SubmissionLower.Night6836Bank
