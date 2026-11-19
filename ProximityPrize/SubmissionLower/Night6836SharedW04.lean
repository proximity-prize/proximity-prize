/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT02
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w120 : P33.Window := ⟨11,32,7195,7012,245933386758043328,19640,21000,5000000,81920000000⟩
def h120_0 : Height w120 := ⟨19640,21000,by decide +kernel⟩
def h120_1 : Height w120 := ⟨24444,18000,by decide +kernel⟩
def h120_2 : Height w120 := ⟨31996,15000,by decide +kernel⟩
def h120_3 : Height w120 := ⟨48121,12000,by decide +kernel⟩
def pick120 (cl : ℕ) : Height w120 := if cl<145 then (if cl<10 then (h120_0) else (h120_1)) else (if cl<1021 then (h120_2) else (h120_3))
private theorem k120_1_0 : check w120 pick120 1 t5529 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k120_1_1 : check w120 pick120 1 t5531 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k120_1_2 : check w120 pick120 1 t5532 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w120 pick120 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5529 t5531 k120_1_0 k120_1_1
private theorem k120_1_3 : check w120 pick120 1 t2988 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k120_1_4 : check w120 pick120 1 t5535 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k120_1_5 : check w120 pick120 1 t5536 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w120 pick120 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2988 t5535 k120_1_3 k120_1_4
private theorem k120_1_6 : check w120 pick120 1 t5537 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w120 pick120 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5532 t5536 k120_1_2 k120_1_5
private theorem k120_1_7 : check w120 pick120 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k120_1_8 : check w120 pick120 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k120_1_9 : check w120 pick120 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w120 pick120 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k120_1_7 k120_1_8
private theorem k120_1_10 : check w120 pick120 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k120_1_11 : check w120 pick120 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k120_1_12 : check w120 pick120 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w120 pick120 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k120_1_10 k120_1_11
private theorem k120_1_13 : check w120 pick120 1 t3201 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w120 pick120 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t1079 k120_1_9 k120_1_12
private theorem k120_1_14 : check w120 pick120 1 t5538 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w120 pick120 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5537 t3201 k120_1_6 k120_1_13
theorem cov120_1 : PA.Covered 1 (OZ.Valid 1 w120.low w120.t w120.y w120.r w120.cap) (P33.root 1) :=
  Night6836Tree.sound w120 pick120 1 t5538 _ k120_1_14
private theorem k120_2_0 : check w120 pick120 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k120_2_1 : check w120 pick120 2 t5541 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k120_2_2 : check w120 pick120 2 t5542 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w120 pick120 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t5541 k120_2_0 k120_2_1
theorem cov120_2 : PA.Covered 2 (OZ.Valid 2 w120.low w120.t w120.y w120.r w120.cap) (P33.root 2) :=
  Night6836Tree.sound w120 pick120 2 t5542 _ k120_2_2
theorem cov120_3 : PA.Covered 3 (OZ.Valid 3 w120.low w120.t w120.y w120.r w120.cap) (P33.root 3) :=
  Night6836Tree.sound w120 pick120 3 t564 _ (by decide +kernel)
theorem cov120_4 : PA.Covered 4 (OZ.Valid 4 w120.low w120.t w120.y w120.r w120.cap) (P33.root 4) :=
  Night6836Tree.sound w120 pick120 4 t565 _ (by decide +kernel)
theorem cov120_5 : PA.Covered 5 (OZ.Valid 5 w120.low w120.t w120.y w120.r w120.cap) (P33.root 5) :=
  Night6836Tree.sound w120 pick120 5 t566 _ (by decide +kernel)
theorem cov120_6 : PA.Covered 6 (OZ.Valid 6 w120.low w120.t w120.y w120.r w120.cap) (P33.root 6) :=
  Night6836Tree.sound w120 pick120 6 t567 _ (by decide +kernel)
theorem cov120_7 : PA.Covered 7 (OZ.Valid 7 w120.low w120.t w120.y w120.r w120.cap) (P33.root 7) :=
  Night6836Tree.sound w120 pick120 7 t568 _ (by decide +kernel)
theorem window120 : P33.WindowCount w120 := by
  apply P33.window_count w120 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov120_1
  · exact cov120_2
  · exact cov120_3
  · exact cov120_4
  · exact cov120_5
  · exact cov120_6
  · exact cov120_7
def w121 : P33.Window := ⟨11,33,5832,4833,203846135450651483,29403,31000,5000000,81920000000⟩
def h121_0 : Height w121 := ⟨29403,31000,by decide +kernel⟩
def h121_1 : Height w121 := ⟨35587,27000,by decide +kernel⟩
def h121_2 : Height w121 := ⟨44619,23000,by decide +kernel⟩
def h121_3 : Height w121 := ⟨60887,19000,by decide +kernel⟩
def pick121 (cl : ℕ) : Height w121 := if cl<83 then (if cl<6 then (h121_0) else (h121_1)) else (if cl<922 then (h121_2) else (h121_3))
private theorem k121_1_0 : check w121 pick121 1 t5529 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k121_1_1 : check w121 pick121 1 t5548 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k121_1_2 : check w121 pick121 1 t5549 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w121 pick121 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5529 t5548 k121_1_0 k121_1_1
private theorem k121_1_3 : check w121 pick121 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k121_1_4 : check w121 pick121 1 t5562 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k121_1_5 : check w121 pick121 1 t5563 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w121 pick121 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t5562 k121_1_3 k121_1_4
private theorem k121_1_6 : check w121 pick121 1 t5564 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w121 pick121 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5549 t5563 k121_1_2 k121_1_5
private theorem k121_1_7 : check w121 pick121 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k121_1_8 : check w121 pick121 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k121_1_9 : check w121 pick121 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w121 pick121 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k121_1_7 k121_1_8
private theorem k121_1_10 : check w121 pick121 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k121_1_11 : check w121 pick121 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k121_1_12 : check w121 pick121 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w121 pick121 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k121_1_10 k121_1_11
private theorem k121_1_13 : check w121 pick121 1 t3201 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w121 pick121 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t1079 k121_1_9 k121_1_12
private theorem k121_1_14 : check w121 pick121 1 t5565 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w121 pick121 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5564 t3201 k121_1_6 k121_1_13
theorem cov121_1 : PA.Covered 1 (OZ.Valid 1 w121.low w121.t w121.y w121.r w121.cap) (P33.root 1) :=
  Night6836Tree.sound w121 pick121 1 t5565 _ k121_1_14
private theorem k121_2_0 : check w121 pick121 2 t5566 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k121_2_1 : check w121 pick121 2 t5541 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k121_2_2 : check w121 pick121 2 t5567 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w121 pick121 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5566 t5541 k121_2_0 k121_2_1
theorem cov121_2 : PA.Covered 2 (OZ.Valid 2 w121.low w121.t w121.y w121.r w121.cap) (P33.root 2) :=
  Night6836Tree.sound w121 pick121 2 t5567 _ k121_2_2
theorem cov121_3 : PA.Covered 3 (OZ.Valid 3 w121.low w121.t w121.y w121.r w121.cap) (P33.root 3) :=
  Night6836Tree.sound w121 pick121 3 t564 _ (by decide +kernel)
theorem cov121_4 : PA.Covered 4 (OZ.Valid 4 w121.low w121.t w121.y w121.r w121.cap) (P33.root 4) :=
  Night6836Tree.sound w121 pick121 4 t565 _ (by decide +kernel)
theorem cov121_5 : PA.Covered 5 (OZ.Valid 5 w121.low w121.t w121.y w121.r w121.cap) (P33.root 5) :=
  Night6836Tree.sound w121 pick121 5 t566 _ (by decide +kernel)
theorem cov121_6 : PA.Covered 6 (OZ.Valid 6 w121.low w121.t w121.y w121.r w121.cap) (P33.root 6) :=
  Night6836Tree.sound w121 pick121 6 t567 _ (by decide +kernel)
theorem cov121_7 : PA.Covered 7 (OZ.Valid 7 w121.low w121.t w121.y w121.r w121.cap) (P33.root 7) :=
  Night6836Tree.sound w121 pick121 7 t2134 _ (by decide +kernel)
theorem window121 : P33.WindowCount w121 := by
  apply P33.window_count w121 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov121_1
  · exact cov121_2
  · exact cov121_3
  · exact cov121_4
  · exact cov121_5
  · exact cov121_6
  · exact cov121_7
def w122 : P33.Window := ⟨11,33,7151,7107,245887798719444598,20115,21000,5000000,81920000000⟩
def h122_0 : Height w122 := ⟨20115,21000,by decide +kernel⟩
def h122_1 : Height w122 := ⟨24893,18000,by decide +kernel⟩
def h122_2 : Height w122 := ⟨32356,15000,by decide +kernel⟩
def h122_3 : Height w122 := ⟨48066,12000,by decide +kernel⟩
def pick122 (cl : ℕ) : Height w122 := if cl<132 then (if cl<10 then (h122_0) else (h122_1)) else (if cl<1020 then (h122_2) else (h122_3))
private theorem k122_1_0 : check w122 pick122 1 t5570 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k122_1_1 : check w122 pick122 1 t5577 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k122_1_2 : check w122 pick122 1 t5578 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w122 pick122 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5570 t5577 k122_1_0 k122_1_1
private theorem k122_1_3 : check w122 pick122 1 t5589 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k122_1_4 : check w122 pick122 1 t5603 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k122_1_5 : check w122 pick122 1 t5604 ⟨1,7,2,16,1,52,70,138⟩ = true := glue w122 pick122 1 ⟨1,7,2,16,1,52,70,138⟩ 3 104 t5589 t5603 k122_1_3 k122_1_4
private theorem k122_1_6 : check w122 pick122 1 t5605 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w122 pick122 1 ⟨1,7,2,16,1,52,1,138⟩ 3 69 t5578 t5604 k122_1_2 k122_1_5
private theorem k122_1_7 : check w122 pick122 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k122_1_8 : check w122 pick122 1 t3371 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k122_1_9 : check w122 pick122 1 t3372 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w122 pick122 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t3199 t3371 k122_1_7 k122_1_8
private theorem k122_1_10 : check w122 pick122 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k122_1_11 : check w122 pick122 1 t3405 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k122_1_12 : check w122 pick122 1 t5606 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w122 pick122 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t3405 k122_1_10 k122_1_11
private theorem k122_1_13 : check w122 pick122 1 t5607 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w122 pick122 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t3372 t5606 k122_1_9 k122_1_12
private theorem k122_1_14 : check w122 pick122 1 t5608 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w122 pick122 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5605 t5607 k122_1_6 k122_1_13
theorem cov122_1 : PA.Covered 1 (OZ.Valid 1 w122.low w122.t w122.y w122.r w122.cap) (P33.root 1) :=
  Night6836Tree.sound w122 pick122 1 t5608 _ k122_1_14
private theorem k122_2_0 : check w122 pick122 2 t5617 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k122_2_1 : check w122 pick122 2 t5624 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k122_2_2 : check w122 pick122 2 t5625 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w122 pick122 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5617 t5624 k122_2_0 k122_2_1
theorem cov122_2 : PA.Covered 2 (OZ.Valid 2 w122.low w122.t w122.y w122.r w122.cap) (P33.root 2) :=
  Night6836Tree.sound w122 pick122 2 t5625 _ k122_2_2
theorem cov122_3 : PA.Covered 3 (OZ.Valid 3 w122.low w122.t w122.y w122.r w122.cap) (P33.root 3) :=
  Night6836Tree.sound w122 pick122 3 t564 _ (by decide +kernel)
theorem cov122_4 : PA.Covered 4 (OZ.Valid 4 w122.low w122.t w122.y w122.r w122.cap) (P33.root 4) :=
  Night6836Tree.sound w122 pick122 4 t565 _ (by decide +kernel)
theorem cov122_5 : PA.Covered 5 (OZ.Valid 5 w122.low w122.t w122.y w122.r w122.cap) (P33.root 5) :=
  Night6836Tree.sound w122 pick122 5 t566 _ (by decide +kernel)
theorem cov122_6 : PA.Covered 6 (OZ.Valid 6 w122.low w122.t w122.y w122.r w122.cap) (P33.root 6) :=
  Night6836Tree.sound w122 pick122 6 t567 _ (by decide +kernel)
theorem cov122_7 : PA.Covered 7 (OZ.Valid 7 w122.low w122.t w122.y w122.r w122.cap) (P33.root 7) :=
  Night6836Tree.sound w122 pick122 7 t568 _ (by decide +kernel)
theorem window122 : P33.WindowCount w122 := by
  apply P33.window_count w122 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov122_1
  · exact cov122_2
  · exact cov122_3
  · exact cov122_4
  · exact cov122_5
  · exact cov122_6
  · exact cov122_7
def w123 : P33.Window := ⟨11,34,7106,7062,246272797982036856,21547,21000,5000000,81920000000⟩
def h123_0 : Height w123 := ⟨21547,21000,by decide +kernel⟩
def h123_1 : Height w123 := ⟨26515,18000,by decide +kernel⟩
def h123_2 : Height w123 := ⟨34343,15000,by decide +kernel⟩
def h123_3 : Height w123 := ⟨51011,12000,by decide +kernel⟩
def pick123 (cl : ℕ) : Height w123 := if cl<165 then (if cl<13 then (h123_0) else (h123_1)) else (if cl<1021 then (h123_2) else (h123_3))
private theorem k123_1_0 : check w123 pick123 1 t5626 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k123_1_1 : check w123 pick123 1 t5577 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k123_1_2 : check w123 pick123 1 t5627 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w123 pick123 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5626 t5577 k123_1_0 k123_1_1
private theorem k123_1_3 : check w123 pick123 1 t5589 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k123_1_4 : check w123 pick123 1 t5603 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k123_1_5 : check w123 pick123 1 t5604 ⟨1,7,2,16,1,52,70,138⟩ = true := glue w123 pick123 1 ⟨1,7,2,16,1,52,70,138⟩ 3 104 t5589 t5603 k123_1_3 k123_1_4
private theorem k123_1_6 : check w123 pick123 1 t5628 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w123 pick123 1 ⟨1,7,2,16,1,52,1,138⟩ 3 69 t5627 t5604 k123_1_2 k123_1_5
private theorem k123_1_7 : check w123 pick123 1 t5629 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k123_1_8 : check w123 pick123 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k123_1_9 : check w123 pick123 1 t5630 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w123 pick123 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t5629 t3615 k123_1_7 k123_1_8
private theorem k123_1_10 : check w123 pick123 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k123_1_11 : check w123 pick123 1 t3405 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k123_1_12 : check w123 pick123 1 t3656 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w123 pick123 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t3405 k123_1_10 k123_1_11
private theorem k123_1_13 : check w123 pick123 1 t5631 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w123 pick123 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t5630 t3656 k123_1_9 k123_1_12
private theorem k123_1_14 : check w123 pick123 1 t5632 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w123 pick123 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5628 t5631 k123_1_6 k123_1_13
theorem cov123_1 : PA.Covered 1 (OZ.Valid 1 w123.low w123.t w123.y w123.r w123.cap) (P33.root 1) :=
  Night6836Tree.sound w123 pick123 1 t5632 _ k123_1_14
private theorem k123_2_0 : check w123 pick123 2 t5638 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k123_2_1 : check w123 pick123 2 t5646 ⟨2,7,4,16,2,52,85,166⟩ = true := by decide +kernel
private theorem k123_2_2 : check w123 pick123 2 t5647 ⟨2,7,4,16,2,52,2,166⟩ = true := glue w123 pick123 2 ⟨2,7,4,16,2,52,2,166⟩ 3 84 t5638 t5646 k123_2_0 k123_2_1
private theorem k123_2_3 : check w123 pick123 2 t5650 ⟨2,7,4,16,2,52,167,450⟩ = true := by decide +kernel
private theorem k123_2_4 : check w123 pick123 2 t5651 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w123 pick123 2 ⟨2,7,4,16,0,52,0,450⟩ 3 166 t5647 t5650 k123_2_2 k123_2_3
theorem cov123_2 : PA.Covered 2 (OZ.Valid 2 w123.low w123.t w123.y w123.r w123.cap) (P33.root 2) :=
  Night6836Tree.sound w123 pick123 2 t5651 _ k123_2_4
theorem cov123_3 : PA.Covered 3 (OZ.Valid 3 w123.low w123.t w123.y w123.r w123.cap) (P33.root 3) :=
  Night6836Tree.sound w123 pick123 3 t564 _ (by decide +kernel)
theorem cov123_4 : PA.Covered 4 (OZ.Valid 4 w123.low w123.t w123.y w123.r w123.cap) (P33.root 4) :=
  Night6836Tree.sound w123 pick123 4 t565 _ (by decide +kernel)
theorem cov123_5 : PA.Covered 5 (OZ.Valid 5 w123.low w123.t w123.y w123.r w123.cap) (P33.root 5) :=
  Night6836Tree.sound w123 pick123 5 t566 _ (by decide +kernel)
theorem cov123_6 : PA.Covered 6 (OZ.Valid 6 w123.low w123.t w123.y w123.r w123.cap) (P33.root 6) :=
  Night6836Tree.sound w123 pick123 6 t567 _ (by decide +kernel)
theorem cov123_7 : PA.Covered 7 (OZ.Valid 7 w123.low w123.t w123.y w123.r w123.cap) (P33.root 7) :=
  Night6836Tree.sound w123 pick123 7 t568 _ (by decide +kernel)
theorem window123 : P33.WindowCount w123 := by
  apply P33.window_count w123 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov123_1
  · exact cov123_2
  · exact cov123_3
  · exact cov123_4
  · exact cov123_5
  · exact cov123_6
  · exact cov123_7
def w124 : P33.Window := ⟨11,35,7061,7012,246262454557153297,23046,21000,5000000,81920000000⟩
def h124_0 : Height w124 := ⟨23046,21000,by decide +kernel⟩
def h124_1 : Height w124 := ⟨28220,18000,by decide +kernel⟩
def h124_2 : Height w124 := ⟨36447,15000,by decide +kernel⟩
def h124_3 : Height w124 := ⟨54180,12000,by decide +kernel⟩
def pick124 (cl : ℕ) : Height w124 := if cl<210 then (if cl<18 then (h124_0) else (h124_1)) else (if cl<1026 then (h124_2) else (h124_3))
private theorem k124_1_0 : check w124 pick124 1 t5626 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k124_1_1 : check w124 pick124 1 t5662 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k124_1_2 : check w124 pick124 1 t5663 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w124 pick124 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5626 t5662 k124_1_0 k124_1_1
private theorem k124_1_3 : check w124 pick124 1 t3944 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k124_1_4 : check w124 pick124 1 t5666 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k124_1_5 : check w124 pick124 1 t5667 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w124 pick124 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3944 t5666 k124_1_3 k124_1_4
private theorem k124_1_6 : check w124 pick124 1 t5668 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w124 pick124 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5663 t5667 k124_1_2 k124_1_5
private theorem k124_1_7 : check w124 pick124 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k124_1_8 : check w124 pick124 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k124_1_9 : check w124 pick124 1 t3616 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w124 pick124 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t3615 k124_1_7 k124_1_8
private theorem k124_1_10 : check w124 pick124 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k124_1_11 : check w124 pick124 1 t3405 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k124_1_12 : check w124 pick124 1 t3656 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w124 pick124 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t3405 k124_1_10 k124_1_11
private theorem k124_1_13 : check w124 pick124 1 t3657 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w124 pick124 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3616 t3656 k124_1_9 k124_1_12
private theorem k124_1_14 : check w124 pick124 1 t5669 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w124 pick124 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5668 t3657 k124_1_6 k124_1_13
theorem cov124_1 : PA.Covered 1 (OZ.Valid 1 w124.low w124.t w124.y w124.r w124.cap) (P33.root 1) :=
  Night6836Tree.sound w124 pick124 1 t5669 _ k124_1_14
private theorem k124_2_0 : check w124 pick124 2 t5695 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k124_2_1 : check w124 pick124 2 t5699 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k124_2_2 : check w124 pick124 2 t5700 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w124 pick124 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5695 t5699 k124_2_0 k124_2_1
private theorem k124_2_3 : check w124 pick124 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k124_2_4 : check w124 pick124 2 t3530 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k124_2_5 : check w124 pick124 2 t3531 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w124 pick124 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t3530 k124_2_3 k124_2_4
private theorem k124_2_6 : check w124 pick124 2 t5701 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w124 pick124 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5700 t3531 k124_2_2 k124_2_5
theorem cov124_2 : PA.Covered 2 (OZ.Valid 2 w124.low w124.t w124.y w124.r w124.cap) (P33.root 2) :=
  Night6836Tree.sound w124 pick124 2 t5701 _ k124_2_6
theorem cov124_3 : PA.Covered 3 (OZ.Valid 3 w124.low w124.t w124.y w124.r w124.cap) (P33.root 3) :=
  Night6836Tree.sound w124 pick124 3 t564 _ (by decide +kernel)
theorem cov124_4 : PA.Covered 4 (OZ.Valid 4 w124.low w124.t w124.y w124.r w124.cap) (P33.root 4) :=
  Night6836Tree.sound w124 pick124 4 t565 _ (by decide +kernel)
theorem cov124_5 : PA.Covered 5 (OZ.Valid 5 w124.low w124.t w124.y w124.r w124.cap) (P33.root 5) :=
  Night6836Tree.sound w124 pick124 5 t566 _ (by decide +kernel)
theorem cov124_6 : PA.Covered 6 (OZ.Valid 6 w124.low w124.t w124.y w124.r w124.cap) (P33.root 6) :=
  Night6836Tree.sound w124 pick124 6 t567 _ (by decide +kernel)
theorem cov124_7 : PA.Covered 7 (OZ.Valid 7 w124.low w124.t w124.y w124.r w124.cap) (P33.root 7) :=
  Night6836Tree.sound w124 pick124 7 t568 _ (by decide +kernel)
theorem window124 : P33.WindowCount w124 := by
  apply P33.window_count w124 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov124_1
  · exact cov124_2
  · exact cov124_3
  · exact cov124_4
  · exact cov124_5
  · exact cov124_6
  · exact cov124_7
def w125 : P33.Window := ⟨11,36,7011,6959,242281148374957518,20654,24000,5000000,81920000000⟩
def h125_0 : Height w125 := ⟨20654,24000,by decide +kernel⟩
def h125_1 : Height w125 := ⟨24603,21000,by decide +kernel⟩
def h125_2 : Height w125 := ⟨29998,18000,by decide +kernel⟩
def h125_3 : Height w125 := ⟨38654,15000,by decide +kernel⟩
def h125_4 : Height w125 := ⟨57555,12000,by decide +kernel⟩
def pick125 (cl : ℕ) : Height w125 := if cl<25 then (if cl<2 then (h125_0) else (h125_1)) else (if cl<257 then (h125_2) else (if cl<1026 then (h125_3) else (h125_4)))
private theorem k125_1_0 : check w125 pick125 1 t5626 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k125_1_1 : check w125 pick125 1 t5714 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k125_1_2 : check w125 pick125 1 t5715 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w125 pick125 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5626 t5714 k125_1_0 k125_1_1
private theorem k125_1_3 : check w125 pick125 1 t3944 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k125_1_4 : check w125 pick125 1 t5666 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k125_1_5 : check w125 pick125 1 t5667 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w125 pick125 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3944 t5666 k125_1_3 k125_1_4
private theorem k125_1_6 : check w125 pick125 1 t5716 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w125 pick125 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5715 t5667 k125_1_2 k125_1_5
private theorem k125_1_7 : check w125 pick125 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k125_1_8 : check w125 pick125 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k125_1_9 : check w125 pick125 1 t3616 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w125 pick125 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t3615 k125_1_7 k125_1_8
private theorem k125_1_10 : check w125 pick125 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k125_1_11 : check w125 pick125 1 t3405 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k125_1_12 : check w125 pick125 1 t3656 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w125 pick125 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t3405 k125_1_10 k125_1_11
private theorem k125_1_13 : check w125 pick125 1 t3657 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w125 pick125 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3616 t3656 k125_1_9 k125_1_12
private theorem k125_1_14 : check w125 pick125 1 t5717 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w125 pick125 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5716 t3657 k125_1_6 k125_1_13
theorem cov125_1 : PA.Covered 1 (OZ.Valid 1 w125.low w125.t w125.y w125.r w125.cap) (P33.root 1) :=
  Night6836Tree.sound w125 pick125 1 t5717 _ k125_1_14
private theorem k125_2_0 : check w125 pick125 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k125_2_1 : check w125 pick125 2 t5723 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k125_2_2 : check w125 pick125 2 t5724 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w125 pick125 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5723 k125_2_0 k125_2_1
private theorem k125_2_3 : check w125 pick125 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k125_2_4 : check w125 pick125 2 t3530 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k125_2_5 : check w125 pick125 2 t3531 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w125 pick125 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t3530 k125_2_3 k125_2_4
private theorem k125_2_6 : check w125 pick125 2 t5725 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w125 pick125 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5724 t3531 k125_2_2 k125_2_5
theorem cov125_2 : PA.Covered 2 (OZ.Valid 2 w125.low w125.t w125.y w125.r w125.cap) (P33.root 2) :=
  Night6836Tree.sound w125 pick125 2 t5725 _ k125_2_6
theorem cov125_3 : PA.Covered 3 (OZ.Valid 3 w125.low w125.t w125.y w125.r w125.cap) (P33.root 3) :=
  Night6836Tree.sound w125 pick125 3 t564 _ (by decide +kernel)
theorem cov125_4 : PA.Covered 4 (OZ.Valid 4 w125.low w125.t w125.y w125.r w125.cap) (P33.root 4) :=
  Night6836Tree.sound w125 pick125 4 t565 _ (by decide +kernel)
theorem cov125_5 : PA.Covered 5 (OZ.Valid 5 w125.low w125.t w125.y w125.r w125.cap) (P33.root 5) :=
  Night6836Tree.sound w125 pick125 5 t566 _ (by decide +kernel)
theorem cov125_6 : PA.Covered 6 (OZ.Valid 6 w125.low w125.t w125.y w125.r w125.cap) (P33.root 6) :=
  Night6836Tree.sound w125 pick125 6 t567 _ (by decide +kernel)
theorem cov125_7 : PA.Covered 7 (OZ.Valid 7 w125.low w125.t w125.y w125.r w125.cap) (P33.root 7) :=
  Night6836Tree.sound w125 pick125 7 t568 _ (by decide +kernel)
theorem window125 : P33.WindowCount w125 := by
  apply P33.window_count w125 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov125_1
  · exact cov125_2
  · exact cov125_3
  · exact cov125_4
  · exact cov125_5
  · exact cov125_6
  · exact cov125_7
def w126 : P33.Window := ⟨11,37,6958,6796,245438871178919931,22940,24000,5000000,81920000000⟩
def h126_0 : Height w126 := ⟨22940,24000,by decide +kernel⟩
def h126_1 : Height w126 := ⟨27161,21000,by decide +kernel⟩
def h126_2 : Height w126 := ⟨33019,18000,by decide +kernel⟩
def h126_3 : Height w126 := ⟨42618,15000,by decide +kernel⟩
def pick126 (cl : ℕ) : Height w126 := if cl<34 then (if cl<4 then (h126_0) else (h126_1)) else (if cl<337 then (h126_2) else (h126_3))
private theorem k126_1_0 : check w126 pick126 1 t5626 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k126_1_1 : check w126 pick126 1 t5714 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k126_1_2 : check w126 pick126 1 t5715 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w126 pick126 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5626 t5714 k126_1_0 k126_1_1
private theorem k126_1_3 : check w126 pick126 1 t3944 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k126_1_4 : check w126 pick126 1 t5666 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k126_1_5 : check w126 pick126 1 t5667 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w126 pick126 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3944 t5666 k126_1_3 k126_1_4
private theorem k126_1_6 : check w126 pick126 1 t5716 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w126 pick126 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5715 t5667 k126_1_2 k126_1_5
private theorem k126_1_7 : check w126 pick126 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k126_1_8 : check w126 pick126 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k126_1_9 : check w126 pick126 1 t3616 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w126 pick126 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t3615 k126_1_7 k126_1_8
private theorem k126_1_10 : check w126 pick126 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k126_1_11 : check w126 pick126 1 t3949 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k126_1_12 : check w126 pick126 1 t3950 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w126 pick126 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t3949 k126_1_10 k126_1_11
private theorem k126_1_13 : check w126 pick126 1 t3951 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w126 pick126 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3616 t3950 k126_1_9 k126_1_12
private theorem k126_1_14 : check w126 pick126 1 t5726 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w126 pick126 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5716 t3951 k126_1_6 k126_1_13
theorem cov126_1 : PA.Covered 1 (OZ.Valid 1 w126.low w126.t w126.y w126.r w126.cap) (P33.root 1) :=
  Night6836Tree.sound w126 pick126 1 t5726 _ k126_1_14
private theorem k126_2_0 : check w126 pick126 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k126_2_1 : check w126 pick126 2 t5723 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k126_2_2 : check w126 pick126 2 t5724 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w126 pick126 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5723 k126_2_0 k126_2_1
private theorem k126_2_3 : check w126 pick126 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k126_2_4 : check w126 pick126 2 t3530 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k126_2_5 : check w126 pick126 2 t3531 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w126 pick126 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t3530 k126_2_3 k126_2_4
private theorem k126_2_6 : check w126 pick126 2 t5725 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w126 pick126 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5724 t3531 k126_2_2 k126_2_5
theorem cov126_2 : PA.Covered 2 (OZ.Valid 2 w126.low w126.t w126.y w126.r w126.cap) (P33.root 2) :=
  Night6836Tree.sound w126 pick126 2 t5725 _ k126_2_6
theorem cov126_3 : PA.Covered 3 (OZ.Valid 3 w126.low w126.t w126.y w126.r w126.cap) (P33.root 3) :=
  Night6836Tree.sound w126 pick126 3 t564 _ (by decide +kernel)
theorem cov126_4 : PA.Covered 4 (OZ.Valid 4 w126.low w126.t w126.y w126.r w126.cap) (P33.root 4) :=
  Night6836Tree.sound w126 pick126 4 t565 _ (by decide +kernel)
theorem cov126_5 : PA.Covered 5 (OZ.Valid 5 w126.low w126.t w126.y w126.r w126.cap) (P33.root 5) :=
  Night6836Tree.sound w126 pick126 5 t566 _ (by decide +kernel)
theorem cov126_6 : PA.Covered 6 (OZ.Valid 6 w126.low w126.t w126.y w126.r w126.cap) (P33.root 6) :=
  Night6836Tree.sound w126 pick126 6 t567 _ (by decide +kernel)
theorem cov126_7 : PA.Covered 7 (OZ.Valid 7 w126.low w126.t w126.y w126.r w126.cap) (P33.root 7) :=
  Night6836Tree.sound w126 pick126 7 t568 _ (by decide +kernel)
theorem window126 : P33.WindowCount w126 := by
  apply P33.window_count w126 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov126_1
  · exact cov126_2
  · exact cov126_3
  · exact cov126_4
  · exact cov126_5
  · exact cov126_6
  · exact cov126_7
def w127 : P33.Window := ⟨11,38,6904,6851,246527079309986134,23614,24000,5000000,81920000000⟩
def h127_0 : Height w127 := ⟨23614,24000,by decide +kernel⟩
def h127_1 : Height w127 := ⟨27851,21000,by decide +kernel⟩
def h127_2 : Height w127 := ⟨33724,18000,by decide +kernel⟩
def h127_3 : Height w127 := ⟨43316,15000,by decide +kernel⟩
def pick127 (cl : ℕ) : Height w127 := if cl<36 then (if cl<4 then (h127_0) else (h127_1)) else (if cl<337 then (h127_2) else (h127_3))
private theorem k127_1_0 : check w127 pick127 1 t5626 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k127_1_1 : check w127 pick127 1 t5714 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k127_1_2 : check w127 pick127 1 t5715 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w127 pick127 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5626 t5714 k127_1_0 k127_1_1
private theorem k127_1_3 : check w127 pick127 1 t3944 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k127_1_4 : check w127 pick127 1 t5666 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k127_1_5 : check w127 pick127 1 t5667 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w127 pick127 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3944 t5666 k127_1_3 k127_1_4
private theorem k127_1_6 : check w127 pick127 1 t5716 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w127 pick127 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5715 t5667 k127_1_2 k127_1_5
private theorem k127_1_7 : check w127 pick127 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k127_1_8 : check w127 pick127 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k127_1_9 : check w127 pick127 1 t3616 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w127 pick127 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t3615 k127_1_7 k127_1_8
private theorem k127_1_10 : check w127 pick127 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k127_1_11 : check w127 pick127 1 t3949 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k127_1_12 : check w127 pick127 1 t3950 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w127 pick127 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t3949 k127_1_10 k127_1_11
private theorem k127_1_13 : check w127 pick127 1 t3951 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w127 pick127 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3616 t3950 k127_1_9 k127_1_12
private theorem k127_1_14 : check w127 pick127 1 t5726 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w127 pick127 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5716 t3951 k127_1_6 k127_1_13
theorem cov127_1 : PA.Covered 1 (OZ.Valid 1 w127.low w127.t w127.y w127.r w127.cap) (P33.root 1) :=
  Night6836Tree.sound w127 pick127 1 t5726 _ k127_1_14
private theorem k127_2_0 : check w127 pick127 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k127_2_1 : check w127 pick127 2 t5736 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k127_2_2 : check w127 pick127 2 t5737 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w127 pick127 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5736 k127_2_0 k127_2_1
private theorem k127_2_3 : check w127 pick127 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k127_2_4 : check w127 pick127 2 t5740 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k127_2_5 : check w127 pick127 2 t5741 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w127 pick127 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t5740 k127_2_3 k127_2_4
private theorem k127_2_6 : check w127 pick127 2 t5742 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w127 pick127 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5737 t5741 k127_2_2 k127_2_5
theorem cov127_2 : PA.Covered 2 (OZ.Valid 2 w127.low w127.t w127.y w127.r w127.cap) (P33.root 2) :=
  Night6836Tree.sound w127 pick127 2 t5742 _ k127_2_6
theorem cov127_3 : PA.Covered 3 (OZ.Valid 3 w127.low w127.t w127.y w127.r w127.cap) (P33.root 3) :=
  Night6836Tree.sound w127 pick127 3 t4151 _ (by decide +kernel)
theorem cov127_4 : PA.Covered 4 (OZ.Valid 4 w127.low w127.t w127.y w127.r w127.cap) (P33.root 4) :=
  Night6836Tree.sound w127 pick127 4 t565 _ (by decide +kernel)
theorem cov127_5 : PA.Covered 5 (OZ.Valid 5 w127.low w127.t w127.y w127.r w127.cap) (P33.root 5) :=
  Night6836Tree.sound w127 pick127 5 t566 _ (by decide +kernel)
theorem cov127_6 : PA.Covered 6 (OZ.Valid 6 w127.low w127.t w127.y w127.r w127.cap) (P33.root 6) :=
  Night6836Tree.sound w127 pick127 6 t567 _ (by decide +kernel)
theorem cov127_7 : PA.Covered 7 (OZ.Valid 7 w127.low w127.t w127.y w127.r w127.cap) (P33.root 7) :=
  Night6836Tree.sound w127 pick127 7 t568 _ (by decide +kernel)
theorem window127 : P33.WindowCount w127 := by
  apply P33.window_count w127 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov127_1
  · exact cov127_2
  · exact cov127_3
  · exact cov127_4
  · exact cov127_5
  · exact cov127_6
  · exact cov127_7
def w128 : P33.Window := ⟨11,39,6172,5223,244078260024243368,34352,30000,5000000,81920000000⟩
def h128_0 : Height w128 := ⟨34352,30000,by decide +kernel⟩
def h128_1 : Height w128 := ⟨38978,27000,by decide +kernel⟩
def h128_2 : Height w128 := ⟨44984,24000,by decide +kernel⟩
def h128_3 : Height w128 := ⟨53538,21000,by decide +kernel⟩
def h128_4 : Height w128 := ⟨67636,18000,by decide +kernel⟩
def pick128 (cl : ℕ) : Height w128 := if cl<40 then (if cl<6 then (h128_0) else (h128_1)) else (if cl<257 then (h128_2) else (if cl<984 then (h128_3) else (h128_4)))
private theorem k128_1_0 : check w128 pick128 1 t5570 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k128_1_1 : check w128 pick128 1 t5577 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k128_1_2 : check w128 pick128 1 t5578 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w128 pick128 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5570 t5577 k128_1_0 k128_1_1
private theorem k128_1_3 : check w128 pick128 1 t5744 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k128_1_4 : check w128 pick128 1 t5745 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k128_1_5 : check w128 pick128 1 t5746 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w128 pick128 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t5744 t5745 k128_1_3 k128_1_4
private theorem k128_1_6 : check w128 pick128 1 t5747 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w128 pick128 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5578 t5746 k128_1_2 k128_1_5
private theorem k128_1_7 : check w128 pick128 1 t5757 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k128_1_8 : check w128 pick128 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k128_1_9 : check w128 pick128 1 t5758 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w128 pick128 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t5757 t3123 k128_1_7 k128_1_8
private theorem k128_1_10 : check w128 pick128 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k128_1_11 : check w128 pick128 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k128_1_12 : check w128 pick128 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w128 pick128 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k128_1_10 k128_1_11
private theorem k128_1_13 : check w128 pick128 1 t5759 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w128 pick128 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5758 t1079 k128_1_9 k128_1_12
private theorem k128_1_14 : check w128 pick128 1 t5760 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w128 pick128 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5747 t5759 k128_1_6 k128_1_13
theorem cov128_1 : PA.Covered 1 (OZ.Valid 1 w128.low w128.t w128.y w128.r w128.cap) (P33.root 1) :=
  Night6836Tree.sound w128 pick128 1 t5760 _ k128_1_14
private theorem k128_2_0 : check w128 pick128 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k128_2_1 : check w128 pick128 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k128_2_2 : check w128 pick128 2 t5528 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w128 pick128 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t3303 k128_2_0 k128_2_1
theorem cov128_2 : PA.Covered 2 (OZ.Valid 2 w128.low w128.t w128.y w128.r w128.cap) (P33.root 2) :=
  Night6836Tree.sound w128 pick128 2 t5528 _ k128_2_2
theorem cov128_3 : PA.Covered 3 (OZ.Valid 3 w128.low w128.t w128.y w128.r w128.cap) (P33.root 3) :=
  Night6836Tree.sound w128 pick128 3 t564 _ (by decide +kernel)
theorem cov128_4 : PA.Covered 4 (OZ.Valid 4 w128.low w128.t w128.y w128.r w128.cap) (P33.root 4) :=
  Night6836Tree.sound w128 pick128 4 t565 _ (by decide +kernel)
theorem cov128_5 : PA.Covered 5 (OZ.Valid 5 w128.low w128.t w128.y w128.r w128.cap) (P33.root 5) :=
  Night6836Tree.sound w128 pick128 5 t566 _ (by decide +kernel)
theorem cov128_6 : PA.Covered 6 (OZ.Valid 6 w128.low w128.t w128.y w128.r w128.cap) (P33.root 6) :=
  Night6836Tree.sound w128 pick128 6 t567 _ (by decide +kernel)
theorem cov128_7 : PA.Covered 7 (OZ.Valid 7 w128.low w128.t w128.y w128.r w128.cap) (P33.root 7) :=
  Night6836Tree.sound w128 pick128 7 t2134 _ (by decide +kernel)
theorem window128 : P33.WindowCount w128 := by
  apply P33.window_count w128 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov128_1
  · exact cov128_2
  · exact cov128_3
  · exact cov128_4
  · exact cov128_5
  · exact cov128_6
  · exact cov128_7
def w129 : P33.Window := ⟨11,39,6850,6796,246955669470258782,25155,24000,5000000,81920000000⟩
def h129_0 : Height w129 := ⟨25155,24000,by decide +kernel⟩
def h129_1 : Height w129 := ⟨29547,21000,by decide +kernel⟩
def h129_2 : Height w129 := ⟨35678,18000,by decide +kernel⟩
def h129_3 : Height w129 := ⟨45781,15000,by decide +kernel⟩
def pick129 (cl : ℕ) : Height w129 := if cl<43 then (if cl<5 then (h129_0) else (h129_1)) else (if cl<531 then (h129_2) else (h129_3))
private theorem k129_1_0 : check w129 pick129 1 t5626 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k129_1_1 : check w129 pick129 1 t5714 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k129_1_2 : check w129 pick129 1 t5715 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w129 pick129 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5626 t5714 k129_1_0 k129_1_1
private theorem k129_1_3 : check w129 pick129 1 t3944 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k129_1_4 : check w129 pick129 1 t5666 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k129_1_5 : check w129 pick129 1 t5667 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w129 pick129 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3944 t5666 k129_1_3 k129_1_4
private theorem k129_1_6 : check w129 pick129 1 t5716 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w129 pick129 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5715 t5667 k129_1_2 k129_1_5
private theorem k129_1_7 : check w129 pick129 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k129_1_8 : check w129 pick129 1 t5783 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k129_1_9 : check w129 pick129 1 t5784 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w129 pick129 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t3594 t5783 k129_1_7 k129_1_8
private theorem k129_1_10 : check w129 pick129 1 t5790 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k129_1_11 : check w129 pick129 1 t4100 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k129_1_12 : check w129 pick129 1 t5791 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w129 pick129 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t5790 t4100 k129_1_10 k129_1_11
private theorem k129_1_13 : check w129 pick129 1 t5792 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w129 pick129 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t5784 t5791 k129_1_9 k129_1_12
private theorem k129_1_14 : check w129 pick129 1 t5793 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w129 pick129 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5716 t5792 k129_1_6 k129_1_13
theorem cov129_1 : PA.Covered 1 (OZ.Valid 1 w129.low w129.t w129.y w129.r w129.cap) (P33.root 1) :=
  Night6836Tree.sound w129 pick129 1 t5793 _ k129_1_14
private theorem k129_2_0 : check w129 pick129 2 t5795 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k129_2_1 : check w129 pick129 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k129_2_2 : check w129 pick129 2 t5796 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w129 pick129 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5795 t4131 k129_2_0 k129_2_1
private theorem k129_2_3 : check w129 pick129 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k129_2_4 : check w129 pick129 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k129_2_5 : check w129 pick129 2 t4141 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w129 pick129 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t4033 k129_2_3 k129_2_4
private theorem k129_2_6 : check w129 pick129 2 t5797 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w129 pick129 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5796 t4141 k129_2_2 k129_2_5
theorem cov129_2 : PA.Covered 2 (OZ.Valid 2 w129.low w129.t w129.y w129.r w129.cap) (P33.root 2) :=
  Night6836Tree.sound w129 pick129 2 t5797 _ k129_2_6
theorem cov129_3 : PA.Covered 3 (OZ.Valid 3 w129.low w129.t w129.y w129.r w129.cap) (P33.root 3) :=
  Night6836Tree.sound w129 pick129 3 t4151 _ (by decide +kernel)
theorem cov129_4 : PA.Covered 4 (OZ.Valid 4 w129.low w129.t w129.y w129.r w129.cap) (P33.root 4) :=
  Night6836Tree.sound w129 pick129 4 t565 _ (by decide +kernel)
theorem cov129_5 : PA.Covered 5 (OZ.Valid 5 w129.low w129.t w129.y w129.r w129.cap) (P33.root 5) :=
  Night6836Tree.sound w129 pick129 5 t566 _ (by decide +kernel)
theorem cov129_6 : PA.Covered 6 (OZ.Valid 6 w129.low w129.t w129.y w129.r w129.cap) (P33.root 6) :=
  Night6836Tree.sound w129 pick129 6 t567 _ (by decide +kernel)
theorem cov129_7 : PA.Covered 7 (OZ.Valid 7 w129.low w129.t w129.y w129.r w129.cap) (P33.root 7) :=
  Night6836Tree.sound w129 pick129 7 t568 _ (by decide +kernel)
theorem window129 : P33.WindowCount w129 := by
  apply P33.window_count w129 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov129_1
  · exact cov129_2
  · exact cov129_3
  · exact cov129_4
  · exact cov129_5
  · exact cov129_6
  · exact cov129_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w130 : P33.Window := ⟨11,40,6556,5607,245921879200227300,30667,30000,5000000,81920000000⟩
def h130_0 : Height w130 := ⟨30667,30000,by decide +kernel⟩
def h130_1 : Height w130 := ⟨34752,27000,by decide +kernel⟩
def h130_2 : Height w130 := ⟨39922,24000,by decide +kernel⟩
def h130_3 : Height w130 := ⟨47039,21000,by decide +kernel⟩
def h130_4 : Height w130 := ⟨58204,18000,by decide +kernel⟩
def pick130 (cl : ℕ) : Height w130 := if cl<18 then (if cl<2 then (h130_0) else (h130_1)) else (if cl<100 then (h130_2) else (if cl<853 then (h130_3) else (h130_4)))
private theorem k130_1_0 : check w130 pick130 1 t5626 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k130_1_1 : check w130 pick130 1 t5714 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k130_1_2 : check w130 pick130 1 t5715 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w130 pick130 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5626 t5714 k130_1_0 k130_1_1
private theorem k130_1_3 : check w130 pick130 1 t3944 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k130_1_4 : check w130 pick130 1 t5666 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k130_1_5 : check w130 pick130 1 t5667 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w130 pick130 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3944 t5666 k130_1_3 k130_1_4
private theorem k130_1_6 : check w130 pick130 1 t5716 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w130 pick130 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5715 t5667 k130_1_2 k130_1_5
private theorem k130_1_7 : check w130 pick130 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k130_1_8 : check w130 pick130 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k130_1_9 : check w130 pick130 1 t3616 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w130 pick130 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t3615 k130_1_7 k130_1_8
private theorem k130_1_10 : check w130 pick130 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k130_1_11 : check w130 pick130 1 t3405 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k130_1_12 : check w130 pick130 1 t3656 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w130 pick130 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t3405 k130_1_10 k130_1_11
private theorem k130_1_13 : check w130 pick130 1 t3657 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w130 pick130 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3616 t3656 k130_1_9 k130_1_12
private theorem k130_1_14 : check w130 pick130 1 t5717 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w130 pick130 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5716 t3657 k130_1_6 k130_1_13
theorem cov130_1 : PA.Covered 1 (OZ.Valid 1 w130.low w130.t w130.y w130.r w130.cap) (P33.root 1) :=
  Night6836Tree.sound w130 pick130 1 t5717 _ k130_1_14
private theorem k130_2_0 : check w130 pick130 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k130_2_1 : check w130 pick130 2 t5736 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k130_2_2 : check w130 pick130 2 t5737 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w130 pick130 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5736 k130_2_0 k130_2_1
private theorem k130_2_3 : check w130 pick130 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k130_2_4 : check w130 pick130 2 t5800 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k130_2_5 : check w130 pick130 2 t5801 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w130 pick130 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t5800 k130_2_3 k130_2_4
private theorem k130_2_6 : check w130 pick130 2 t5802 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w130 pick130 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5737 t5801 k130_2_2 k130_2_5
theorem cov130_2 : PA.Covered 2 (OZ.Valid 2 w130.low w130.t w130.y w130.r w130.cap) (P33.root 2) :=
  Night6836Tree.sound w130 pick130 2 t5802 _ k130_2_6
theorem cov130_3 : PA.Covered 3 (OZ.Valid 3 w130.low w130.t w130.y w130.r w130.cap) (P33.root 3) :=
  Night6836Tree.sound w130 pick130 3 t564 _ (by decide +kernel)
theorem cov130_4 : PA.Covered 4 (OZ.Valid 4 w130.low w130.t w130.y w130.r w130.cap) (P33.root 4) :=
  Night6836Tree.sound w130 pick130 4 t565 _ (by decide +kernel)
theorem cov130_5 : PA.Covered 5 (OZ.Valid 5 w130.low w130.t w130.y w130.r w130.cap) (P33.root 5) :=
  Night6836Tree.sound w130 pick130 5 t566 _ (by decide +kernel)
theorem cov130_6 : PA.Covered 6 (OZ.Valid 6 w130.low w130.t w130.y w130.r w130.cap) (P33.root 6) :=
  Night6836Tree.sound w130 pick130 6 t567 _ (by decide +kernel)
theorem cov130_7 : PA.Covered 7 (OZ.Valid 7 w130.low w130.t w130.y w130.r w130.cap) (P33.root 7) :=
  Night6836Tree.sound w130 pick130 7 t568 _ (by decide +kernel)
theorem window130 : P33.WindowCount w130 := by
  apply P33.window_count w130 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov130_1
  · exact cov130_2
  · exact cov130_3
  · exact cov130_4
  · exact cov130_5
  · exact cov130_6
  · exact cov130_7
def w131 : P33.Window := ⟨11,40,6795,6400,245983530647980802,26007,27000,5000000,81920000000⟩
def h131_0 : Height w131 := ⟨26007,27000,by decide +kernel⟩
def h131_1 : Height w131 := ⟨29939,24000,by decide +kernel⟩
def h131_2 : Height w131 := ⟨35039,21000,by decide +kernel⟩
def h131_3 : Height w131 := ⟨42415,18000,by decide +kernel⟩
def h131_4 : Height w131 := ⟨55202,15000,by decide +kernel⟩
def pick131 (cl : ℕ) : Height w131 := if cl<18 then (if cl<2 then (h131_0) else (h131_1)) else (if cl<117 then (h131_2) else (if cl<961 then (h131_3) else (h131_4)))
private theorem k131_1_0 : check w131 pick131 1 t5803 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k131_1_1 : check w131 pick131 1 t5714 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k131_1_2 : check w131 pick131 1 t5804 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w131 pick131 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5803 t5714 k131_1_0 k131_1_1
private theorem k131_1_3 : check w131 pick131 1 t5812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k131_1_4 : check w131 pick131 1 t5821 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k131_1_5 : check w131 pick131 1 t5822 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w131 pick131 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t5812 t5821 k131_1_3 k131_1_4
private theorem k131_1_6 : check w131 pick131 1 t5823 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w131 pick131 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5804 t5822 k131_1_2 k131_1_5
private theorem k131_1_7 : check w131 pick131 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k131_1_8 : check w131 pick131 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k131_1_9 : check w131 pick131 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w131 pick131 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k131_1_7 k131_1_8
private theorem k131_1_10 : check w131 pick131 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k131_1_11 : check w131 pick131 1 t4100 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k131_1_12 : check w131 pick131 1 t4101 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w131 pick131 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4100 k131_1_10 k131_1_11
private theorem k131_1_13 : check w131 pick131 1 t4102 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w131 pick131 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4101 k131_1_9 k131_1_12
private theorem k131_1_14 : check w131 pick131 1 t5824 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w131 pick131 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5823 t4102 k131_1_6 k131_1_13
theorem cov131_1 : PA.Covered 1 (OZ.Valid 1 w131.low w131.t w131.y w131.r w131.cap) (P33.root 1) :=
  Night6836Tree.sound w131 pick131 1 t5824 _ k131_1_14
private theorem k131_2_0 : check w131 pick131 2 t5829 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k131_2_1 : check w131 pick131 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k131_2_2 : check w131 pick131 2 t5830 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w131 pick131 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5829 t4131 k131_2_0 k131_2_1
private theorem k131_2_3 : check w131 pick131 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k131_2_4 : check w131 pick131 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k131_2_5 : check w131 pick131 2 t4141 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w131 pick131 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t4033 k131_2_3 k131_2_4
private theorem k131_2_6 : check w131 pick131 2 t5831 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w131 pick131 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5830 t4141 k131_2_2 k131_2_5
theorem cov131_2 : PA.Covered 2 (OZ.Valid 2 w131.low w131.t w131.y w131.r w131.cap) (P33.root 2) :=
  Night6836Tree.sound w131 pick131 2 t5831 _ k131_2_6
theorem cov131_3 : PA.Covered 3 (OZ.Valid 3 w131.low w131.t w131.y w131.r w131.cap) (P33.root 3) :=
  Night6836Tree.sound w131 pick131 3 t4151 _ (by decide +kernel)
theorem cov131_4 : PA.Covered 4 (OZ.Valid 4 w131.low w131.t w131.y w131.r w131.cap) (P33.root 4) :=
  Night6836Tree.sound w131 pick131 4 t565 _ (by decide +kernel)
theorem cov131_5 : PA.Covered 5 (OZ.Valid 5 w131.low w131.t w131.y w131.r w131.cap) (P33.root 5) :=
  Night6836Tree.sound w131 pick131 5 t566 _ (by decide +kernel)
theorem cov131_6 : PA.Covered 6 (OZ.Valid 6 w131.low w131.t w131.y w131.r w131.cap) (P33.root 6) :=
  Night6836Tree.sound w131 pick131 6 t567 _ (by decide +kernel)
theorem cov131_7 : PA.Covered 7 (OZ.Valid 7 w131.low w131.t w131.y w131.r w131.cap) (P33.root 7) :=
  Night6836Tree.sound w131 pick131 7 t568 _ (by decide +kernel)
theorem window131 : P33.WindowCount w131 := by
  apply P33.window_count w131 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov131_1
  · exact cov131_2
  · exact cov131_3
  · exact cov131_4
  · exact cov131_5
  · exact cov131_6
  · exact cov131_7
def w132 : P33.Window := ⟨11,41,6731,5782,245908797876583008,29911,30000,5000000,81920000000⟩
def h132_0 : Height w132 := ⟨29911,30000,by decide +kernel⟩
def h132_1 : Height w132 := ⟨33836,27000,by decide +kernel⟩
def h132_2 : Height w132 := ⟨38757,24000,by decide +kernel⟩
def h132_3 : Height w132 := ⟨45448,21000,by decide +kernel⟩
def h132_4 : Height w132 := ⟨55756,18000,by decide +kernel⟩
def h132_5 : Height w132 := ⟨75426,15000,by decide +kernel⟩
def pick132 (cl : ℕ) : Height w132 := if cl<72 then (if cl<2 then (h132_0) else (if cl<12 then (h132_1) else (h132_2))) else (if cl<644 then (h132_3) else (if cl<1026 then (h132_4) else (h132_5)))
private theorem k132_1_0 : check w132 pick132 1 t5833 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k132_1_1 : check w132 pick132 1 t5838 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k132_1_2 : check w132 pick132 1 t5839 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w132 pick132 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5833 t5838 k132_1_0 k132_1_1
private theorem k132_1_3 : check w132 pick132 1 t4569 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k132_1_4 : check w132 pick132 1 t5857 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k132_1_5 : check w132 pick132 1 t5858 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w132 pick132 1 ⟨1,7,2,16,1,52,70,131⟩ 3 104 t4569 t5857 k132_1_3 k132_1_4
private theorem k132_1_6 : check w132 pick132 1 t5859 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w132 pick132 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5839 t5858 k132_1_2 k132_1_5
private theorem k132_1_7 : check w132 pick132 1 t5866 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k132_1_8 : check w132 pick132 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k132_1_9 : check w132 pick132 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k132_1_10 : check w132 pick132 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w132 pick132 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k132_1_8 k132_1_9
private theorem k132_1_11 : check w132 pick132 1 t5867 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w132 pick132 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t5866 t4432 k132_1_7 k132_1_10
private theorem k132_1_12 : check w132 pick132 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k132_1_13 : check w132 pick132 1 t4100 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k132_1_14 : check w132 pick132 1 t4101 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w132 pick132 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4100 k132_1_12 k132_1_13
private theorem k132_1_15 : check w132 pick132 1 t5868 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w132 pick132 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5867 t4101 k132_1_11 k132_1_14
private theorem k132_1_16 : check w132 pick132 1 t5869 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w132 pick132 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5859 t5868 k132_1_6 k132_1_15
theorem cov132_1 : PA.Covered 1 (OZ.Valid 1 w132.low w132.t w132.y w132.r w132.cap) (P33.root 1) :=
  Night6836Tree.sound w132 pick132 1 t5869 _ k132_1_16
private theorem k132_2_0 : check w132 pick132 2 t5829 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k132_2_1 : check w132 pick132 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k132_2_2 : check w132 pick132 2 t5830 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w132 pick132 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5829 t4131 k132_2_0 k132_2_1
private theorem k132_2_3 : check w132 pick132 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k132_2_4 : check w132 pick132 2 t5886 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k132_2_5 : check w132 pick132 2 t5887 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w132 pick132 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t5886 k132_2_3 k132_2_4
private theorem k132_2_6 : check w132 pick132 2 t5888 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w132 pick132 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5830 t5887 k132_2_2 k132_2_5
theorem cov132_2 : PA.Covered 2 (OZ.Valid 2 w132.low w132.t w132.y w132.r w132.cap) (P33.root 2) :=
  Night6836Tree.sound w132 pick132 2 t5888 _ k132_2_6
theorem cov132_3 : PA.Covered 3 (OZ.Valid 3 w132.low w132.t w132.y w132.r w132.cap) (P33.root 3) :=
  Night6836Tree.sound w132 pick132 3 t4231 _ (by decide +kernel)
theorem cov132_4 : PA.Covered 4 (OZ.Valid 4 w132.low w132.t w132.y w132.r w132.cap) (P33.root 4) :=
  Night6836Tree.sound w132 pick132 4 t565 _ (by decide +kernel)
theorem cov132_5 : PA.Covered 5 (OZ.Valid 5 w132.low w132.t w132.y w132.r w132.cap) (P33.root 5) :=
  Night6836Tree.sound w132 pick132 5 t566 _ (by decide +kernel)
theorem cov132_6 : PA.Covered 6 (OZ.Valid 6 w132.low w132.t w132.y w132.r w132.cap) (P33.root 6) :=
  Night6836Tree.sound w132 pick132 6 t567 _ (by decide +kernel)
theorem cov132_7 : PA.Covered 7 (OZ.Valid 7 w132.low w132.t w132.y w132.r w132.cap) (P33.root 7) :=
  Night6836Tree.sound w132 pick132 7 t568 _ (by decide +kernel)
theorem window132 : P33.WindowCount w132 := by
  apply P33.window_count w132 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov132_1
  · exact cov132_2
  · exact cov132_3
  · exact cov132_4
  · exact cov132_5
  · exact cov132_6
  · exact cov132_7
def w133 : P33.Window := ⟨11,41,6738,6673,247133362054875931,28471,24000,5000000,81920000000⟩
def h133_0 : Height w133 := ⟨28471,24000,by decide +kernel⟩
def h133_1 : Height w133 := ⟨33214,21000,by decide +kernel⟩
def h133_2 : Height w133 := ⟨39934,18000,by decide +kernel⟩
def h133_3 : Height w133 := ⟨51223,15000,by decide +kernel⟩
def pick133 (cl : ℕ) : Height w133 := if cl<73 then (if cl<10 then (h133_0) else (h133_1)) else (if cl<853 then (h133_2) else (h133_3))
private theorem k133_1_0 : check w133 pick133 1 t5803 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k133_1_1 : check w133 pick133 1 t5893 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k133_1_2 : check w133 pick133 1 t5894 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w133 pick133 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5803 t5893 k133_1_0 k133_1_1
private theorem k133_1_3 : check w133 pick133 1 t4171 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k133_1_4 : check w133 pick133 1 t4174 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k133_1_5 : check w133 pick133 1 t4175 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w133 pick133 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4171 t4174 k133_1_3 k133_1_4
private theorem k133_1_6 : check w133 pick133 1 t5821 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k133_1_7 : check w133 pick133 1 t5895 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w133 pick133 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4175 t5821 k133_1_5 k133_1_6
private theorem k133_1_8 : check w133 pick133 1 t5896 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w133 pick133 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5894 t5895 k133_1_2 k133_1_7
private theorem k133_1_9 : check w133 pick133 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k133_1_10 : check w133 pick133 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k133_1_11 : check w133 pick133 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w133 pick133 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k133_1_9 k133_1_10
private theorem k133_1_12 : check w133 pick133 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k133_1_13 : check w133 pick133 1 t4100 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k133_1_14 : check w133 pick133 1 t4101 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w133 pick133 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4100 k133_1_12 k133_1_13
private theorem k133_1_15 : check w133 pick133 1 t4102 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w133 pick133 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4101 k133_1_11 k133_1_14
private theorem k133_1_16 : check w133 pick133 1 t5897 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w133 pick133 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5896 t4102 k133_1_8 k133_1_15
theorem cov133_1 : PA.Covered 1 (OZ.Valid 1 w133.low w133.t w133.y w133.r w133.cap) (P33.root 1) :=
  Night6836Tree.sound w133 pick133 1 t5897 _ k133_1_16
private theorem k133_2_0 : check w133 pick133 2 t5829 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k133_2_1 : check w133 pick133 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k133_2_2 : check w133 pick133 2 t5830 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w133 pick133 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5829 t4131 k133_2_0 k133_2_1
private theorem k133_2_3 : check w133 pick133 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k133_2_4 : check w133 pick133 2 t5898 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k133_2_5 : check w133 pick133 2 t5899 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w133 pick133 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t5898 k133_2_3 k133_2_4
private theorem k133_2_6 : check w133 pick133 2 t5900 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w133 pick133 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5830 t5899 k133_2_2 k133_2_5
theorem cov133_2 : PA.Covered 2 (OZ.Valid 2 w133.low w133.t w133.y w133.r w133.cap) (P33.root 2) :=
  Night6836Tree.sound w133 pick133 2 t5900 _ k133_2_6
theorem cov133_3 : PA.Covered 3 (OZ.Valid 3 w133.low w133.t w133.y w133.r w133.cap) (P33.root 3) :=
  Night6836Tree.sound w133 pick133 3 t4231 _ (by decide +kernel)
theorem cov133_4 : PA.Covered 4 (OZ.Valid 4 w133.low w133.t w133.y w133.r w133.cap) (P33.root 4) :=
  Night6836Tree.sound w133 pick133 4 t565 _ (by decide +kernel)
theorem cov133_5 : PA.Covered 5 (OZ.Valid 5 w133.low w133.t w133.y w133.r w133.cap) (P33.root 5) :=
  Night6836Tree.sound w133 pick133 5 t566 _ (by decide +kernel)
theorem cov133_6 : PA.Covered 6 (OZ.Valid 6 w133.low w133.t w133.y w133.r w133.cap) (P33.root 6) :=
  Night6836Tree.sound w133 pick133 6 t567 _ (by decide +kernel)
theorem cov133_7 : PA.Covered 7 (OZ.Valid 7 w133.low w133.t w133.y w133.r w133.cap) (P33.root 7) :=
  Night6836Tree.sound w133 pick133 7 t568 _ (by decide +kernel)
theorem window133 : P33.WindowCount w133 := by
  apply P33.window_count w133 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov133_1
  · exact cov133_2
  · exact cov133_3
  · exact cov133_4
  · exact cov133_5
  · exact cov133_6
  · exact cov133_7
def w134 : P33.Window := ⟨11,42,4889,3940,240691265522432761,48264,42000,5000000,81920000000⟩
def h134_0 : Height w134 := ⟨48264,42000,by decide +kernel⟩
def h134_1 : Height w134 := ⟨52489,39000,by decide +kernel⟩
def h134_2 : Height w134 := ⟨57448,36000,by decide +kernel⟩
def h134_3 : Height w134 := ⟨63484,33000,by decide +kernel⟩
def h134_4 : Height w134 := ⟨71189,30000,by decide +kernel⟩
def h134_5 : Height w134 := ⟨81690,27000,by decide +kernel⟩
def pick134 (cl : ℕ) : Height w134 := if cl<40 then (if cl<4 then (h134_0) else (if cl<13 then (h134_1) else (h134_2))) else (if cl<165 then (h134_3) else (if cl<685 then (h134_4) else (h134_5)))
private theorem k134_1_0 : check w134 pick134 1 t52 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k134_1_1 : check w134 pick134 1 t5340 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k134_1_2 : check w134 pick134 1 t5901 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w134 pick134 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t52 t5340 k134_1_0 k134_1_1
private theorem k134_1_3 : check w134 pick134 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k134_1_4 : check w134 pick134 1 t5307 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k134_1_5 : check w134 pick134 1 t5902 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w134 pick134 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t5307 k134_1_3 k134_1_4
private theorem k134_1_6 : check w134 pick134 1 t5903 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w134 pick134 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5901 t5902 k134_1_2 k134_1_5
private theorem k134_1_7 : check w134 pick134 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k134_1_8 : check w134 pick134 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k134_1_9 : check w134 pick134 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w134 pick134 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k134_1_7 k134_1_8
private theorem k134_1_10 : check w134 pick134 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k134_1_11 : check w134 pick134 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k134_1_12 : check w134 pick134 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w134 pick134 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k134_1_10 k134_1_11
private theorem k134_1_13 : check w134 pick134 1 t2461 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w134 pick134 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t499 k134_1_9 k134_1_12
private theorem k134_1_14 : check w134 pick134 1 t5904 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w134 pick134 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5903 t2461 k134_1_6 k134_1_13
theorem cov134_1 : PA.Covered 1 (OZ.Valid 1 w134.low w134.t w134.y w134.r w134.cap) (P33.root 1) :=
  Night6836Tree.sound w134 pick134 1 t5904 _ k134_1_14
theorem cov134_2 : PA.Covered 2 (OZ.Valid 2 w134.low w134.t w134.y w134.r w134.cap) (P33.root 2) :=
  Night6836Tree.sound w134 pick134 2 t5320 _ (by decide +kernel)
theorem cov134_3 : PA.Covered 3 (OZ.Valid 3 w134.low w134.t w134.y w134.r w134.cap) (P33.root 3) :=
  Night6836Tree.sound w134 pick134 3 t564 _ (by decide +kernel)
theorem cov134_4 : PA.Covered 4 (OZ.Valid 4 w134.low w134.t w134.y w134.r w134.cap) (P33.root 4) :=
  Night6836Tree.sound w134 pick134 4 t565 _ (by decide +kernel)
theorem cov134_5 : PA.Covered 5 (OZ.Valid 5 w134.low w134.t w134.y w134.r w134.cap) (P33.root 5) :=
  Night6836Tree.sound w134 pick134 5 t566 _ (by decide +kernel)
theorem cov134_6 : PA.Covered 6 (OZ.Valid 6 w134.low w134.t w134.y w134.r w134.cap) (P33.root 6) :=
  Night6836Tree.sound w134 pick134 6 t567 _ (by decide +kernel)
theorem cov134_7 : PA.Covered 7 (OZ.Valid 7 w134.low w134.t w134.y w134.r w134.cap) (P33.root 7) :=
  Night6836Tree.sound w134 pick134 7 t2134 _ (by decide +kernel)
theorem window134 : P33.WindowCount w134 := by
  apply P33.window_count w134 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov134_1
  · exact cov134_2
  · exact cov134_3
  · exact cov134_4
  · exact cov134_5
  · exact cov134_6
  · exact cov134_7
def w135 : P33.Window := ⟨11,42,6672,6455,247220247481296842,27774,27000,5000000,81920000000⟩
def h135_0 : Height w135 := ⟨27774,27000,by decide +kernel⟩
def h135_1 : Height w135 := ⟨31780,24000,by decide +kernel⟩
def h135_2 : Height w135 := ⟨36984,21000,by decide +kernel⟩
def h135_3 : Height w135 := ⟨44508,18000,by decide +kernel⟩
def h135_4 : Height w135 := ⟨57517,15000,by decide +kernel⟩
def pick135 (cl : ℕ) : Height w135 := if cl<20 then (if cl<2 then (h135_0) else (h135_1)) else (if cl<135 then (h135_2) else (if cl<961 then (h135_3) else (h135_4)))
private theorem k135_1_0 : check w135 pick135 1 t5833 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k135_1_1 : check w135 pick135 1 t5893 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k135_1_2 : check w135 pick135 1 t5905 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w135 pick135 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5833 t5893 k135_1_0 k135_1_1
private theorem k135_1_3 : check w135 pick135 1 t4171 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k135_1_4 : check w135 pick135 1 t4174 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k135_1_5 : check w135 pick135 1 t4175 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w135 pick135 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4171 t4174 k135_1_3 k135_1_4
private theorem k135_1_6 : check w135 pick135 1 t5821 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k135_1_7 : check w135 pick135 1 t5895 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w135 pick135 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4175 t5821 k135_1_5 k135_1_6
private theorem k135_1_8 : check w135 pick135 1 t5906 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w135 pick135 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5905 t5895 k135_1_2 k135_1_7
private theorem k135_1_9 : check w135 pick135 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k135_1_10 : check w135 pick135 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k135_1_11 : check w135 pick135 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w135 pick135 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k135_1_9 k135_1_10
private theorem k135_1_12 : check w135 pick135 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k135_1_13 : check w135 pick135 1 t4100 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k135_1_14 : check w135 pick135 1 t4101 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w135 pick135 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4100 k135_1_12 k135_1_13
private theorem k135_1_15 : check w135 pick135 1 t4102 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w135 pick135 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4101 k135_1_11 k135_1_14
private theorem k135_1_16 : check w135 pick135 1 t5907 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w135 pick135 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5906 t4102 k135_1_8 k135_1_15
theorem cov135_1 : PA.Covered 1 (OZ.Valid 1 w135.low w135.t w135.y w135.r w135.cap) (P33.root 1) :=
  Night6836Tree.sound w135 pick135 1 t5907 _ k135_1_16
private theorem k135_2_0 : check w135 pick135 2 t5829 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k135_2_1 : check w135 pick135 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k135_2_2 : check w135 pick135 2 t5830 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w135 pick135 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5829 t4131 k135_2_0 k135_2_1
private theorem k135_2_3 : check w135 pick135 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k135_2_4 : check w135 pick135 2 t5912 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k135_2_5 : check w135 pick135 2 t5913 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w135 pick135 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t5912 k135_2_3 k135_2_4
private theorem k135_2_6 : check w135 pick135 2 t5914 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w135 pick135 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5830 t5913 k135_2_2 k135_2_5
theorem cov135_2 : PA.Covered 2 (OZ.Valid 2 w135.low w135.t w135.y w135.r w135.cap) (P33.root 2) :=
  Night6836Tree.sound w135 pick135 2 t5914 _ k135_2_6
theorem cov135_3 : PA.Covered 3 (OZ.Valid 3 w135.low w135.t w135.y w135.r w135.cap) (P33.root 3) :=
  Night6836Tree.sound w135 pick135 3 t4231 _ (by decide +kernel)
theorem cov135_4 : PA.Covered 4 (OZ.Valid 4 w135.low w135.t w135.y w135.r w135.cap) (P33.root 4) :=
  Night6836Tree.sound w135 pick135 4 t565 _ (by decide +kernel)
theorem cov135_5 : PA.Covered 5 (OZ.Valid 5 w135.low w135.t w135.y w135.r w135.cap) (P33.root 5) :=
  Night6836Tree.sound w135 pick135 5 t566 _ (by decide +kernel)
theorem cov135_6 : PA.Covered 6 (OZ.Valid 6 w135.low w135.t w135.y w135.r w135.cap) (P33.root 6) :=
  Night6836Tree.sound w135 pick135 6 t567 _ (by decide +kernel)
theorem cov135_7 : PA.Covered 7 (OZ.Valid 7 w135.low w135.t w135.y w135.r w135.cap) (P33.root 7) :=
  Night6836Tree.sound w135 pick135 7 t568 _ (by decide +kernel)
theorem window135 : P33.WindowCount w135 := by
  apply P33.window_count w135 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov135_1
  · exact cov135_2
  · exact cov135_3
  · exact cov135_4
  · exact cov135_5
  · exact cov135_6
  · exact cov135_7
def w136 : P33.Window := ⟨11,42,6672,6606,246951085548712819,30253,24000,5000000,81920000000⟩
def h136_0 : Height w136 := ⟨30253,24000,by decide +kernel⟩
def h136_1 : Height w136 := ⟨35194,21000,by decide +kernel⟩
def h136_2 : Height w136 := ⟨42249,18000,by decide +kernel⟩
def h136_3 : Height w136 := ⟨54223,15000,by decide +kernel⟩
def pick136 (cl : ℕ) : Height w136 := if cl<97 then (if cl<13 then (h136_0) else (h136_1)) else (if cl<922 then (h136_2) else (h136_3))
private theorem k136_1_0 : check w136 pick136 1 t5833 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k136_1_1 : check w136 pick136 1 t5893 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k136_1_2 : check w136 pick136 1 t5905 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w136 pick136 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5833 t5893 k136_1_0 k136_1_1
private theorem k136_1_3 : check w136 pick136 1 t4171 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k136_1_4 : check w136 pick136 1 t4174 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k136_1_5 : check w136 pick136 1 t4175 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w136 pick136 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4171 t4174 k136_1_3 k136_1_4
private theorem k136_1_6 : check w136 pick136 1 t5821 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k136_1_7 : check w136 pick136 1 t5895 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w136 pick136 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4175 t5821 k136_1_5 k136_1_6
private theorem k136_1_8 : check w136 pick136 1 t5906 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w136 pick136 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5905 t5895 k136_1_2 k136_1_7
private theorem k136_1_9 : check w136 pick136 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k136_1_10 : check w136 pick136 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k136_1_11 : check w136 pick136 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w136 pick136 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k136_1_9 k136_1_10
private theorem k136_1_12 : check w136 pick136 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k136_1_13 : check w136 pick136 1 t4100 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k136_1_14 : check w136 pick136 1 t4101 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w136 pick136 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4100 k136_1_12 k136_1_13
private theorem k136_1_15 : check w136 pick136 1 t4102 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w136 pick136 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4101 k136_1_11 k136_1_14
private theorem k136_1_16 : check w136 pick136 1 t5907 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w136 pick136 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5906 t4102 k136_1_8 k136_1_15
theorem cov136_1 : PA.Covered 1 (OZ.Valid 1 w136.low w136.t w136.y w136.r w136.cap) (P33.root 1) :=
  Night6836Tree.sound w136 pick136 1 t5907 _ k136_1_16
private theorem k136_2_0 : check w136 pick136 2 t5829 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k136_2_1 : check w136 pick136 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k136_2_2 : check w136 pick136 2 t5830 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w136 pick136 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5829 t4131 k136_2_0 k136_2_1
private theorem k136_2_3 : check w136 pick136 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k136_2_4 : check w136 pick136 2 t5912 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k136_2_5 : check w136 pick136 2 t5913 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w136 pick136 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t5912 k136_2_3 k136_2_4
private theorem k136_2_6 : check w136 pick136 2 t5914 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w136 pick136 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5830 t5913 k136_2_2 k136_2_5
theorem cov136_2 : PA.Covered 2 (OZ.Valid 2 w136.low w136.t w136.y w136.r w136.cap) (P33.root 2) :=
  Night6836Tree.sound w136 pick136 2 t5914 _ k136_2_6
theorem cov136_3 : PA.Covered 3 (OZ.Valid 3 w136.low w136.t w136.y w136.r w136.cap) (P33.root 3) :=
  Night6836Tree.sound w136 pick136 3 t4231 _ (by decide +kernel)
theorem cov136_4 : PA.Covered 4 (OZ.Valid 4 w136.low w136.t w136.y w136.r w136.cap) (P33.root 4) :=
  Night6836Tree.sound w136 pick136 4 t565 _ (by decide +kernel)
theorem cov136_5 : PA.Covered 5 (OZ.Valid 5 w136.low w136.t w136.y w136.r w136.cap) (P33.root 5) :=
  Night6836Tree.sound w136 pick136 5 t566 _ (by decide +kernel)
theorem cov136_6 : PA.Covered 6 (OZ.Valid 6 w136.low w136.t w136.y w136.r w136.cap) (P33.root 6) :=
  Night6836Tree.sound w136 pick136 6 t567 _ (by decide +kernel)
theorem cov136_7 : PA.Covered 7 (OZ.Valid 7 w136.low w136.t w136.y w136.r w136.cap) (P33.root 7) :=
  Night6836Tree.sound w136 pick136 7 t568 _ (by decide +kernel)
theorem window136 : P33.WindowCount w136 := by
  apply P33.window_count w136 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov136_1
  · exact cov136_2
  · exact cov136_3
  · exact cov136_4
  · exact cov136_5
  · exact cov136_6
  · exact cov136_7
def w137 : P33.Window := ⟨11,43,6605,6537,247094724735366092,28132,27000,5000000,81920000000⟩
def h137_0 : Height w137 := ⟨28132,27000,by decide +kernel⟩
def h137_1 : Height w137 := ⟨32111,24000,by decide +kernel⟩
def h137_2 : Height w137 := ⟨37265,21000,by decide +kernel⟩
def h137_3 : Height w137 := ⟨44683,18000,by decide +kernel⟩
def h137_4 : Height w137 := ⟨57403,15000,by decide +kernel⟩
def pick137 (cl : ℕ) : Height w137 := if cl<18 then (if cl<2 then (h137_0) else (h137_1)) else (if cl<126 then (h137_2) else (if cl<947 then (h137_3) else (h137_4)))
private theorem k137_1_0 : check w137 pick137 1 t5833 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k137_1_1 : check w137 pick137 1 t5919 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k137_1_2 : check w137 pick137 1 t5920 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w137 pick137 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5833 t5919 k137_1_0 k137_1_1
private theorem k137_1_3 : check w137 pick137 1 t4171 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k137_1_4 : check w137 pick137 1 t4174 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k137_1_5 : check w137 pick137 1 t4175 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w137 pick137 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4171 t4174 k137_1_3 k137_1_4
private theorem k137_1_6 : check w137 pick137 1 t5821 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k137_1_7 : check w137 pick137 1 t5895 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w137 pick137 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4175 t5821 k137_1_5 k137_1_6
private theorem k137_1_8 : check w137 pick137 1 t5921 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w137 pick137 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5920 t5895 k137_1_2 k137_1_7
private theorem k137_1_9 : check w137 pick137 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k137_1_10 : check w137 pick137 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k137_1_11 : check w137 pick137 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w137 pick137 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k137_1_9 k137_1_10
private theorem k137_1_12 : check w137 pick137 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k137_1_13 : check w137 pick137 1 t4100 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k137_1_14 : check w137 pick137 1 t4101 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w137 pick137 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4100 k137_1_12 k137_1_13
private theorem k137_1_15 : check w137 pick137 1 t4102 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w137 pick137 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4101 k137_1_11 k137_1_14
private theorem k137_1_16 : check w137 pick137 1 t5922 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w137 pick137 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5921 t4102 k137_1_8 k137_1_15
theorem cov137_1 : PA.Covered 1 (OZ.Valid 1 w137.low w137.t w137.y w137.r w137.cap) (P33.root 1) :=
  Night6836Tree.sound w137 pick137 1 t5922 _ k137_1_16
private theorem k137_2_0 : check w137 pick137 2 t5936 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k137_2_1 : check w137 pick137 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k137_2_2 : check w137 pick137 2 t5937 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w137 pick137 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5936 t4131 k137_2_0 k137_2_1
private theorem k137_2_3 : check w137 pick137 2 t5938 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k137_2_4 : check w137 pick137 2 t5912 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k137_2_5 : check w137 pick137 2 t5939 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w137 pick137 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t5938 t5912 k137_2_3 k137_2_4
private theorem k137_2_6 : check w137 pick137 2 t5940 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w137 pick137 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5937 t5939 k137_2_2 k137_2_5
theorem cov137_2 : PA.Covered 2 (OZ.Valid 2 w137.low w137.t w137.y w137.r w137.cap) (P33.root 2) :=
  Night6836Tree.sound w137 pick137 2 t5940 _ k137_2_6
theorem cov137_3 : PA.Covered 3 (OZ.Valid 3 w137.low w137.t w137.y w137.r w137.cap) (P33.root 3) :=
  Night6836Tree.sound w137 pick137 3 t4231 _ (by decide +kernel)
theorem cov137_4 : PA.Covered 4 (OZ.Valid 4 w137.low w137.t w137.y w137.r w137.cap) (P33.root 4) :=
  Night6836Tree.sound w137 pick137 4 t565 _ (by decide +kernel)
theorem cov137_5 : PA.Covered 5 (OZ.Valid 5 w137.low w137.t w137.y w137.r w137.cap) (P33.root 5) :=
  Night6836Tree.sound w137 pick137 5 t566 _ (by decide +kernel)
theorem cov137_6 : PA.Covered 6 (OZ.Valid 6 w137.low w137.t w137.y w137.r w137.cap) (P33.root 6) :=
  Night6836Tree.sound w137 pick137 6 t567 _ (by decide +kernel)
theorem cov137_7 : PA.Covered 7 (OZ.Valid 7 w137.low w137.t w137.y w137.r w137.cap) (P33.root 7) :=
  Night6836Tree.sound w137 pick137 7 t568 _ (by decide +kernel)
theorem window137 : P33.WindowCount w137 := by
  apply P33.window_count w137 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov137_1
  · exact cov137_2
  · exact cov137_3
  · exact cov137_4
  · exact cov137_5
  · exact cov137_6
  · exact cov137_7
def w138 : P33.Window := ⟨11,44,6536,6455,247811242914863477,30031,27000,5000000,81920000000⟩
def h138_0 : Height w138 := ⟨30031,27000,by decide +kernel⟩
def h138_1 : Height w138 := ⟨34174,24000,by decide +kernel⟩
def h138_2 : Height w138 := ⟨39577,21000,by decide +kernel⟩
def h138_3 : Height w138 := ⟨47426,18000,by decide +kernel⟩
def h138_4 : Height w138 := ⟨61049,15000,by decide +kernel⟩
def pick138 (cl : ℕ) : Height w138 := if cl<23 then (if cl<3 then (h138_0) else (h138_1)) else (if cl<163 then (h138_2) else (if cl<966 then (h138_3) else (h138_4)))
private theorem k138_1_0 : check w138 pick138 1 t5833 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k138_1_1 : check w138 pick138 1 t5919 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k138_1_2 : check w138 pick138 1 t5920 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w138 pick138 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5833 t5919 k138_1_0 k138_1_1
private theorem k138_1_3 : check w138 pick138 1 t4171 ⟨1,7,2,5,1,52,77,110⟩ = true := by decide +kernel
private theorem k138_1_4 : check w138 pick138 1 t4174 ⟨1,7,6,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k138_1_5 : check w138 pick138 1 t4175 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w138 pick138 1 ⟨1,7,2,16,1,52,77,110⟩ 1 5 t4171 t4174 k138_1_3 k138_1_4
private theorem k138_1_6 : check w138 pick138 1 t5821 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k138_1_7 : check w138 pick138 1 t5895 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w138 pick138 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t4175 t5821 k138_1_5 k138_1_6
private theorem k138_1_8 : check w138 pick138 1 t5921 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w138 pick138 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t5920 t5895 k138_1_2 k138_1_7
private theorem k138_1_9 : check w138 pick138 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k138_1_10 : check w138 pick138 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k138_1_11 : check w138 pick138 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w138 pick138 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k138_1_9 k138_1_10
private theorem k138_1_12 : check w138 pick138 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k138_1_13 : check w138 pick138 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k138_1_14 : check w138 pick138 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w138 pick138 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k138_1_12 k138_1_13
private theorem k138_1_15 : check w138 pick138 1 t4180 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w138 pick138 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t4179 k138_1_11 k138_1_14
private theorem k138_1_16 : check w138 pick138 1 t5941 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w138 pick138 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t5921 t4180 k138_1_8 k138_1_15
theorem cov138_1 : PA.Covered 1 (OZ.Valid 1 w138.low w138.t w138.y w138.r w138.cap) (P33.root 1) :=
  Night6836Tree.sound w138 pick138 1 t5941 _ k138_1_16
private theorem k138_2_0 : check w138 pick138 2 t5935 ⟨2,7,4,16,2,52,2,56⟩ = true := by decide +kernel
private theorem k138_2_1 : check w138 pick138 2 t5946 ⟨2,7,4,16,2,52,57,84⟩ = true := by decide +kernel
private theorem k138_2_2 : check w138 pick138 2 t5947 ⟨2,7,4,16,2,52,2,84⟩ = true := glue w138 pick138 2 ⟨2,7,4,16,2,52,2,84⟩ 3 56 t5935 t5946 k138_2_0 k138_2_1
private theorem k138_2_3 : check w138 pick138 2 t4479 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k138_2_4 : check w138 pick138 2 t5948 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w138 pick138 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5947 t4479 k138_2_2 k138_2_3
private theorem k138_2_5 : check w138 pick138 2 t5956 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k138_2_6 : check w138 pick138 2 t5912 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k138_2_7 : check w138 pick138 2 t5957 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w138 pick138 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t5956 t5912 k138_2_5 k138_2_6
private theorem k138_2_8 : check w138 pick138 2 t5958 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w138 pick138 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5948 t5957 k138_2_4 k138_2_7
theorem cov138_2 : PA.Covered 2 (OZ.Valid 2 w138.low w138.t w138.y w138.r w138.cap) (P33.root 2) :=
  Night6836Tree.sound w138 pick138 2 t5958 _ k138_2_8
theorem cov138_3 : PA.Covered 3 (OZ.Valid 3 w138.low w138.t w138.y w138.r w138.cap) (P33.root 3) :=
  Night6836Tree.sound w138 pick138 3 t4800 _ (by decide +kernel)
theorem cov138_4 : PA.Covered 4 (OZ.Valid 4 w138.low w138.t w138.y w138.r w138.cap) (P33.root 4) :=
  Night6836Tree.sound w138 pick138 4 t565 _ (by decide +kernel)
theorem cov138_5 : PA.Covered 5 (OZ.Valid 5 w138.low w138.t w138.y w138.r w138.cap) (P33.root 5) :=
  Night6836Tree.sound w138 pick138 5 t566 _ (by decide +kernel)
theorem cov138_6 : PA.Covered 6 (OZ.Valid 6 w138.low w138.t w138.y w138.r w138.cap) (P33.root 6) :=
  Night6836Tree.sound w138 pick138 6 t567 _ (by decide +kernel)
theorem cov138_7 : PA.Covered 7 (OZ.Valid 7 w138.low w138.t w138.y w138.r w138.cap) (P33.root 7) :=
  Night6836Tree.sound w138 pick138 7 t568 _ (by decide +kernel)
theorem window138 : P33.WindowCount w138 := by
  apply P33.window_count w138 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov138_1
  · exact cov138_2
  · exact cov138_3
  · exact cov138_4
  · exact cov138_5
  · exact cov138_6
  · exact cov138_7
def w139 : P33.Window := ⟨11,45,5606,4657,245790339061624117,45017,36000,5000000,81920000000⟩
def h139_0 : Height w139 := ⟨45017,36000,by decide +kernel⟩
def h139_1 : Height w139 := ⟨49411,33000,by decide +kernel⟩
def h139_2 : Height w139 := ⟨54751,30000,by decide +kernel⟩
def h139_3 : Height w139 := ⟨61589,27000,by decide +kernel⟩
def h139_4 : Height w139 := ⟨71010,24000,by decide +kernel⟩
def h139_5 : Height w139 := ⟨85473,21000,by decide +kernel⟩
def pick139 (cl : ℕ) : Height w139 := if cl<82 then (if cl<5 then (h139_0) else (if cl<27 then (h139_1) else (h139_2))) else (if cl<303 then (h139_3) else (if cl<989 then (h139_4) else (h139_5)))
private theorem k139_1_0 : check w139 pick139 1 t5570 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k139_1_1 : check w139 pick139 1 t5960 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k139_1_2 : check w139 pick139 1 t5961 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w139 pick139 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5570 t5960 k139_1_0 k139_1_1
private theorem k139_1_3 : check w139 pick139 1 t5965 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k139_1_4 : check w139 pick139 1 t5979 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k139_1_5 : check w139 pick139 1 t5980 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w139 pick139 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t5965 t5979 k139_1_3 k139_1_4
private theorem k139_1_6 : check w139 pick139 1 t5981 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w139 pick139 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5961 t5980 k139_1_2 k139_1_5
private theorem k139_1_7 : check w139 pick139 1 t5991 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k139_1_8 : check w139 pick139 1 t3840 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k139_1_9 : check w139 pick139 1 t5992 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w139 pick139 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t5991 t3840 k139_1_7 k139_1_8
private theorem k139_1_10 : check w139 pick139 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k139_1_11 : check w139 pick139 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k139_1_12 : check w139 pick139 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w139 pick139 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k139_1_10 k139_1_11
private theorem k139_1_13 : check w139 pick139 1 t5993 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w139 pick139 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5992 t3709 k139_1_9 k139_1_12
private theorem k139_1_14 : check w139 pick139 1 t5994 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w139 pick139 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t5981 t5993 k139_1_6 k139_1_13
theorem cov139_1 : PA.Covered 1 (OZ.Valid 1 w139.low w139.t w139.y w139.r w139.cap) (P33.root 1) :=
  Night6836Tree.sound w139 pick139 1 t5994 _ k139_1_14
private theorem k139_2_0 : check w139 pick139 2 t5998 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k139_2_1 : check w139 pick139 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k139_2_2 : check w139 pick139 2 t5999 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w139 pick139 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5998 t3777 k139_2_0 k139_2_1
private theorem k139_2_3 : check w139 pick139 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k139_2_4 : check w139 pick139 2 t6001 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k139_2_5 : check w139 pick139 2 t6002 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w139 pick139 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t6001 k139_2_3 k139_2_4
private theorem k139_2_6 : check w139 pick139 2 t6003 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w139 pick139 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5999 t6002 k139_2_2 k139_2_5
theorem cov139_2 : PA.Covered 2 (OZ.Valid 2 w139.low w139.t w139.y w139.r w139.cap) (P33.root 2) :=
  Night6836Tree.sound w139 pick139 2 t6003 _ k139_2_6
theorem cov139_3 : PA.Covered 3 (OZ.Valid 3 w139.low w139.t w139.y w139.r w139.cap) (P33.root 3) :=
  Night6836Tree.sound w139 pick139 3 t564 _ (by decide +kernel)
theorem cov139_4 : PA.Covered 4 (OZ.Valid 4 w139.low w139.t w139.y w139.r w139.cap) (P33.root 4) :=
  Night6836Tree.sound w139 pick139 4 t565 _ (by decide +kernel)
theorem cov139_5 : PA.Covered 5 (OZ.Valid 5 w139.low w139.t w139.y w139.r w139.cap) (P33.root 5) :=
  Night6836Tree.sound w139 pick139 5 t566 _ (by decide +kernel)
theorem cov139_6 : PA.Covered 6 (OZ.Valid 6 w139.low w139.t w139.y w139.r w139.cap) (P33.root 6) :=
  Night6836Tree.sound w139 pick139 6 t567 _ (by decide +kernel)
theorem cov139_7 : PA.Covered 7 (OZ.Valid 7 w139.low w139.t w139.y w139.r w139.cap) (P33.root 7) :=
  Night6836Tree.sound w139 pick139 7 t2134 _ (by decide +kernel)
theorem window139 : P33.WindowCount w139 := by
  apply P33.window_count w139 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov139_1
  · exact cov139_2
  · exact cov139_3
  · exact cov139_4
  · exact cov139_5
  · exact cov139_6
  · exact cov139_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w140 : P33.Window := ⟨11,45,6454,5607,246823597859590922,37270,30000,5000000,81920000000⟩
def h140_0 : Height w140 := ⟨37270,30000,by decide +kernel⟩
def h140_1 : Height w140 := ⟨41724,27000,by decide +kernel⟩
def h140_2 : Height w140 := ⟨47417,24000,by decide +kernel⟩
def h140_3 : Height w140 := ⟨55331,21000,by decide +kernel⟩
def h140_4 : Height w140 := ⟨67857,18000,by decide +kernel⟩
def pick140 (cl : ℕ) : Height w140 := if cl<28 then (if cl<5 then (h140_0) else (h140_1)) else (if cl<168 then (h140_2) else (if cl<947 then (h140_3) else (h140_4)))
private theorem k140_1_0 : check w140 pick140 1 t5833 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k140_1_1 : check w140 pick140 1 t6004 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k140_1_2 : check w140 pick140 1 t6005 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w140 pick140 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5833 t6004 k140_1_0 k140_1_1
private theorem k140_1_3 : check w140 pick140 1 t6016 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k140_1_4 : check w140 pick140 1 t6022 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k140_1_5 : check w140 pick140 1 t6023 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w140 pick140 1 ⟨1,7,2,16,1,52,70,131⟩ 3 104 t6016 t6022 k140_1_3 k140_1_4
private theorem k140_1_6 : check w140 pick140 1 t6024 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w140 pick140 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t6005 t6023 k140_1_2 k140_1_5
private theorem k140_1_7 : check w140 pick140 1 t6040 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k140_1_8 : check w140 pick140 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k140_1_9 : check w140 pick140 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k140_1_10 : check w140 pick140 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w140 pick140 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k140_1_8 k140_1_9
private theorem k140_1_11 : check w140 pick140 1 t6041 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w140 pick140 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t6040 t4432 k140_1_7 k140_1_10
private theorem k140_1_12 : check w140 pick140 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k140_1_13 : check w140 pick140 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k140_1_14 : check w140 pick140 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w140 pick140 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k140_1_12 k140_1_13
private theorem k140_1_15 : check w140 pick140 1 t6042 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w140 pick140 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t6041 t4179 k140_1_11 k140_1_14
private theorem k140_1_16 : check w140 pick140 1 t6043 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w140 pick140 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t6024 t6042 k140_1_6 k140_1_15
theorem cov140_1 : PA.Covered 1 (OZ.Valid 1 w140.low w140.t w140.y w140.r w140.cap) (P33.root 1) :=
  Night6836Tree.sound w140 pick140 1 t6043 _ k140_1_16
private theorem k140_2_0 : check w140 pick140 2 t6069 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k140_2_1 : check w140 pick140 2 t4716 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k140_2_2 : check w140 pick140 2 t6070 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w140 pick140 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t6069 t4716 k140_2_0 k140_2_1
private theorem k140_2_3 : check w140 pick140 2 t6080 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k140_2_4 : check w140 pick140 2 t6086 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k140_2_5 : check w140 pick140 2 t6087 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w140 pick140 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t6080 t6086 k140_2_3 k140_2_4
private theorem k140_2_6 : check w140 pick140 2 t6088 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w140 pick140 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t6070 t6087 k140_2_2 k140_2_5
theorem cov140_2 : PA.Covered 2 (OZ.Valid 2 w140.low w140.t w140.y w140.r w140.cap) (P33.root 2) :=
  Night6836Tree.sound w140 pick140 2 t6088 _ k140_2_6
theorem cov140_3 : PA.Covered 3 (OZ.Valid 3 w140.low w140.t w140.y w140.r w140.cap) (P33.root 3) :=
  Night6836Tree.sound w140 pick140 3 t6094 _ (by decide +kernel)
theorem cov140_4 : PA.Covered 4 (OZ.Valid 4 w140.low w140.t w140.y w140.r w140.cap) (P33.root 4) :=
  Night6836Tree.sound w140 pick140 4 t565 _ (by decide +kernel)
theorem cov140_5 : PA.Covered 5 (OZ.Valid 5 w140.low w140.t w140.y w140.r w140.cap) (P33.root 5) :=
  Night6836Tree.sound w140 pick140 5 t566 _ (by decide +kernel)
theorem cov140_6 : PA.Covered 6 (OZ.Valid 6 w140.low w140.t w140.y w140.r w140.cap) (P33.root 6) :=
  Night6836Tree.sound w140 pick140 6 t567 _ (by decide +kernel)
theorem cov140_7 : PA.Covered 7 (OZ.Valid 7 w140.low w140.t w140.y w140.r w140.cap) (P33.root 7) :=
  Night6836Tree.sound w140 pick140 7 t568 _ (by decide +kernel)
theorem window140 : P33.WindowCount w140 := by
  apply P33.window_count w140 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov140_1
  · exact cov140_2
  · exact cov140_3
  · exact cov140_4
  · exact cov140_5
  · exact cov140_6
  · exact cov140_7
def w141 : P33.Window := ⟨11,46,3939,2990,242628720979388171,71254,57000,5000000,81920000000⟩
def h141_0 : Height w141 := ⟨71254,57000,by decide +kernel⟩
def h141_1 : Height w141 := ⟨75421,54000,by decide +kernel⟩
def h141_2 : Height w141 := ⟨80073,51000,by decide +kernel⟩
def h141_3 : Height w141 := ⟨85354,48000,by decide +kernel⟩
def h141_4 : Height w141 := ⟨91473,45000,by decide +kernel⟩
def h141_5 : Height w141 := ⟨98742,42000,by decide +kernel⟩
def h141_6 : Height w141 := ⟨107651,39000,by decide +kernel⟩
def pick141 (cl : ℕ) : Height w141 := if cl<32 then (if cl<4 then (h141_0) else (if cl<6 then (h141_1) else (h141_2))) else (if cl<107 then (if cl<43 then (h141_3) else (h141_4)) else (if cl<278 then (h141_5) else (h141_6)))
private theorem k141_1_0 : check w141 pick141 1 t5290 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k141_1_1 : check w141 pick141 1 t5292 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k141_1_2 : check w141 pick141 1 t5293 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w141 pick141 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t5290 t5292 k141_1_0 k141_1_1
private theorem k141_1_3 : check w141 pick141 1 t6096 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k141_1_4 : check w141 pick141 1 t6097 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w141 pick141 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t5293 t6096 k141_1_2 k141_1_3
private theorem k141_1_5 : check w141 pick141 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k141_1_6 : check w141 pick141 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k141_1_7 : check w141 pick141 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w141 pick141 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k141_1_5 k141_1_6
private theorem k141_1_8 : check w141 pick141 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k141_1_9 : check w141 pick141 1 t4260 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k141_1_10 : check w141 pick141 1 t4261 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w141 pick141 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t4260 k141_1_8 k141_1_9
private theorem k141_1_11 : check w141 pick141 1 t4262 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w141 pick141 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t4261 k141_1_7 k141_1_10
private theorem k141_1_12 : check w141 pick141 1 t6098 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w141 pick141 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6097 t4262 k141_1_4 k141_1_11
theorem cov141_1 : PA.Covered 1 (OZ.Valid 1 w141.low w141.t w141.y w141.r w141.cap) (P33.root 1) :=
  Night6836Tree.sound w141 pick141 1 t6098 _ k141_1_12
theorem cov141_2 : PA.Covered 2 (OZ.Valid 2 w141.low w141.t w141.y w141.r w141.cap) (P33.root 2) :=
  Night6836Tree.sound w141 pick141 2 t6109 _ (by decide +kernel)
theorem cov141_3 : PA.Covered 3 (OZ.Valid 3 w141.low w141.t w141.y w141.r w141.cap) (P33.root 3) :=
  Night6836Tree.sound w141 pick141 3 t564 _ (by decide +kernel)
theorem cov141_4 : PA.Covered 4 (OZ.Valid 4 w141.low w141.t w141.y w141.r w141.cap) (P33.root 4) :=
  Night6836Tree.sound w141 pick141 4 t565 _ (by decide +kernel)
theorem cov141_5 : PA.Covered 5 (OZ.Valid 5 w141.low w141.t w141.y w141.r w141.cap) (P33.root 5) :=
  Night6836Tree.sound w141 pick141 5 t566 _ (by decide +kernel)
theorem cov141_6 : PA.Covered 6 (OZ.Valid 6 w141.low w141.t w141.y w141.r w141.cap) (P33.root 6) :=
  Night6836Tree.sound w141 pick141 6 t567 _ (by decide +kernel)
theorem cov141_7 : PA.Covered 7 (OZ.Valid 7 w141.low w141.t w141.y w141.r w141.cap) (P33.root 7) :=
  Night6836Tree.sound w141 pick141 7 t2134 _ (by decide +kernel)
theorem window141 : P33.WindowCount w141 := by
  apply P33.window_count w141 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov141_1
  · exact cov141_2
  · exact cov141_3
  · exact cov141_4
  · exact cov141_5
  · exact cov141_6
  · exact cov141_7
def w142 : P33.Window := ⟨11,46,6362,6145,247932203997834852,35732,27000,5000000,81920000000⟩
def h142_0 : Height w142 := ⟨35732,27000,by decide +kernel⟩
def h142_1 : Height w142 := ⟨40455,24000,by decide +kernel⟩
def h142_2 : Height w142 := ⟨46770,21000,by decide +kernel⟩
def h142_3 : Height w142 := ⟨56234,18000,by decide +kernel⟩
def h142_4 : Height w142 := ⟨73412,15000,by decide +kernel⟩
def pick142 (cl : ℕ) : Height w142 := if cl<49 then (if cl<10 then (h142_0) else (h142_1)) else (if cl<312 then (h142_2) else (if cl<1022 then (h142_3) else (h142_4)))
private theorem k142_1_0 : check w142 pick142 1 t5833 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k142_1_1 : check w142 pick142 1 t6111 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k142_1_2 : check w142 pick142 1 t6112 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w142 pick142 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5833 t6111 k142_1_0 k142_1_1
private theorem k142_1_3 : check w142 pick142 1 t4569 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k142_1_4 : check w142 pick142 1 t5857 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k142_1_5 : check w142 pick142 1 t5858 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w142 pick142 1 ⟨1,7,2,16,1,52,70,131⟩ 3 104 t4569 t5857 k142_1_3 k142_1_4
private theorem k142_1_6 : check w142 pick142 1 t6113 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w142 pick142 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t6112 t5858 k142_1_2 k142_1_5
private theorem k142_1_7 : check w142 pick142 1 t5866 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k142_1_8 : check w142 pick142 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k142_1_9 : check w142 pick142 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k142_1_10 : check w142 pick142 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w142 pick142 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k142_1_8 k142_1_9
private theorem k142_1_11 : check w142 pick142 1 t5867 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w142 pick142 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t5866 t4432 k142_1_7 k142_1_10
private theorem k142_1_12 : check w142 pick142 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k142_1_13 : check w142 pick142 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k142_1_14 : check w142 pick142 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w142 pick142 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k142_1_12 k142_1_13
private theorem k142_1_15 : check w142 pick142 1 t6114 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w142 pick142 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t5867 t4179 k142_1_11 k142_1_14
private theorem k142_1_16 : check w142 pick142 1 t6115 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w142 pick142 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t6113 t6114 k142_1_6 k142_1_15
theorem cov142_1 : PA.Covered 1 (OZ.Valid 1 w142.low w142.t w142.y w142.r w142.cap) (P33.root 1) :=
  Night6836Tree.sound w142 pick142 1 t6115 _ k142_1_16
private theorem k142_2_0 : check w142 pick142 2 t6069 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k142_2_1 : check w142 pick142 2 t4716 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k142_2_2 : check w142 pick142 2 t6070 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w142 pick142 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t6069 t4716 k142_2_0 k142_2_1
private theorem k142_2_3 : check w142 pick142 2 t6116 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k142_2_4 : check w142 pick142 2 t6118 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k142_2_5 : check w142 pick142 2 t6119 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w142 pick142 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t6116 t6118 k142_2_3 k142_2_4
private theorem k142_2_6 : check w142 pick142 2 t6120 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w142 pick142 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t6070 t6119 k142_2_2 k142_2_5
theorem cov142_2 : PA.Covered 2 (OZ.Valid 2 w142.low w142.t w142.y w142.r w142.cap) (P33.root 2) :=
  Night6836Tree.sound w142 pick142 2 t6120 _ k142_2_6
theorem cov142_3 : PA.Covered 3 (OZ.Valid 3 w142.low w142.t w142.y w142.r w142.cap) (P33.root 3) :=
  Night6836Tree.sound w142 pick142 3 t6094 _ (by decide +kernel)
theorem cov142_4 : PA.Covered 4 (OZ.Valid 4 w142.low w142.t w142.y w142.r w142.cap) (P33.root 4) :=
  Night6836Tree.sound w142 pick142 4 t565 _ (by decide +kernel)
theorem cov142_5 : PA.Covered 5 (OZ.Valid 5 w142.low w142.t w142.y w142.r w142.cap) (P33.root 5) :=
  Night6836Tree.sound w142 pick142 5 t566 _ (by decide +kernel)
theorem cov142_6 : PA.Covered 6 (OZ.Valid 6 w142.low w142.t w142.y w142.r w142.cap) (P33.root 6) :=
  Night6836Tree.sound w142 pick142 6 t567 _ (by decide +kernel)
theorem cov142_7 : PA.Covered 7 (OZ.Valid 7 w142.low w142.t w142.y w142.r w142.cap) (P33.root 7) :=
  Night6836Tree.sound w142 pick142 7 t2134 _ (by decide +kernel)
theorem window142 : P33.WindowCount w142 := by
  apply P33.window_count w142 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov142_1
  · exact cov142_2
  · exact cov142_3
  · exact cov142_4
  · exact cov142_5
  · exact cov142_6
  · exact cov142_7
def w143 : P33.Window := ⟨11,47,6144,5885,246496974520374551,36155,30000,5000000,81920000000⟩
def h143_0 : Height w143 := ⟨36155,30000,by decide +kernel⟩
def h143_1 : Height w143 := ⟨40339,27000,by decide +kernel⟩
def h143_2 : Height w143 := ⟨45614,24000,by decide +kernel⟩
def h143_3 : Height w143 := ⟨52811,21000,by decide +kernel⟩
def h143_4 : Height w143 := ⟨63896,18000,by decide +kernel⟩
def pick143 (cl : ℕ) : Height w143 := if cl<20 then (if cl<4 then (h143_0) else (h143_1)) else (if cl<104 then (h143_2) else (if cl<830 then (h143_3) else (h143_4)))
private theorem k143_1_0 : check w143 pick143 1 t5833 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k143_1_1 : check w143 pick143 1 t5838 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k143_1_2 : check w143 pick143 1 t5839 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w143 pick143 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5833 t5838 k143_1_0 k143_1_1
private theorem k143_1_3 : check w143 pick143 1 t4358 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k143_1_4 : check w143 pick143 1 t6143 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k143_1_5 : check w143 pick143 1 t6144 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w143 pick143 1 ⟨1,7,2,16,1,52,70,131⟩ 3 104 t4358 t6143 k143_1_3 k143_1_4
private theorem k143_1_6 : check w143 pick143 1 t6145 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w143 pick143 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t5839 t6144 k143_1_2 k143_1_5
private theorem k143_1_7 : check w143 pick143 1 t6149 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k143_1_8 : check w143 pick143 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k143_1_9 : check w143 pick143 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k143_1_10 : check w143 pick143 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w143 pick143 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k143_1_8 k143_1_9
private theorem k143_1_11 : check w143 pick143 1 t6150 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w143 pick143 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t6149 t4432 k143_1_7 k143_1_10
private theorem k143_1_12 : check w143 pick143 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k143_1_13 : check w143 pick143 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k143_1_14 : check w143 pick143 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w143 pick143 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k143_1_12 k143_1_13
private theorem k143_1_15 : check w143 pick143 1 t6151 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w143 pick143 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t6150 t4179 k143_1_11 k143_1_14
private theorem k143_1_16 : check w143 pick143 1 t6152 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w143 pick143 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t6145 t6151 k143_1_6 k143_1_15
theorem cov143_1 : PA.Covered 1 (OZ.Valid 1 w143.low w143.t w143.y w143.r w143.cap) (P33.root 1) :=
  Night6836Tree.sound w143 pick143 1 t6152 _ k143_1_16
private theorem k143_2_0 : check w143 pick143 2 t6155 ⟨2,7,4,16,2,52,2,56⟩ = true := by decide +kernel
private theorem k143_2_1 : check w143 pick143 2 t4463 ⟨2,7,4,16,2,52,57,84⟩ = true := by decide +kernel
private theorem k143_2_2 : check w143 pick143 2 t6156 ⟨2,7,4,16,2,52,2,84⟩ = true := glue w143 pick143 2 ⟨2,7,4,16,2,52,2,84⟩ 3 56 t6155 t4463 k143_2_0 k143_2_1
private theorem k143_2_3 : check w143 pick143 2 t4479 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k143_2_4 : check w143 pick143 2 t6157 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w143 pick143 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t6156 t4479 k143_2_2 k143_2_3
private theorem k143_2_5 : check w143 pick143 2 t6080 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k143_2_6 : check w143 pick143 2 t6161 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k143_2_7 : check w143 pick143 2 t6162 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w143 pick143 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t6080 t6161 k143_2_5 k143_2_6
private theorem k143_2_8 : check w143 pick143 2 t6163 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w143 pick143 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t6157 t6162 k143_2_4 k143_2_7
theorem cov143_2 : PA.Covered 2 (OZ.Valid 2 w143.low w143.t w143.y w143.r w143.cap) (P33.root 2) :=
  Night6836Tree.sound w143 pick143 2 t6163 _ k143_2_8
theorem cov143_3 : PA.Covered 3 (OZ.Valid 3 w143.low w143.t w143.y w143.r w143.cap) (P33.root 3) :=
  Night6836Tree.sound w143 pick143 3 t6167 _ (by decide +kernel)
theorem cov143_4 : PA.Covered 4 (OZ.Valid 4 w143.low w143.t w143.y w143.r w143.cap) (P33.root 4) :=
  Night6836Tree.sound w143 pick143 4 t565 _ (by decide +kernel)
theorem cov143_5 : PA.Covered 5 (OZ.Valid 5 w143.low w143.t w143.y w143.r w143.cap) (P33.root 5) :=
  Night6836Tree.sound w143 pick143 5 t566 _ (by decide +kernel)
theorem cov143_6 : PA.Covered 6 (OZ.Valid 6 w143.low w143.t w143.y w143.r w143.cap) (P33.root 6) :=
  Night6836Tree.sound w143 pick143 6 t567 _ (by decide +kernel)
theorem cov143_7 : PA.Covered 7 (OZ.Valid 7 w143.low w143.t w143.y w143.r w143.cap) (P33.root 7) :=
  Night6836Tree.sound w143 pick143 7 t2134 _ (by decide +kernel)
theorem window143 : P33.WindowCount w143 := by
  apply P33.window_count w143 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov143_1
  · exact cov143_2
  · exact cov143_3
  · exact cov143_4
  · exact cov143_5
  · exact cov143_6
  · exact cov143_7
def w144 : P33.Window := ⟨11,48,4047,3448,215949932277535391,63993,51000,5000000,81920000000⟩
def h144_0 : Height w144 := ⟨63993,51000,by decide +kernel⟩
def h144_1 : Height w144 := ⟨69544,47000,by decide +kernel⟩
def h144_2 : Height w144 := ⟨76133,43000,by decide +kernel⟩
def h144_3 : Height w144 := ⟨84291,39000,by decide +kernel⟩
def h144_4 : Height w144 := ⟨94984,35000,by decide +kernel⟩
def h144_5 : Height w144 := ⟨110170,31000,by decide +kernel⟩
def pick144 (cl : ℕ) : Height w144 := if cl<43 then (if cl<4 then (h144_0) else (if cl<13 then (h144_1) else (h144_2))) else (if cl<188 then (h144_3) else (if cl<870 then (h144_4) else (h144_5)))
private theorem k144_1_0 : check w144 pick144 1 t6174 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k144_1_1 : check w144 pick144 1 t6194 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k144_1_2 : check w144 pick144 1 t6195 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w144 pick144 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t6174 t6194 k144_1_0 k144_1_1
private theorem k144_1_3 : check w144 pick144 1 t6204 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k144_1_4 : check w144 pick144 1 t6205 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w144 pick144 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t6195 t6204 k144_1_2 k144_1_3
private theorem k144_1_5 : check w144 pick144 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k144_1_6 : check w144 pick144 1 t6211 ⟨1,7,2,16,1,52,173,206⟩ = true := by decide +kernel
private theorem k144_1_7 : check w144 pick144 1 t6212 ⟨1,7,2,16,1,52,139,206⟩ = true := glue w144 pick144 1 ⟨1,7,2,16,1,52,139,206⟩ 3 172 t2459 t6211 k144_1_5 k144_1_6
private theorem k144_1_8 : check w144 pick144 1 t6222 ⟨1,7,2,16,1,52,207,247⟩ = true := by decide +kernel
private theorem k144_1_9 : check w144 pick144 1 t6231 ⟨1,7,2,16,1,52,248,450⟩ = true := by decide +kernel
private theorem k144_1_10 : check w144 pick144 1 t6232 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w144 pick144 1 ⟨1,7,2,16,1,52,207,450⟩ 3 247 t6222 t6231 k144_1_8 k144_1_9
private theorem k144_1_11 : check w144 pick144 1 t6233 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w144 pick144 1 ⟨1,7,2,16,1,52,139,450⟩ 3 206 t6212 t6232 k144_1_7 k144_1_10
private theorem k144_1_12 : check w144 pick144 1 t6234 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w144 pick144 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6205 t6233 k144_1_4 k144_1_11
theorem cov144_1 : PA.Covered 1 (OZ.Valid 1 w144.low w144.t w144.y w144.r w144.cap) (P33.root 1) :=
  Night6836Tree.sound w144 pick144 1 t6234 _ k144_1_12
private theorem k144_2_0 : check w144 pick144 2 t6236 ⟨2,7,4,16,2,52,2,166⟩ = true := by decide +kernel
private theorem k144_2_1 : check w144 pick144 2 t5204 ⟨2,7,4,16,2,52,167,450⟩ = true := by decide +kernel
private theorem k144_2_2 : check w144 pick144 2 t6237 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w144 pick144 2 ⟨2,7,4,16,0,52,0,450⟩ 3 166 t6236 t5204 k144_2_0 k144_2_1
theorem cov144_2 : PA.Covered 2 (OZ.Valid 2 w144.low w144.t w144.y w144.r w144.cap) (P33.root 2) :=
  Night6836Tree.sound w144 pick144 2 t6237 _ k144_2_2
theorem cov144_3 : PA.Covered 3 (OZ.Valid 3 w144.low w144.t w144.y w144.r w144.cap) (P33.root 3) :=
  Night6836Tree.sound w144 pick144 3 t564 _ (by decide +kernel)
theorem cov144_4 : PA.Covered 4 (OZ.Valid 4 w144.low w144.t w144.y w144.r w144.cap) (P33.root 4) :=
  Night6836Tree.sound w144 pick144 4 t565 _ (by decide +kernel)
theorem cov144_5 : PA.Covered 5 (OZ.Valid 5 w144.low w144.t w144.y w144.r w144.cap) (P33.root 5) :=
  Night6836Tree.sound w144 pick144 5 t566 _ (by decide +kernel)
theorem cov144_6 : PA.Covered 6 (OZ.Valid 6 w144.low w144.t w144.y w144.r w144.cap) (P33.root 6) :=
  Night6836Tree.sound w144 pick144 6 t567 _ (by decide +kernel)
theorem cov144_7 : PA.Covered 7 (OZ.Valid 7 w144.low w144.t w144.y w144.r w144.cap) (P33.root 7) :=
  Night6836Tree.sound w144 pick144 7 t2134 _ (by decide +kernel)
theorem window144 : P33.WindowCount w144 := by
  apply P33.window_count w144 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov144_1
  · exact cov144_2
  · exact cov144_3
  · exact cov144_4
  · exact cov144_5
  · exact cov144_6
  · exact cov144_7
def w145 : P33.Window := ⟨11,48,5884,5614,247469075300970965,41126,30000,5000000,81920000000⟩
def h145_0 : Height w145 := ⟨41126,30000,by decide +kernel⟩
def h145_1 : Height w145 := ⟨45789,27000,by decide +kernel⟩
def h145_2 : Height w145 := ⟨51777,24000,by decide +kernel⟩
def h145_3 : Height w145 := ⟨60137,21000,by decide +kernel⟩
def h145_4 : Height w145 := ⟨73415,18000,by decide +kernel⟩
def pick145 (cl : ℕ) : Height w145 := if cl<37 then (if cl<6 then (h145_0) else (h145_1)) else (if cl<216 then (h145_2) else (if cl<961 then (h145_3) else (h145_4)))
private theorem k145_1_0 : check w145 pick145 1 t5833 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k145_1_1 : check w145 pick145 1 t6111 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k145_1_2 : check w145 pick145 1 t6112 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w145 pick145 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5833 t6111 k145_1_0 k145_1_1
private theorem k145_1_3 : check w145 pick145 1 t4358 ⟨1,7,2,16,1,52,70,104⟩ = true := by decide +kernel
private theorem k145_1_4 : check w145 pick145 1 t6244 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k145_1_5 : check w145 pick145 1 t6245 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w145 pick145 1 ⟨1,7,2,16,1,52,70,131⟩ 3 104 t4358 t6244 k145_1_3 k145_1_4
private theorem k145_1_6 : check w145 pick145 1 t6246 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w145 pick145 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t6112 t6245 k145_1_2 k145_1_5
private theorem k145_1_7 : check w145 pick145 1 t6149 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k145_1_8 : check w145 pick145 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k145_1_9 : check w145 pick145 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k145_1_10 : check w145 pick145 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w145 pick145 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k145_1_8 k145_1_9
private theorem k145_1_11 : check w145 pick145 1 t6150 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w145 pick145 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t6149 t4432 k145_1_7 k145_1_10
private theorem k145_1_12 : check w145 pick145 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k145_1_13 : check w145 pick145 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k145_1_14 : check w145 pick145 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w145 pick145 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k145_1_12 k145_1_13
private theorem k145_1_15 : check w145 pick145 1 t6151 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w145 pick145 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t6150 t4179 k145_1_11 k145_1_14
private theorem k145_1_16 : check w145 pick145 1 t6247 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w145 pick145 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t6246 t6151 k145_1_6 k145_1_15
theorem cov145_1 : PA.Covered 1 (OZ.Valid 1 w145.low w145.t w145.y w145.r w145.cap) (P33.root 1) :=
  Night6836Tree.sound w145 pick145 1 t6247 _ k145_1_16
private theorem k145_2_0 : check w145 pick145 2 t5935 ⟨2,7,4,16,2,52,2,56⟩ = true := by decide +kernel
private theorem k145_2_1 : check w145 pick145 2 t5946 ⟨2,7,4,16,2,52,57,84⟩ = true := by decide +kernel
private theorem k145_2_2 : check w145 pick145 2 t5947 ⟨2,7,4,16,2,52,2,84⟩ = true := glue w145 pick145 2 ⟨2,7,4,16,2,52,2,84⟩ 3 56 t5935 t5946 k145_2_0 k145_2_1
private theorem k145_2_3 : check w145 pick145 2 t4479 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k145_2_4 : check w145 pick145 2 t5948 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w145 pick145 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5947 t4479 k145_2_2 k145_2_3
private theorem k145_2_5 : check w145 pick145 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k145_2_6 : check w145 pick145 2 t6161 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k145_2_7 : check w145 pick145 2 t6248 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w145 pick145 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t6161 k145_2_5 k145_2_6
private theorem k145_2_8 : check w145 pick145 2 t6249 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w145 pick145 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5948 t6248 k145_2_4 k145_2_7
theorem cov145_2 : PA.Covered 2 (OZ.Valid 2 w145.low w145.t w145.y w145.r w145.cap) (P33.root 2) :=
  Night6836Tree.sound w145 pick145 2 t6249 _ k145_2_8
theorem cov145_3 : PA.Covered 3 (OZ.Valid 3 w145.low w145.t w145.y w145.r w145.cap) (P33.root 3) :=
  Night6836Tree.sound w145 pick145 3 t4877 _ (by decide +kernel)
theorem cov145_4 : PA.Covered 4 (OZ.Valid 4 w145.low w145.t w145.y w145.r w145.cap) (P33.root 4) :=
  Night6836Tree.sound w145 pick145 4 t565 _ (by decide +kernel)
theorem cov145_5 : PA.Covered 5 (OZ.Valid 5 w145.low w145.t w145.y w145.r w145.cap) (P33.root 5) :=
  Night6836Tree.sound w145 pick145 5 t566 _ (by decide +kernel)
theorem cov145_6 : PA.Covered 6 (OZ.Valid 6 w145.low w145.t w145.y w145.r w145.cap) (P33.root 6) :=
  Night6836Tree.sound w145 pick145 6 t567 _ (by decide +kernel)
theorem cov145_7 : PA.Covered 7 (OZ.Valid 7 w145.low w145.t w145.y w145.r w145.cap) (P33.root 7) :=
  Night6836Tree.sound w145 pick145 7 t2134 _ (by decide +kernel)
theorem window145 : P33.WindowCount w145 := by
  apply P33.window_count w145 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov145_1
  · exact cov145_2
  · exact cov145_3
  · exact cov145_4
  · exact cov145_5
  · exact cov145_6
  · exact cov145_7
def w146 : P33.Window := ⟨11,49,5606,4657,246336289338112862,47393,39000,5000000,81920000000⟩
def h146_0 : Height w146 := ⟨47393,39000,by decide +kernel⟩
def h146_1 : Height w146 := ⟨51378,36000,by decide +kernel⟩
def h146_2 : Height w146 := ⟨56060,33000,by decide +kernel⟩
def h146_3 : Height w146 := ⟨61780,30000,by decide +kernel⟩
def h146_4 : Height w146 := ⟨69145,27000,by decide +kernel⟩
def h146_5 : Height w146 := ⟨79344,24000,by decide +kernel⟩
def h146_6 : Height w146 := ⟨95064,21000,by decide +kernel⟩
def pick146 (cl : ℕ) : Height w146 := if cl<32 then (if cl<2 then (h146_0) else (if cl<10 then (h146_1) else (h146_2))) else (if cl<580 then (if cl<117 then (h146_3) else (h146_4)) else (if cl<1020 then (h146_5) else (h146_6)))
private theorem k146_1_0 : check w146 pick146 1 t6264 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k146_1_1 : check w146 pick146 1 t6290 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k146_1_2 : check w146 pick146 1 t6291 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w146 pick146 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6264 t6290 k146_1_0 k146_1_1
private theorem k146_1_3 : check w146 pick146 1 t6297 ⟨1,7,2,16,1,20,77,138⟩ = true := by decide +kernel
private theorem k146_1_4 : check w146 pick146 1 t6315 ⟨1,7,2,16,21,52,77,138⟩ = true := by decide +kernel
private theorem k146_1_5 : check w146 pick146 1 t6316 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w146 pick146 1 ⟨1,7,2,16,1,52,77,138⟩ 2 20 t6297 t6315 k146_1_3 k146_1_4
private theorem k146_1_6 : check w146 pick146 1 t6317 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w146 pick146 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t6291 t6316 k146_1_2 k146_1_5
private theorem k146_1_7 : check w146 pick146 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k146_1_8 : check w146 pick146 1 t6324 ⟨1,7,2,16,1,52,166,186⟩ = true := by decide +kernel
private theorem k146_1_9 : check w146 pick146 1 t6327 ⟨1,7,2,16,1,52,187,199⟩ = true := by decide +kernel
private theorem k146_1_10 : check w146 pick146 1 t6328 ⟨1,7,2,16,1,52,166,199⟩ = true := glue w146 pick146 1 ⟨1,7,2,16,1,52,166,199⟩ 3 186 t6324 t6327 k146_1_8 k146_1_9
private theorem k146_1_11 : check w146 pick146 1 t6329 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w146 pick146 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t4077 t6328 k146_1_7 k146_1_10
private theorem k146_1_12 : check w146 pick146 1 t6332 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k146_1_13 : check w146 pick146 1 t6337 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k146_1_14 : check w146 pick146 1 t6338 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w146 pick146 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t6332 t6337 k146_1_12 k146_1_13
private theorem k146_1_15 : check w146 pick146 1 t6339 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w146 pick146 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t6329 t6338 k146_1_11 k146_1_14
private theorem k146_1_16 : check w146 pick146 1 t6340 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w146 pick146 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6317 t6339 k146_1_6 k146_1_15
theorem cov146_1 : PA.Covered 1 (OZ.Valid 1 w146.low w146.t w146.y w146.r w146.cap) (P33.root 1) :=
  Night6836Tree.sound w146 pick146 1 t6340 _ k146_1_16
private theorem k146_2_0 : check w146 pick146 2 t6341 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k146_2_1 : check w146 pick146 2 t4937 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k146_2_2 : check w146 pick146 2 t6342 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w146 pick146 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t6341 t4937 k146_2_0 k146_2_1
private theorem k146_2_3 : check w146 pick146 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k146_2_4 : check w146 pick146 2 t6346 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k146_2_5 : check w146 pick146 2 t6347 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w146 pick146 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t6346 k146_2_3 k146_2_4
private theorem k146_2_6 : check w146 pick146 2 t6348 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w146 pick146 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t6342 t6347 k146_2_2 k146_2_5
theorem cov146_2 : PA.Covered 2 (OZ.Valid 2 w146.low w146.t w146.y w146.r w146.cap) (P33.root 2) :=
  Night6836Tree.sound w146 pick146 2 t6348 _ k146_2_6
theorem cov146_3 : PA.Covered 3 (OZ.Valid 3 w146.low w146.t w146.y w146.r w146.cap) (P33.root 3) :=
  Night6836Tree.sound w146 pick146 3 t564 _ (by decide +kernel)
theorem cov146_4 : PA.Covered 4 (OZ.Valid 4 w146.low w146.t w146.y w146.r w146.cap) (P33.root 4) :=
  Night6836Tree.sound w146 pick146 4 t565 _ (by decide +kernel)
theorem cov146_5 : PA.Covered 5 (OZ.Valid 5 w146.low w146.t w146.y w146.r w146.cap) (P33.root 5) :=
  Night6836Tree.sound w146 pick146 5 t566 _ (by decide +kernel)
theorem cov146_6 : PA.Covered 6 (OZ.Valid 6 w146.low w146.t w146.y w146.r w146.cap) (P33.root 6) :=
  Night6836Tree.sound w146 pick146 6 t567 _ (by decide +kernel)
theorem cov146_7 : PA.Covered 7 (OZ.Valid 7 w146.low w146.t w146.y w146.r w146.cap) (P33.root 7) :=
  Night6836Tree.sound w146 pick146 7 t2134 _ (by decide +kernel)
theorem window146 : P33.WindowCount w146 := by
  apply P33.window_count w146 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov146_1
  · exact cov146_2
  · exact cov146_3
  · exact cov146_4
  · exact cov146_5
  · exact cov146_6
  · exact cov146_7
def w147 : P33.Window := ⟨11,49,5613,5330,247432552255688057,42790,33000,5000000,81920000000⟩
def h147_0 : Height w147 := ⟨42790,33000,by decide +kernel⟩
def h147_1 : Height w147 := ⟨47087,30000,by decide +kernel⟩
def h147_2 : Height w147 := ⟨52381,27000,by decide +kernel⟩
def h147_3 : Height w147 := ⟨59321,24000,by decide +kernel⟩
def h147_4 : Height w147 := ⟨69267,21000,by decide +kernel⟩
def h147_5 : Height w147 := ⟨85643,18000,by decide +kernel⟩
def pick147 (cl : ℕ) : Height w147 := if cl<90 then (if cl<4 then (h147_0) else (if cl<25 then (h147_1) else (h147_2))) else (if cl<465 then (h147_3) else (if cl<1021 then (h147_4) else (h147_5)))
private theorem k147_1_0 : check w147 pick147 1 t5626 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k147_1_1 : check w147 pick147 1 t6351 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k147_1_2 : check w147 pick147 1 t6352 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w147 pick147 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t5626 t6351 k147_1_0 k147_1_1
private theorem k147_1_3 : check w147 pick147 1 t6370 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k147_1_4 : check w147 pick147 1 t6383 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k147_1_5 : check w147 pick147 1 t6384 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w147 pick147 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t6370 t6383 k147_1_3 k147_1_4
private theorem k147_1_6 : check w147 pick147 1 t6385 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w147 pick147 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t6352 t6384 k147_1_2 k147_1_5
private theorem k147_1_7 : check w147 pick147 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k147_1_8 : check w147 pick147 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k147_1_9 : check w147 pick147 1 t6386 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w147 pick147 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t4090 k147_1_7 k147_1_8
private theorem k147_1_10 : check w147 pick147 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k147_1_11 : check w147 pick147 1 t4178 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k147_1_12 : check w147 pick147 1 t4179 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w147 pick147 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t4178 k147_1_10 k147_1_11
private theorem k147_1_13 : check w147 pick147 1 t6387 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w147 pick147 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t6386 t4179 k147_1_9 k147_1_12
private theorem k147_1_14 : check w147 pick147 1 t6388 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w147 pick147 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6385 t6387 k147_1_6 k147_1_13
theorem cov147_1 : PA.Covered 1 (OZ.Valid 1 w147.low w147.t w147.y w147.r w147.cap) (P33.root 1) :=
  Night6836Tree.sound w147 pick147 1 t6388 _ k147_1_14
private theorem k147_2_0 : check w147 pick147 2 t6390 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k147_2_1 : check w147 pick147 2 t4937 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k147_2_2 : check w147 pick147 2 t6391 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w147 pick147 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t6390 t4937 k147_2_0 k147_2_1
private theorem k147_2_3 : check w147 pick147 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k147_2_4 : check w147 pick147 2 t6392 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k147_2_5 : check w147 pick147 2 t6393 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w147 pick147 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t6392 k147_2_3 k147_2_4
private theorem k147_2_6 : check w147 pick147 2 t6394 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w147 pick147 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t6391 t6393 k147_2_2 k147_2_5
theorem cov147_2 : PA.Covered 2 (OZ.Valid 2 w147.low w147.t w147.y w147.r w147.cap) (P33.root 2) :=
  Night6836Tree.sound w147 pick147 2 t6394 _ k147_2_6
theorem cov147_3 : PA.Covered 3 (OZ.Valid 3 w147.low w147.t w147.y w147.r w147.cap) (P33.root 3) :=
  Night6836Tree.sound w147 pick147 3 t564 _ (by decide +kernel)
theorem cov147_4 : PA.Covered 4 (OZ.Valid 4 w147.low w147.t w147.y w147.r w147.cap) (P33.root 4) :=
  Night6836Tree.sound w147 pick147 4 t565 _ (by decide +kernel)
theorem cov147_5 : PA.Covered 5 (OZ.Valid 5 w147.low w147.t w147.y w147.r w147.cap) (P33.root 5) :=
  Night6836Tree.sound w147 pick147 5 t566 _ (by decide +kernel)
theorem cov147_6 : PA.Covered 6 (OZ.Valid 6 w147.low w147.t w147.y w147.r w147.cap) (P33.root 6) :=
  Night6836Tree.sound w147 pick147 6 t567 _ (by decide +kernel)
theorem cov147_7 : PA.Covered 7 (OZ.Valid 7 w147.low w147.t w147.y w147.r w147.cap) (P33.root 7) :=
  Night6836Tree.sound w147 pick147 7 t2134 _ (by decide +kernel)
theorem window147 : P33.WindowCount w147 := by
  apply P33.window_count w147 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov147_1
  · exact cov147_2
  · exact cov147_3
  · exact cov147_4
  · exact cov147_5
  · exact cov147_6
  · exact cov147_7
def w148 : P33.Window := ⟨11,50,4656,3707,244849044676203242,62699,48000,5000000,81920000000⟩
def h148_0 : Height w148 := ⟨62699,48000,by decide +kernel⟩
def h148_1 : Height w148 := ⟨66826,45000,by decide +kernel⟩
def h148_2 : Height w148 := ⟨71527,42000,by decide +kernel⟩
def h148_3 : Height w148 := ⟨77013,39000,by decide +kernel⟩
def h148_4 : Height w148 := ⟨83611,36000,by decide +kernel⟩
def h148_5 : Height w148 := ⟨91862,33000,by decide +kernel⟩
def h148_6 : Height w148 := ⟨102719,30000,by decide +kernel⟩
def h148_7 : Height w148 := ⟨118038,27000,by decide +kernel⟩
def pick148 (cl : ℕ) : Height w148 := if cl<70 then (if cl<10 then (if cl<3 then (h148_0) else (h148_1)) else (if cl<32 then (h148_2) else (h148_3))) else (if cl<922 then (if cl<210 then (h148_4) else (h148_5)) else (if cl<1012 then (h148_6) else (h148_7)))
private theorem k148_1_0 : check w148 pick148 1 t6395 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k148_1_1 : check w148 pick148 1 t6402 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k148_1_2 : check w148 pick148 1 t6403 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w148 pick148 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t6395 t6402 k148_1_0 k148_1_1
private theorem k148_1_3 : check w148 pick148 1 t6204 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k148_1_4 : check w148 pick148 1 t6404 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w148 pick148 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t6403 t6204 k148_1_2 k148_1_3
private theorem k148_1_5 : check w148 pick148 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k148_1_6 : check w148 pick148 1 t6211 ⟨1,7,2,16,1,52,173,206⟩ = true := by decide +kernel
private theorem k148_1_7 : check w148 pick148 1 t6212 ⟨1,7,2,16,1,52,139,206⟩ = true := glue w148 pick148 1 ⟨1,7,2,16,1,52,139,206⟩ 3 172 t2459 t6211 k148_1_5 k148_1_6
private theorem k148_1_8 : check w148 pick148 1 t6410 ⟨1,7,2,16,1,52,207,247⟩ = true := by decide +kernel
private theorem k148_1_9 : check w148 pick148 1 t6411 ⟨1,7,2,16,1,52,248,450⟩ = true := by decide +kernel
private theorem k148_1_10 : check w148 pick148 1 t6412 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w148 pick148 1 ⟨1,7,2,16,1,52,207,450⟩ 3 247 t6410 t6411 k148_1_8 k148_1_9
private theorem k148_1_11 : check w148 pick148 1 t6413 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w148 pick148 1 ⟨1,7,2,16,1,52,139,450⟩ 3 206 t6212 t6412 k148_1_7 k148_1_10
private theorem k148_1_12 : check w148 pick148 1 t6414 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w148 pick148 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6404 t6413 k148_1_4 k148_1_11
theorem cov148_1 : PA.Covered 1 (OZ.Valid 1 w148.low w148.t w148.y w148.r w148.cap) (P33.root 1) :=
  Night6836Tree.sound w148 pick148 1 t6414 _ k148_1_12
private theorem k148_2_0 : check w148 pick148 2 t6415 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k148_2_1 : check w148 pick148 2 t5187 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k148_2_2 : check w148 pick148 2 t6416 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w148 pick148 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t6415 t5187 k148_2_0 k148_2_1
theorem cov148_2 : PA.Covered 2 (OZ.Valid 2 w148.low w148.t w148.y w148.r w148.cap) (P33.root 2) :=
  Night6836Tree.sound w148 pick148 2 t6416 _ k148_2_2
theorem cov148_3 : PA.Covered 3 (OZ.Valid 3 w148.low w148.t w148.y w148.r w148.cap) (P33.root 3) :=
  Night6836Tree.sound w148 pick148 3 t564 _ (by decide +kernel)
theorem cov148_4 : PA.Covered 4 (OZ.Valid 4 w148.low w148.t w148.y w148.r w148.cap) (P33.root 4) :=
  Night6836Tree.sound w148 pick148 4 t565 _ (by decide +kernel)
theorem cov148_5 : PA.Covered 5 (OZ.Valid 5 w148.low w148.t w148.y w148.r w148.cap) (P33.root 5) :=
  Night6836Tree.sound w148 pick148 5 t566 _ (by decide +kernel)
theorem cov148_6 : PA.Covered 6 (OZ.Valid 6 w148.low w148.t w148.y w148.r w148.cap) (P33.root 6) :=
  Night6836Tree.sound w148 pick148 6 t567 _ (by decide +kernel)
theorem cov148_7 : PA.Covered 7 (OZ.Valid 7 w148.low w148.t w148.y w148.r w148.cap) (P33.root 7) :=
  Night6836Tree.sound w148 pick148 7 t2134 _ (by decide +kernel)
theorem window148 : P33.WindowCount w148 := by
  apply P33.window_count w148 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov148_1
  · exact cov148_2
  · exact cov148_3
  · exact cov148_4
  · exact cov148_5
  · exact cov148_6
  · exact cov148_7
def w149 : P33.Window := ⟨11,50,5329,5033,247416325680712476,45388,36000,5000000,81920000000⟩
def h149_0 : Height w149 := ⟨45388,36000,by decide +kernel⟩
def h149_1 : Height w149 := ⟨49475,33000,by decide +kernel⟩
def h149_2 : Height w149 := ⟨54370,30000,by decide +kernel⟩
def h149_3 : Height w149 := ⟨60518,27000,by decide +kernel⟩
def h149_4 : Height w149 := ⟨68770,24000,by decide +kernel⟩
def h149_5 : Height w149 := ⟨80962,21000,by decide +kernel⟩
def pick149 (cl : ℕ) : Height w149 := if cl<43 then (if cl<2 then (h149_0) else (if cl<13 then (h149_1) else (h149_2))) else (if cl<210 then (h149_3) else (if cl<922 then (h149_4) else (h149_5)))
private theorem k149_1_0 : check w149 pick149 1 t5570 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k149_1_1 : check w149 pick149 1 t6420 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k149_1_2 : check w149 pick149 1 t6421 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w149 pick149 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t5570 t6420 k149_1_0 k149_1_1
private theorem k149_1_3 : check w149 pick149 1 t6423 ⟨1,7,2,16,1,20,70,138⟩ = true := by decide +kernel
private theorem k149_1_4 : check w149 pick149 1 t6435 ⟨1,7,2,16,21,52,70,138⟩ = true := by decide +kernel
private theorem k149_1_5 : check w149 pick149 1 t6436 ⟨1,7,2,16,1,52,70,138⟩ = true := glue w149 pick149 1 ⟨1,7,2,16,1,52,70,138⟩ 2 20 t6423 t6435 k149_1_3 k149_1_4
private theorem k149_1_6 : check w149 pick149 1 t6437 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w149 pick149 1 ⟨1,7,2,16,1,52,1,138⟩ 3 69 t6421 t6436 k149_1_2 k149_1_5
private theorem k149_1_7 : check w149 pick149 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k149_1_8 : check w149 pick149 1 t3371 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k149_1_9 : check w149 pick149 1 t3372 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w149 pick149 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t3199 t3371 k149_1_7 k149_1_8
private theorem k149_1_10 : check w149 pick149 1 t6444 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k149_1_11 : check w149 pick149 1 t3949 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k149_1_12 : check w149 pick149 1 t6445 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w149 pick149 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t6444 t3949 k149_1_10 k149_1_11
private theorem k149_1_13 : check w149 pick149 1 t6446 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w149 pick149 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t3372 t6445 k149_1_9 k149_1_12
private theorem k149_1_14 : check w149 pick149 1 t6447 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w149 pick149 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t6437 t6446 k149_1_6 k149_1_13
theorem cov149_1 : PA.Covered 1 (OZ.Valid 1 w149.low w149.t w149.y w149.r w149.cap) (P33.root 1) :=
  Night6836Tree.sound w149 pick149 1 t6447 _ k149_1_14
private theorem k149_2_0 : check w149 pick149 2 t6453 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k149_2_1 : check w149 pick149 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k149_2_2 : check w149 pick149 2 t6454 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w149 pick149 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t6453 t3777 k149_2_0 k149_2_1
private theorem k149_2_3 : check w149 pick149 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k149_2_4 : check w149 pick149 2 t6455 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k149_2_5 : check w149 pick149 2 t6456 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w149 pick149 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t6455 k149_2_3 k149_2_4
private theorem k149_2_6 : check w149 pick149 2 t6457 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w149 pick149 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t6454 t6456 k149_2_2 k149_2_5
theorem cov149_2 : PA.Covered 2 (OZ.Valid 2 w149.low w149.t w149.y w149.r w149.cap) (P33.root 2) :=
  Night6836Tree.sound w149 pick149 2 t6457 _ k149_2_6
theorem cov149_3 : PA.Covered 3 (OZ.Valid 3 w149.low w149.t w149.y w149.r w149.cap) (P33.root 3) :=
  Night6836Tree.sound w149 pick149 3 t564 _ (by decide +kernel)
theorem cov149_4 : PA.Covered 4 (OZ.Valid 4 w149.low w149.t w149.y w149.r w149.cap) (P33.root 4) :=
  Night6836Tree.sound w149 pick149 4 t565 _ (by decide +kernel)
theorem cov149_5 : PA.Covered 5 (OZ.Valid 5 w149.low w149.t w149.y w149.r w149.cap) (P33.root 5) :=
  Night6836Tree.sound w149 pick149 5 t566 _ (by decide +kernel)
theorem cov149_6 : PA.Covered 6 (OZ.Valid 6 w149.low w149.t w149.y w149.r w149.cap) (P33.root 6) :=
  Night6836Tree.sound w149 pick149 6 t567 _ (by decide +kernel)
theorem cov149_7 : PA.Covered 7 (OZ.Valid 7 w149.low w149.t w149.y w149.r w149.cap) (P33.root 7) :=
  Night6836Tree.sound w149 pick149 7 t2134 _ (by decide +kernel)
theorem window149 : P33.WindowCount w149 := by
  apply P33.window_count w149 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov149_1
  · exact cov149_2
  · exact cov149_3
  · exact cov149_4
  · exact cov149_5
  · exact cov149_6
  · exact cov149_7
end ProximityPrize.SubmissionLower.Night6836Bank
