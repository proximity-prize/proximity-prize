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
def w270 : P33.Window := ⟨14,30,6253,5304,239055310096672380,19607,33000,5000000,81920000000⟩
def h270_0 : Height w270 := ⟨19607,33000,by decide +kernel⟩
def h270_1 : Height w270 := ⟨23669,30000,by decide +kernel⟩
def h270_2 : Height w270 := ⟨28835,27000,by decide +kernel⟩
def h270_3 : Height w270 := ⟨36013,24000,by decide +kernel⟩
def h270_4 : Height w270 := ⟨47476,21000,by decide +kernel⟩
def pick270 (cl : ℕ) : Height w270 := if cl<18 then (if cl<2 then (h270_0) else (h270_1)) else (if cl<104 then (h270_2) else (if cl<922 then (h270_3) else (h270_4)))
private theorem k270_1_0 : check w270 pick270 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k270_1_1 : check w270 pick270 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k270_1_2 : check w270 pick270 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w270 pick270 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k270_1_0 k270_1_1
private theorem k270_1_3 : check w270 pick270 1 t8472 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k270_1_4 : check w270 pick270 1 t6792 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k270_1_5 : check w270 pick270 1 t8473 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w270 pick270 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t8472 t6792 k270_1_3 k270_1_4
private theorem k270_1_6 : check w270 pick270 1 t8474 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w270 pick270 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t8473 k270_1_2 k270_1_5
private theorem k270_1_7 : check w270 pick270 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k270_1_8 : check w270 pick270 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k270_1_9 : check w270 pick270 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w270 pick270 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k270_1_7 k270_1_8
private theorem k270_1_10 : check w270 pick270 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k270_1_11 : check w270 pick270 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k270_1_12 : check w270 pick270 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w270 pick270 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k270_1_10 k270_1_11
private theorem k270_1_13 : check w270 pick270 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w270 pick270 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k270_1_9 k270_1_12
private theorem k270_1_14 : check w270 pick270 1 t8475 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w270 pick270 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8474 t7519 k270_1_6 k270_1_13
theorem cov270_1 : PA.Covered 1 (OZ.Valid 1 w270.low w270.t w270.y w270.r w270.cap) (P33.root 1) :=
  Night6836Tree.sound w270 pick270 1 t8475 _ k270_1_14
private theorem k270_2_0 : check w270 pick270 2 t7548 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k270_2_1 : check w270 pick270 2 t5624 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k270_2_2 : check w270 pick270 2 t7549 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w270 pick270 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7548 t5624 k270_2_0 k270_2_1
theorem cov270_2 : PA.Covered 2 (OZ.Valid 2 w270.low w270.t w270.y w270.r w270.cap) (P33.root 2) :=
  Night6836Tree.sound w270 pick270 2 t7549 _ k270_2_2
theorem cov270_3 : PA.Covered 3 (OZ.Valid 3 w270.low w270.t w270.y w270.r w270.cap) (P33.root 3) :=
  Night6836Tree.sound w270 pick270 3 t564 _ (by decide +kernel)
theorem cov270_4 : PA.Covered 4 (OZ.Valid 4 w270.low w270.t w270.y w270.r w270.cap) (P33.root 4) :=
  Night6836Tree.sound w270 pick270 4 t565 _ (by decide +kernel)
theorem cov270_5 : PA.Covered 5 (OZ.Valid 5 w270.low w270.t w270.y w270.r w270.cap) (P33.root 5) :=
  Night6836Tree.sound w270 pick270 5 t566 _ (by decide +kernel)
theorem cov270_6 : PA.Covered 6 (OZ.Valid 6 w270.low w270.t w270.y w270.r w270.cap) (P33.root 6) :=
  Night6836Tree.sound w270 pick270 6 t567 _ (by decide +kernel)
theorem cov270_7 : PA.Covered 7 (OZ.Valid 7 w270.low w270.t w270.y w270.r w270.cap) (P33.root 7) :=
  Night6836Tree.sound w270 pick270 7 t2134 _ (by decide +kernel)
theorem window270 : P33.WindowCount w270 := by
  apply P33.window_count w270 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov270_1
  · exact cov270_2
  · exact cov270_3
  · exact cov270_4
  · exact cov270_5
  · exact cov270_6
  · exact cov270_7
def w271 : P33.Window := ⟨14,30,6282,6097,240165421339008140,19289,27000,5000000,81920000000⟩
def h271_0 : Height w271 := ⟨19289,27000,by decide +kernel⟩
def h271_1 : Height w271 := ⟨24107,24000,by decide +kernel⟩
def h271_2 : Height w271 := ⟨30996,21000,by decide +kernel⟩
def h271_3 : Height w271 := ⟨42760,18000,by decide +kernel⟩
def pick271 (cl : ℕ) : Height w271 := if cl<83 then (if cl<10 then (h271_0) else (h271_1)) else (if cl<922 then (h271_2) else (h271_3))
private theorem k271_1_0 : check w271 pick271 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k271_1_1 : check w271 pick271 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k271_1_2 : check w271 pick271 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w271 pick271 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k271_1_0 k271_1_1
private theorem k271_1_3 : check w271 pick271 1 t8472 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k271_1_4 : check w271 pick271 1 t6792 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k271_1_5 : check w271 pick271 1 t8473 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w271 pick271 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t8472 t6792 k271_1_3 k271_1_4
private theorem k271_1_6 : check w271 pick271 1 t8474 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w271 pick271 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t8473 k271_1_2 k271_1_5
private theorem k271_1_7 : check w271 pick271 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k271_1_8 : check w271 pick271 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k271_1_9 : check w271 pick271 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w271 pick271 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k271_1_7 k271_1_8
private theorem k271_1_10 : check w271 pick271 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k271_1_11 : check w271 pick271 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k271_1_12 : check w271 pick271 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w271 pick271 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k271_1_10 k271_1_11
private theorem k271_1_13 : check w271 pick271 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w271 pick271 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k271_1_9 k271_1_12
private theorem k271_1_14 : check w271 pick271 1 t8475 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w271 pick271 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8474 t7519 k271_1_6 k271_1_13
theorem cov271_1 : PA.Covered 1 (OZ.Valid 1 w271.low w271.t w271.y w271.r w271.cap) (P33.root 1) :=
  Night6836Tree.sound w271 pick271 1 t8475 _ k271_1_14
private theorem k271_2_0 : check w271 pick271 2 t7548 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k271_2_1 : check w271 pick271 2 t5624 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k271_2_2 : check w271 pick271 2 t7549 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w271 pick271 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7548 t5624 k271_2_0 k271_2_1
theorem cov271_2 : PA.Covered 2 (OZ.Valid 2 w271.low w271.t w271.y w271.r w271.cap) (P33.root 2) :=
  Night6836Tree.sound w271 pick271 2 t7549 _ k271_2_2
theorem cov271_3 : PA.Covered 3 (OZ.Valid 3 w271.low w271.t w271.y w271.r w271.cap) (P33.root 3) :=
  Night6836Tree.sound w271 pick271 3 t564 _ (by decide +kernel)
theorem cov271_4 : PA.Covered 4 (OZ.Valid 4 w271.low w271.t w271.y w271.r w271.cap) (P33.root 4) :=
  Night6836Tree.sound w271 pick271 4 t565 _ (by decide +kernel)
theorem cov271_5 : PA.Covered 5 (OZ.Valid 5 w271.low w271.t w271.y w271.r w271.cap) (P33.root 5) :=
  Night6836Tree.sound w271 pick271 5 t566 _ (by decide +kernel)
theorem cov271_6 : PA.Covered 6 (OZ.Valid 6 w271.low w271.t w271.y w271.r w271.cap) (P33.root 6) :=
  Night6836Tree.sound w271 pick271 6 t567 _ (by decide +kernel)
theorem cov271_7 : PA.Covered 7 (OZ.Valid 7 w271.low w271.t w271.y w271.r w271.cap) (P33.root 7) :=
  Night6836Tree.sound w271 pick271 7 t2134 _ (by decide +kernel)
theorem window271 : P33.WindowCount w271 := by
  apply P33.window_count w271 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov271_1
  · exact cov271_2
  · exact cov271_3
  · exact cov271_4
  · exact cov271_5
  · exact cov271_6
  · exact cov271_7
def w272 : P33.Window := ⟨14,31,6096,5905,245545076474839365,18576,30000,5000000,81920000000⟩
def h272_0 : Height w272 := ⟨18576,30000,by decide +kernel⟩
def h272_1 : Height w272 := ⟨22688,27000,by decide +kernel⟩
def h272_2 : Height w272 := ⟨28080,24000,by decide +kernel⟩
def h272_3 : Height w272 := ⟨35995,21000,by decide +kernel⟩
def h272_4 : Height w272 := ⟨50039,18000,by decide +kernel⟩
def pick272 (cl : ℕ) : Height w272 := if cl<32 then (if cl<3 then (h272_0) else (h272_1)) else (if cl<168 then (h272_2) else (if cl<984 then (h272_3) else (h272_4)))
private theorem k272_1_0 : check w272 pick272 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k272_1_1 : check w272 pick272 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k272_1_2 : check w272 pick272 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w272 pick272 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k272_1_0 k272_1_1
private theorem k272_1_3 : check w272 pick272 1 t8472 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k272_1_4 : check w272 pick272 1 t6792 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k272_1_5 : check w272 pick272 1 t8473 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w272 pick272 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t8472 t6792 k272_1_3 k272_1_4
private theorem k272_1_6 : check w272 pick272 1 t8474 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w272 pick272 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t8473 k272_1_2 k272_1_5
private theorem k272_1_7 : check w272 pick272 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k272_1_8 : check w272 pick272 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k272_1_9 : check w272 pick272 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w272 pick272 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k272_1_7 k272_1_8
private theorem k272_1_10 : check w272 pick272 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k272_1_11 : check w272 pick272 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k272_1_12 : check w272 pick272 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w272 pick272 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k272_1_10 k272_1_11
private theorem k272_1_13 : check w272 pick272 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w272 pick272 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k272_1_9 k272_1_12
private theorem k272_1_14 : check w272 pick272 1 t8475 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w272 pick272 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8474 t7519 k272_1_6 k272_1_13
theorem cov272_1 : PA.Covered 1 (OZ.Valid 1 w272.low w272.t w272.y w272.r w272.cap) (P33.root 1) :=
  Night6836Tree.sound w272 pick272 1 t8475 _ k272_1_14
private theorem k272_2_0 : check w272 pick272 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k272_2_1 : check w272 pick272 2 t5541 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k272_2_2 : check w272 pick272 2 t5542 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w272 pick272 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t5541 k272_2_0 k272_2_1
theorem cov272_2 : PA.Covered 2 (OZ.Valid 2 w272.low w272.t w272.y w272.r w272.cap) (P33.root 2) :=
  Night6836Tree.sound w272 pick272 2 t5542 _ k272_2_2
theorem cov272_3 : PA.Covered 3 (OZ.Valid 3 w272.low w272.t w272.y w272.r w272.cap) (P33.root 3) :=
  Night6836Tree.sound w272 pick272 3 t564 _ (by decide +kernel)
theorem cov272_4 : PA.Covered 4 (OZ.Valid 4 w272.low w272.t w272.y w272.r w272.cap) (P33.root 4) :=
  Night6836Tree.sound w272 pick272 4 t565 _ (by decide +kernel)
theorem cov272_5 : PA.Covered 5 (OZ.Valid 5 w272.low w272.t w272.y w272.r w272.cap) (P33.root 5) :=
  Night6836Tree.sound w272 pick272 5 t566 _ (by decide +kernel)
theorem cov272_6 : PA.Covered 6 (OZ.Valid 6 w272.low w272.t w272.y w272.r w272.cap) (P33.root 6) :=
  Night6836Tree.sound w272 pick272 6 t567 _ (by decide +kernel)
theorem cov272_7 : PA.Covered 7 (OZ.Valid 7 w272.low w272.t w272.y w272.r w272.cap) (P33.root 7) :=
  Night6836Tree.sound w272 pick272 7 t2134 _ (by decide +kernel)
theorem window272 : P33.WindowCount w272 := by
  apply P33.window_count w272 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov272_1
  · exact cov272_2
  · exact cov272_3
  · exact cov272_4
  · exact cov272_5
  · exact cov272_6
  · exact cov272_7
def w273 : P33.Window := ⟨14,32,5904,5710,245807360434927968,21986,30000,5000000,81920000000⟩
def h273_0 : Height w273 := ⟨21986,30000,by decide +kernel⟩
def h273_1 : Height w273 := ⟨26540,27000,by decide +kernel⟩
def h273_2 : Height w273 := ⟨32639,24000,by decide +kernel⟩
def h273_3 : Height w273 := ⟨41850,21000,by decide +kernel⟩
def pick273 (cl : ℕ) : Height w273 := if cl<42 then (if cl<6 then (h273_0) else (h273_1)) else (if cl<302 then (h273_2) else (h273_3))
private theorem k273_1_0 : check w273 pick273 1 t7465 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k273_1_1 : check w273 pick273 1 t8890 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k273_1_2 : check w273 pick273 1 t8891 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w273 pick273 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7465 t8890 k273_1_0 k273_1_1
private theorem k273_1_3 : check w273 pick273 1 t7477 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k273_1_4 : check w273 pick273 1 t7482 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k273_1_5 : check w273 pick273 1 t7483 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w273 pick273 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t7477 t7482 k273_1_3 k273_1_4
private theorem k273_1_6 : check w273 pick273 1 t8892 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w273 pick273 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8891 t7483 k273_1_2 k273_1_5
private theorem k273_1_7 : check w273 pick273 1 t7489 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k273_1_8 : check w273 pick273 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k273_1_9 : check w273 pick273 1 t7490 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w273 pick273 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7489 t6872 k273_1_7 k273_1_8
private theorem k273_1_10 : check w273 pick273 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k273_1_11 : check w273 pick273 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k273_1_12 : check w273 pick273 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w273 pick273 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k273_1_10 k273_1_11
private theorem k273_1_13 : check w273 pick273 1 t7491 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w273 pick273 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7490 t7190 k273_1_9 k273_1_12
private theorem k273_1_14 : check w273 pick273 1 t8893 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w273 pick273 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8892 t7491 k273_1_6 k273_1_13
theorem cov273_1 : PA.Covered 1 (OZ.Valid 1 w273.low w273.t w273.y w273.r w273.cap) (P33.root 1) :=
  Night6836Tree.sound w273 pick273 1 t8893 _ k273_1_14
private theorem k273_2_0 : check w273 pick273 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k273_2_1 : check w273 pick273 2 t5541 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k273_2_2 : check w273 pick273 2 t5542 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w273 pick273 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t5541 k273_2_0 k273_2_1
theorem cov273_2 : PA.Covered 2 (OZ.Valid 2 w273.low w273.t w273.y w273.r w273.cap) (P33.root 2) :=
  Night6836Tree.sound w273 pick273 2 t5542 _ k273_2_2
theorem cov273_3 : PA.Covered 3 (OZ.Valid 3 w273.low w273.t w273.y w273.r w273.cap) (P33.root 3) :=
  Night6836Tree.sound w273 pick273 3 t564 _ (by decide +kernel)
theorem cov273_4 : PA.Covered 4 (OZ.Valid 4 w273.low w273.t w273.y w273.r w273.cap) (P33.root 4) :=
  Night6836Tree.sound w273 pick273 4 t565 _ (by decide +kernel)
theorem cov273_5 : PA.Covered 5 (OZ.Valid 5 w273.low w273.t w273.y w273.r w273.cap) (P33.root 5) :=
  Night6836Tree.sound w273 pick273 5 t566 _ (by decide +kernel)
theorem cov273_6 : PA.Covered 6 (OZ.Valid 6 w273.low w273.t w273.y w273.r w273.cap) (P33.root 6) :=
  Night6836Tree.sound w273 pick273 6 t567 _ (by decide +kernel)
theorem cov273_7 : PA.Covered 7 (OZ.Valid 7 w273.low w273.t w273.y w273.r w273.cap) (P33.root 7) :=
  Night6836Tree.sound w273 pick273 7 t2134 _ (by decide +kernel)
theorem window273 : P33.WindowCount w273 := by
  apply P33.window_count w273 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov273_1
  · exact cov273_2
  · exact cov273_3
  · exact cov273_4
  · exact cov273_5
  · exact cov273_6
  · exact cov273_7
def w274 : P33.Window := ⟨14,33,5169,4220,244488707429210091,29856,42000,5000000,81920000000⟩
def h274_0 : Height w274 := ⟨29856,42000,by decide +kernel⟩
def h274_1 : Height w274 := ⟨34020,39000,by decide +kernel⟩
def h274_2 : Height w274 := ⟨39000,36000,by decide +kernel⟩
def h274_3 : Height w274 := ⟨45234,33000,by decide +kernel⟩
def h274_4 : Height w274 := ⟨53551,30000,by decide +kernel⟩
def h274_5 : Height w274 := ⟨65695,27000,by decide +kernel⟩
def pick274 (cl : ℕ) : Height w274 := if cl<46 then (if cl<4 then (h274_0) else (if cl<14 then (h274_1) else (h274_2))) else (if cl<213 then (h274_3) else (if cl<922 then (h274_4) else (h274_5)))
private theorem k274_1_0 : check w274 pick274 1 t7724 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k274_1_1 : check w274 pick274 1 t7727 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k274_1_2 : check w274 pick274 1 t7728 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w274 pick274 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7724 t7727 k274_1_0 k274_1_1
private theorem k274_1_3 : check w274 pick274 1 t7400 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k274_1_4 : check w274 pick274 1 t7403 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k274_1_5 : check w274 pick274 1 t7404 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w274 pick274 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7400 t7403 k274_1_3 k274_1_4
private theorem k274_1_6 : check w274 pick274 1 t8894 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w274 pick274 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7728 t7404 k274_1_2 k274_1_5
private theorem k274_1_7 : check w274 pick274 1 t7701 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k274_1_8 : check w274 pick274 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k274_1_9 : check w274 pick274 1 t7703 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w274 pick274 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7701 t7702 k274_1_7 k274_1_8
private theorem k274_1_10 : check w274 pick274 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k274_1_11 : check w274 pick274 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k274_1_12 : check w274 pick274 1 t7319 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w274 pick274 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t7318 k274_1_10 k274_1_11
private theorem k274_1_13 : check w274 pick274 1 t7704 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w274 pick274 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7703 t7319 k274_1_9 k274_1_12
private theorem k274_1_14 : check w274 pick274 1 t8895 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w274 pick274 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8894 t7704 k274_1_6 k274_1_13
theorem cov274_1 : PA.Covered 1 (OZ.Valid 1 w274.low w274.t w274.y w274.r w274.cap) (P33.root 1) :=
  Night6836Tree.sound w274 pick274 1 t8895 _ k274_1_14
theorem cov274_2 : PA.Covered 2 (OZ.Valid 2 w274.low w274.t w274.y w274.r w274.cap) (P33.root 2) :=
  Night6836Tree.sound w274 pick274 2 t5320 _ (by decide +kernel)
theorem cov274_3 : PA.Covered 3 (OZ.Valid 3 w274.low w274.t w274.y w274.r w274.cap) (P33.root 3) :=
  Night6836Tree.sound w274 pick274 3 t564 _ (by decide +kernel)
theorem cov274_4 : PA.Covered 4 (OZ.Valid 4 w274.low w274.t w274.y w274.r w274.cap) (P33.root 4) :=
  Night6836Tree.sound w274 pick274 4 t565 _ (by decide +kernel)
theorem cov274_5 : PA.Covered 5 (OZ.Valid 5 w274.low w274.t w274.y w274.r w274.cap) (P33.root 5) :=
  Night6836Tree.sound w274 pick274 5 t566 _ (by decide +kernel)
theorem cov274_6 : PA.Covered 6 (OZ.Valid 6 w274.low w274.t w274.y w274.r w274.cap) (P33.root 6) :=
  Night6836Tree.sound w274 pick274 6 t567 _ (by decide +kernel)
theorem cov274_7 : PA.Covered 7 (OZ.Valid 7 w274.low w274.t w274.y w274.r w274.cap) (P33.root 7) :=
  Night6836Tree.sound w274 pick274 7 t2134 _ (by decide +kernel)
theorem window274 : P33.WindowCount w274 := by
  apply P33.window_count w274 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov274_1
  · exact cov274_2
  · exact cov274_3
  · exact cov274_4
  · exact cov274_5
  · exact cov274_6
  · exact cov274_7
def w275 : P33.Window := ⟨14,33,5709,5509,245791991987588524,21844,33000,5000000,81920000000⟩
def h275_0 : Height w275 := ⟨21844,33000,by decide +kernel⟩
def h275_1 : Height w275 := ⟨25888,30000,by decide +kernel⟩
def h275_2 : Height w275 := ⟨30991,27000,by decide +kernel⟩
def h275_3 : Height w275 := ⟨37986,24000,by decide +kernel⟩
def h275_4 : Height w275 := ⟨48887,21000,by decide +kernel⟩
def pick275 (cl : ℕ) : Height w275 := if cl<18 then (if cl<2 then (h275_0) else (h275_1)) else (if cl<92 then (h275_2) else (if cl<853 then (h275_3) else (h275_4)))
private theorem k275_1_0 : check w275 pick275 1 t7124 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k275_1_1 : check w275 pick275 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k275_1_2 : check w275 pick275 1 t7132 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w275 pick275 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7124 t7131 k275_1_0 k275_1_1
private theorem k275_1_3 : check w275 pick275 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k275_1_4 : check w275 pick275 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k275_1_5 : check w275 pick275 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w275 pick275 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k275_1_3 k275_1_4
private theorem k275_1_6 : check w275 pick275 1 t7455 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w275 pick275 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7132 t7381 k275_1_2 k275_1_5
private theorem k275_1_7 : check w275 pick275 1 t7489 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k275_1_8 : check w275 pick275 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k275_1_9 : check w275 pick275 1 t7490 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w275 pick275 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7489 t6872 k275_1_7 k275_1_8
private theorem k275_1_10 : check w275 pick275 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k275_1_11 : check w275 pick275 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k275_1_12 : check w275 pick275 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w275 pick275 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k275_1_10 k275_1_11
private theorem k275_1_13 : check w275 pick275 1 t7491 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w275 pick275 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7490 t7190 k275_1_9 k275_1_12
private theorem k275_1_14 : check w275 pick275 1 t8896 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w275 pick275 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7455 t7491 k275_1_6 k275_1_13
theorem cov275_1 : PA.Covered 1 (OZ.Valid 1 w275.low w275.t w275.y w275.r w275.cap) (P33.root 1) :=
  Night6836Tree.sound w275 pick275 1 t8896 _ k275_1_14
private theorem k275_2_0 : check w275 pick275 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k275_2_1 : check w275 pick275 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k275_2_2 : check w275 pick275 2 t5528 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w275 pick275 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t3303 k275_2_0 k275_2_1
theorem cov275_2 : PA.Covered 2 (OZ.Valid 2 w275.low w275.t w275.y w275.r w275.cap) (P33.root 2) :=
  Night6836Tree.sound w275 pick275 2 t5528 _ k275_2_2
theorem cov275_3 : PA.Covered 3 (OZ.Valid 3 w275.low w275.t w275.y w275.r w275.cap) (P33.root 3) :=
  Night6836Tree.sound w275 pick275 3 t564 _ (by decide +kernel)
theorem cov275_4 : PA.Covered 4 (OZ.Valid 4 w275.low w275.t w275.y w275.r w275.cap) (P33.root 4) :=
  Night6836Tree.sound w275 pick275 4 t565 _ (by decide +kernel)
theorem cov275_5 : PA.Covered 5 (OZ.Valid 5 w275.low w275.t w275.y w275.r w275.cap) (P33.root 5) :=
  Night6836Tree.sound w275 pick275 5 t566 _ (by decide +kernel)
theorem cov275_6 : PA.Covered 6 (OZ.Valid 6 w275.low w275.t w275.y w275.r w275.cap) (P33.root 6) :=
  Night6836Tree.sound w275 pick275 6 t567 _ (by decide +kernel)
theorem cov275_7 : PA.Covered 7 (OZ.Valid 7 w275.low w275.t w275.y w275.r w275.cap) (P33.root 7) :=
  Night6836Tree.sound w275 pick275 7 t2134 _ (by decide +kernel)
theorem window275 : P33.WindowCount w275 := by
  apply P33.window_count w275 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov275_1
  · exact cov275_2
  · exact cov275_3
  · exact cov275_4
  · exact cov275_5
  · exact cov275_6
  · exact cov275_7
def w276 : P33.Window := ⟨14,34,5508,5304,245562375244573450,25872,33000,5000000,81920000000⟩
def h276_0 : Height w276 := ⟨25872,33000,by decide +kernel⟩
def h276_1 : Height w276 := ⟨30373,30000,by decide +kernel⟩
def h276_2 : Height w276 := ⟨36165,27000,by decide +kernel⟩
def h276_3 : Height w276 := ⟨44309,24000,by decide +kernel⟩
def h276_4 : Height w276 := ⟨57447,21000,by decide +kernel⟩
def pick276 (cl : ℕ) : Height w276 := if cl<32 then (if cl<5 then (h276_0) else (h276_1)) else (if cl<202 then (h276_2) else (if cl<961 then (h276_3) else (h276_4)))
private theorem k276_1_0 : check w276 pick276 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k276_1_1 : check w276 pick276 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k276_1_2 : check w276 pick276 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w276 pick276 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k276_1_0 k276_1_1
private theorem k276_1_3 : check w276 pick276 1 t8669 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k276_1_4 : check w276 pick276 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k276_1_5 : check w276 pick276 1 t8670 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w276 pick276 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t8669 t7348 k276_1_3 k276_1_4
private theorem k276_1_6 : check w276 pick276 1 t8671 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w276 pick276 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t8670 k276_1_2 k276_1_5
private theorem k276_1_7 : check w276 pick276 1 t7458 ⟨1,7,2,16,1,20,139,199⟩ = true := by decide +kernel
private theorem k276_1_8 : check w276 pick276 1 t3099 ⟨1,7,2,16,21,52,139,199⟩ = true := by decide +kernel
private theorem k276_1_9 : check w276 pick276 1 t7459 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w276 pick276 1 ⟨1,7,2,16,1,52,139,199⟩ 2 20 t7458 t3099 k276_1_7 k276_1_8
private theorem k276_1_10 : check w276 pick276 1 t7461 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k276_1_11 : check w276 pick276 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k276_1_12 : check w276 pick276 1 t7462 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w276 pick276 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7461 t7318 k276_1_10 k276_1_11
private theorem k276_1_13 : check w276 pick276 1 t7463 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w276 pick276 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7459 t7462 k276_1_9 k276_1_12
private theorem k276_1_14 : check w276 pick276 1 t8897 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w276 pick276 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8671 t7463 k276_1_6 k276_1_13
theorem cov276_1 : PA.Covered 1 (OZ.Valid 1 w276.low w276.t w276.y w276.r w276.cap) (P33.root 1) :=
  Night6836Tree.sound w276 pick276 1 t8897 _ k276_1_14
private theorem k276_2_0 : check w276 pick276 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k276_2_1 : check w276 pick276 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k276_2_2 : check w276 pick276 2 t5528 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w276 pick276 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t3303 k276_2_0 k276_2_1
theorem cov276_2 : PA.Covered 2 (OZ.Valid 2 w276.low w276.t w276.y w276.r w276.cap) (P33.root 2) :=
  Night6836Tree.sound w276 pick276 2 t5528 _ k276_2_2
theorem cov276_3 : PA.Covered 3 (OZ.Valid 3 w276.low w276.t w276.y w276.r w276.cap) (P33.root 3) :=
  Night6836Tree.sound w276 pick276 3 t564 _ (by decide +kernel)
theorem cov276_4 : PA.Covered 4 (OZ.Valid 4 w276.low w276.t w276.y w276.r w276.cap) (P33.root 4) :=
  Night6836Tree.sound w276 pick276 4 t565 _ (by decide +kernel)
theorem cov276_5 : PA.Covered 5 (OZ.Valid 5 w276.low w276.t w276.y w276.r w276.cap) (P33.root 5) :=
  Night6836Tree.sound w276 pick276 5 t566 _ (by decide +kernel)
theorem cov276_6 : PA.Covered 6 (OZ.Valid 6 w276.low w276.t w276.y w276.r w276.cap) (P33.root 6) :=
  Night6836Tree.sound w276 pick276 6 t567 _ (by decide +kernel)
theorem cov276_7 : PA.Covered 7 (OZ.Valid 7 w276.low w276.t w276.y w276.r w276.cap) (P33.root 7) :=
  Night6836Tree.sound w276 pick276 7 t2134 _ (by decide +kernel)
theorem window276 : P33.WindowCount w276 := by
  apply P33.window_count w276 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov276_1
  · exact cov276_2
  · exact cov276_3
  · exact cov276_4
  · exact cov276_5
  · exact cov276_6
  · exact cov276_7
def w277 : P33.Window := ⟨14,35,5303,5094,242745702404407166,26408,36000,5000000,81920000000⟩
def h277_0 : Height w277 := ⟨26408,36000,by decide +kernel⟩
def h277_1 : Height w277 := ⟨30528,33000,by decide +kernel⟩
def h277_2 : Height w277 := ⟨35606,30000,by decide +kernel⟩
def h277_3 : Height w277 := ⟨42284,27000,by decide +kernel⟩
def h277_4 : Height w277 := ⟨51938,24000,by decide +kernel⟩
def h277_5 : Height w277 := ⟨68137,21000,by decide +kernel⟩
def pick277 (cl : ℕ) : Height w277 := if cl<70 then (if cl<3 then (h277_0) else (if cl<18 then (h277_1) else (h277_2))) else (if cl<347 then (h277_3) else (if cl<1021 then (h277_4) else (h277_5)))
private theorem k277_1_0 : check w277 pick277 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k277_1_1 : check w277 pick277 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k277_1_2 : check w277 pick277 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w277 pick277 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k277_1_0 k277_1_1
private theorem k277_1_3 : check w277 pick277 1 t7416 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k277_1_4 : check w277 pick277 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k277_1_5 : check w277 pick277 1 t7417 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w277 pick277 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7416 t7348 k277_1_3 k277_1_4
private theorem k277_1_6 : check w277 pick277 1 t7418 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w277 pick277 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7417 k277_1_2 k277_1_5
private theorem k277_1_7 : check w277 pick277 1 t7386 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k277_1_8 : check w277 pick277 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k277_1_9 : check w277 pick277 1 t7387 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w277 pick277 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7386 t7362 k277_1_7 k277_1_8
private theorem k277_1_10 : check w277 pick277 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k277_1_11 : check w277 pick277 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k277_1_12 : check w277 pick277 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w277 pick277 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k277_1_10 k277_1_11
private theorem k277_1_13 : check w277 pick277 1 t7388 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w277 pick277 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7387 t7369 k277_1_9 k277_1_12
private theorem k277_1_14 : check w277 pick277 1 t7419 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w277 pick277 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7418 t7388 k277_1_6 k277_1_13
theorem cov277_1 : PA.Covered 1 (OZ.Valid 1 w277.low w277.t w277.y w277.r w277.cap) (P33.root 1) :=
  Night6836Tree.sound w277 pick277 1 t7419 _ k277_1_14
private theorem k277_2_0 : check w277 pick277 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k277_2_1 : check w277 pick277 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k277_2_2 : check w277 pick277 2 t5528 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w277 pick277 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t3303 k277_2_0 k277_2_1
theorem cov277_2 : PA.Covered 2 (OZ.Valid 2 w277.low w277.t w277.y w277.r w277.cap) (P33.root 2) :=
  Night6836Tree.sound w277 pick277 2 t5528 _ k277_2_2
theorem cov277_3 : PA.Covered 3 (OZ.Valid 3 w277.low w277.t w277.y w277.r w277.cap) (P33.root 3) :=
  Night6836Tree.sound w277 pick277 3 t564 _ (by decide +kernel)
theorem cov277_4 : PA.Covered 4 (OZ.Valid 4 w277.low w277.t w277.y w277.r w277.cap) (P33.root 4) :=
  Night6836Tree.sound w277 pick277 4 t565 _ (by decide +kernel)
theorem cov277_5 : PA.Covered 5 (OZ.Valid 5 w277.low w277.t w277.y w277.r w277.cap) (P33.root 5) :=
  Night6836Tree.sound w277 pick277 5 t566 _ (by decide +kernel)
theorem cov277_6 : PA.Covered 6 (OZ.Valid 6 w277.low w277.t w277.y w277.r w277.cap) (P33.root 6) :=
  Night6836Tree.sound w277 pick277 6 t567 _ (by decide +kernel)
theorem cov277_7 : PA.Covered 7 (OZ.Valid 7 w277.low w277.t w277.y w277.r w277.cap) (P33.root 7) :=
  Night6836Tree.sound w277 pick277 7 t2134 _ (by decide +kernel)
theorem window277 : P33.WindowCount w277 := by
  apply P33.window_count w277 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov277_1
  · exact cov277_2
  · exact cov277_3
  · exact cov277_4
  · exact cov277_5
  · exact cov277_6
  · exact cov277_7
def w278 : P33.Window := ⟨14,36,5093,4199,244904354113614898,36174,42000,5000000,81920000000⟩
def h278_0 : Height w278 := ⟨36174,42000,by decide +kernel⟩
def h278_1 : Height w278 := ⟨40690,39000,by decide +kernel⟩
def h278_2 : Height w278 := ⟨46131,36000,by decide +kernel⟩
def h278_3 : Height w278 := ⟨53000,33000,by decide +kernel⟩
def h278_4 : Height w278 := ⟨62237,30000,by decide +kernel⟩
def h278_5 : Height w278 := ⟨75836,27000,by decide +kernel⟩
def pick278 (cl : ℕ) : Height w278 := if cl<83 then (if cl<6 then (h278_0) else (if cl<32 then (h278_1) else (h278_2))) else (if cl<302 then (h278_3) else (if cl<964 then (h278_4) else (h278_5)))
private theorem k278_1_0 : check w278 pick278 1 t8615 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k278_1_1 : check w278 pick278 1 t8616 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k278_1_2 : check w278 pick278 1 t8617 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w278 pick278 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t8615 t8616 k278_1_0 k278_1_1
private theorem k278_1_3 : check w278 pick278 1 t8619 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k278_1_4 : check w278 pick278 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k278_1_5 : check w278 pick278 1 t8620 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w278 pick278 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t8619 t7348 k278_1_3 k278_1_4
private theorem k278_1_6 : check w278 pick278 1 t8621 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w278 pick278 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8617 t8620 k278_1_2 k278_1_5
private theorem k278_1_7 : check w278 pick278 1 t7386 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k278_1_8 : check w278 pick278 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k278_1_9 : check w278 pick278 1 t7387 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w278 pick278 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7386 t7362 k278_1_7 k278_1_8
private theorem k278_1_10 : check w278 pick278 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k278_1_11 : check w278 pick278 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k278_1_12 : check w278 pick278 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w278 pick278 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k278_1_10 k278_1_11
private theorem k278_1_13 : check w278 pick278 1 t7388 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w278 pick278 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7387 t7369 k278_1_9 k278_1_12
private theorem k278_1_14 : check w278 pick278 1 t8622 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w278 pick278 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8621 t7388 k278_1_6 k278_1_13
theorem cov278_1 : PA.Covered 1 (OZ.Valid 1 w278.low w278.t w278.y w278.r w278.cap) (P33.root 1) :=
  Night6836Tree.sound w278 pick278 1 t8622 _ k278_1_14
private theorem k278_2_0 : check w278 pick278 2 t6415 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k278_2_1 : check w278 pick278 2 t8252 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k278_2_2 : check w278 pick278 2 t8623 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w278 pick278 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t6415 t8252 k278_2_0 k278_2_1
theorem cov278_2 : PA.Covered 2 (OZ.Valid 2 w278.low w278.t w278.y w278.r w278.cap) (P33.root 2) :=
  Night6836Tree.sound w278 pick278 2 t8623 _ k278_2_2
theorem cov278_3 : PA.Covered 3 (OZ.Valid 3 w278.low w278.t w278.y w278.r w278.cap) (P33.root 3) :=
  Night6836Tree.sound w278 pick278 3 t564 _ (by decide +kernel)
theorem cov278_4 : PA.Covered 4 (OZ.Valid 4 w278.low w278.t w278.y w278.r w278.cap) (P33.root 4) :=
  Night6836Tree.sound w278 pick278 4 t565 _ (by decide +kernel)
theorem cov278_5 : PA.Covered 5 (OZ.Valid 5 w278.low w278.t w278.y w278.r w278.cap) (P33.root 5) :=
  Night6836Tree.sound w278 pick278 5 t566 _ (by decide +kernel)
theorem cov278_6 : PA.Covered 6 (OZ.Valid 6 w278.low w278.t w278.y w278.r w278.cap) (P33.root 6) :=
  Night6836Tree.sound w278 pick278 6 t567 _ (by decide +kernel)
theorem cov278_7 : PA.Covered 7 (OZ.Valid 7 w278.low w278.t w278.y w278.r w278.cap) (P33.root 7) :=
  Night6836Tree.sound w278 pick278 7 t2134 _ (by decide +kernel)
theorem window278 : P33.WindowCount w278 := by
  apply P33.window_count w278 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov278_1
  · exact cov278_2
  · exact cov278_3
  · exact cov278_4
  · exact cov278_5
  · exact cov278_6
  · exact cov278_7
def w279 : P33.Window := ⟨14,37,4878,4658,245702972840977328,32823,39000,5000000,81920000000⟩
def h279_0 : Height w279 := ⟨32823,39000,by decide +kernel⟩
def h279_1 : Height w279 := ⟨37180,36000,by decide +kernel⟩
def h279_2 : Height w279 := ⟨42480,33000,by decide +kernel⟩
def h279_3 : Height w279 := ⟨49282,30000,by decide +kernel⟩
def h279_4 : Height w279 := ⟨58693,27000,by decide +kernel⟩
def h279_5 : Height w279 := ⟨73243,24000,by decide +kernel⟩
def pick279 (cl : ℕ) : Height w279 := if cl<83 then (if cl<5 then (h279_0) else (if cl<32 then (h279_1) else (h279_2))) else (if cl<302 then (h279_3) else (if cl<993 then (h279_4) else (h279_5)))
private theorem k279_1_0 : check w279 pick279 1 t7393 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k279_1_1 : check w279 pick279 1 t575 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k279_1_2 : check w279 pick279 1 t7394 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w279 pick279 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7393 t575 k279_1_0 k279_1_1
private theorem k279_1_3 : check w279 pick279 1 t7732 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k279_1_4 : check w279 pick279 1 t7403 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k279_1_5 : check w279 pick279 1 t7733 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w279 pick279 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7732 t7403 k279_1_3 k279_1_4
private theorem k279_1_6 : check w279 pick279 1 t8725 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w279 pick279 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7394 t7733 k279_1_2 k279_1_5
private theorem k279_1_7 : check w279 pick279 1 t7701 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k279_1_8 : check w279 pick279 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k279_1_9 : check w279 pick279 1 t7703 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w279 pick279 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7701 t7702 k279_1_7 k279_1_8
private theorem k279_1_10 : check w279 pick279 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k279_1_11 : check w279 pick279 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k279_1_12 : check w279 pick279 1 t7319 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w279 pick279 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t7318 k279_1_10 k279_1_11
private theorem k279_1_13 : check w279 pick279 1 t7704 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w279 pick279 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7703 t7319 k279_1_9 k279_1_12
private theorem k279_1_14 : check w279 pick279 1 t8898 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w279 pick279 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8725 t7704 k279_1_6 k279_1_13
theorem cov279_1 : PA.Covered 1 (OZ.Valid 1 w279.low w279.t w279.y w279.r w279.cap) (P33.root 1) :=
  Night6836Tree.sound w279 pick279 1 t8898 _ k279_1_14
private theorem k279_2_0 : check w279 pick279 2 t8905 ⟨2,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k279_2_1 : check w279 pick279 2 t8908 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k279_2_2 : check w279 pick279 2 t8909 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w279 pick279 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t8905 t8908 k279_2_0 k279_2_1
theorem cov279_2 : PA.Covered 2 (OZ.Valid 2 w279.low w279.t w279.y w279.r w279.cap) (P33.root 2) :=
  Night6836Tree.sound w279 pick279 2 t8909 _ k279_2_2
theorem cov279_3 : PA.Covered 3 (OZ.Valid 3 w279.low w279.t w279.y w279.r w279.cap) (P33.root 3) :=
  Night6836Tree.sound w279 pick279 3 t564 _ (by decide +kernel)
theorem cov279_4 : PA.Covered 4 (OZ.Valid 4 w279.low w279.t w279.y w279.r w279.cap) (P33.root 4) :=
  Night6836Tree.sound w279 pick279 4 t565 _ (by decide +kernel)
theorem cov279_5 : PA.Covered 5 (OZ.Valid 5 w279.low w279.t w279.y w279.r w279.cap) (P33.root 5) :=
  Night6836Tree.sound w279 pick279 5 t566 _ (by decide +kernel)
theorem cov279_6 : PA.Covered 6 (OZ.Valid 6 w279.low w279.t w279.y w279.r w279.cap) (P33.root 6) :=
  Night6836Tree.sound w279 pick279 6 t567 _ (by decide +kernel)
theorem cov279_7 : PA.Covered 7 (OZ.Valid 7 w279.low w279.t w279.y w279.r w279.cap) (P33.root 7) :=
  Night6836Tree.sound w279 pick279 7 t2134 _ (by decide +kernel)
theorem window279 : P33.WindowCount w279 := by
  apply P33.window_count w279 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov279_1
  · exact cov279_2
  · exact cov279_3
  · exact cov279_4
  · exact cov279_5
  · exact cov279_6
  · exact cov279_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w280 : P33.Window := ⟨14,38,4657,4431,245922835506462631,34998,42000,5000000,81920000000⟩
def h280_0 : Height w280 := ⟨34998,42000,by decide +kernel⟩
def h280_1 : Height w280 := ⟨39194,39000,by decide +kernel⟩
def h280_2 : Height w280 := ⟨44183,36000,by decide +kernel⟩
def h280_3 : Height w280 := ⟨50373,33000,by decide +kernel⟩
def h280_4 : Height w280 := ⟨58512,30000,by decide +kernel⟩
def h280_5 : Height w280 := ⟨70120,27000,by decide +kernel⟩
def pick280 (cl : ℕ) : Height w280 := if cl<43 then (if cl<4 then (h280_0) else (if cl<14 then (h280_1) else (h280_2))) else (if cl<200 then (h280_3) else (if cl<922 then (h280_4) else (h280_5)))
private theorem k280_1_0 : check w280 pick280 1 t8910 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k280_1_1 : check w280 pick280 1 t2318 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k280_1_2 : check w280 pick280 1 t8911 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w280 pick280 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t8910 t2318 k280_1_0 k280_1_1
private theorem k280_1_3 : check w280 pick280 1 t8254 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k280_1_4 : check w280 pick280 1 t7403 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k280_1_5 : check w280 pick280 1 t8912 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w280 pick280 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t8254 t7403 k280_1_3 k280_1_4
private theorem k280_1_6 : check w280 pick280 1 t8913 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w280 pick280 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8911 t8912 k280_1_2 k280_1_5
private theorem k280_1_7 : check w280 pick280 1 t7701 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k280_1_8 : check w280 pick280 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k280_1_9 : check w280 pick280 1 t7703 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w280 pick280 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7701 t7702 k280_1_7 k280_1_8
private theorem k280_1_10 : check w280 pick280 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k280_1_11 : check w280 pick280 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k280_1_12 : check w280 pick280 1 t7319 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w280 pick280 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t7318 k280_1_10 k280_1_11
private theorem k280_1_13 : check w280 pick280 1 t7704 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w280 pick280 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7703 t7319 k280_1_9 k280_1_12
private theorem k280_1_14 : check w280 pick280 1 t8914 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w280 pick280 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8913 t7704 k280_1_6 k280_1_13
theorem cov280_1 : PA.Covered 1 (OZ.Valid 1 w280.low w280.t w280.y w280.r w280.cap) (P33.root 1) :=
  Night6836Tree.sound w280 pick280 1 t8914 _ k280_1_14
theorem cov280_2 : PA.Covered 2 (OZ.Valid 2 w280.low w280.t w280.y w280.r w280.cap) (P33.root 2) :=
  Night6836Tree.sound w280 pick280 2 t8917 _ (by decide +kernel)
theorem cov280_3 : PA.Covered 3 (OZ.Valid 3 w280.low w280.t w280.y w280.r w280.cap) (P33.root 3) :=
  Night6836Tree.sound w280 pick280 3 t564 _ (by decide +kernel)
theorem cov280_4 : PA.Covered 4 (OZ.Valid 4 w280.low w280.t w280.y w280.r w280.cap) (P33.root 4) :=
  Night6836Tree.sound w280 pick280 4 t565 _ (by decide +kernel)
theorem cov280_5 : PA.Covered 5 (OZ.Valid 5 w280.low w280.t w280.y w280.r w280.cap) (P33.root 5) :=
  Night6836Tree.sound w280 pick280 5 t566 _ (by decide +kernel)
theorem cov280_6 : PA.Covered 6 (OZ.Valid 6 w280.low w280.t w280.y w280.r w280.cap) (P33.root 6) :=
  Night6836Tree.sound w280 pick280 6 t567 _ (by decide +kernel)
theorem cov280_7 : PA.Covered 7 (OZ.Valid 7 w280.low w280.t w280.y w280.r w280.cap) (P33.root 7) :=
  Night6836Tree.sound w280 pick280 7 t2134 _ (by decide +kernel)
theorem window280 : P33.WindowCount w280 := by
  apply P33.window_count w280 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov280_1
  · exact cov280_2
  · exact cov280_3
  · exact cov280_4
  · exact cov280_5
  · exact cov280_6
  · exact cov280_7
def w281 : P33.Window := ⟨14,39,4430,4199,245628889841374333,37943,45000,5000000,81920000000⟩
def h281_0 : Height w281 := ⟨37943,45000,by decide +kernel⟩
def h281_1 : Height w281 := ⟨42067,42000,by decide +kernel⟩
def h281_2 : Height w281 := ⟨46889,39000,by decide +kernel⟩
def h281_3 : Height w281 := ⟨52728,36000,by decide +kernel⟩
def h281_4 : Height w281 := ⟨60137,33000,by decide +kernel⟩
def h281_5 : Height w281 := ⟨70146,30000,by decide +kernel⟩
def pick281 (cl : ℕ) : Height w281 := if cl<36 then (if cl<3 then (h281_0) else (if cl<10 then (h281_1) else (h281_2))) else (if cl<132 then (h281_3) else (if cl<493 then (h281_4) else (h281_5)))
private theorem k281_1_0 : check w281 pick281 1 t8331 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k281_1_1 : check w281 pick281 1 t8937 ⟨1,7,2,16,1,52,84,152⟩ = true := by decide +kernel
private theorem k281_1_2 : check w281 pick281 1 t8938 ⟨1,7,2,16,1,52,1,152⟩ = true := glue w281 pick281 1 ⟨1,7,2,16,1,52,1,152⟩ 3 83 t8331 t8937 k281_1_0 k281_1_1
private theorem k281_1_3 : check w281 pick281 1 t8948 ⟨1,7,2,16,1,52,153,206⟩ = true := by decide +kernel
private theorem k281_1_4 : check w281 pick281 1 t8867 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k281_1_5 : check w281 pick281 1 t8455 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k281_1_6 : check w281 pick281 1 t8868 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w281 pick281 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t8867 t8455 k281_1_4 k281_1_5
private theorem k281_1_7 : check w281 pick281 1 t8949 ⟨1,7,2,16,1,52,153,450⟩ = true := glue w281 pick281 1 ⟨1,7,2,16,1,52,153,450⟩ 3 206 t8948 t8868 k281_1_3 k281_1_6
private theorem k281_1_8 : check w281 pick281 1 t8950 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w281 pick281 1 ⟨1,7,2,16,0,52,0,450⟩ 3 152 t8938 t8949 k281_1_2 k281_1_7
theorem cov281_1 : PA.Covered 1 (OZ.Valid 1 w281.low w281.t w281.y w281.r w281.cap) (P33.root 1) :=
  Night6836Tree.sound w281 pick281 1 t8950 _ k281_1_8
theorem cov281_2 : PA.Covered 2 (OZ.Valid 2 w281.low w281.t w281.y w281.r w281.cap) (P33.root 2) :=
  Night6836Tree.sound w281 pick281 2 t8756 _ (by decide +kernel)
theorem cov281_3 : PA.Covered 3 (OZ.Valid 3 w281.low w281.t w281.y w281.r w281.cap) (P33.root 3) :=
  Night6836Tree.sound w281 pick281 3 t564 _ (by decide +kernel)
theorem cov281_4 : PA.Covered 4 (OZ.Valid 4 w281.low w281.t w281.y w281.r w281.cap) (P33.root 4) :=
  Night6836Tree.sound w281 pick281 4 t565 _ (by decide +kernel)
theorem cov281_5 : PA.Covered 5 (OZ.Valid 5 w281.low w281.t w281.y w281.r w281.cap) (P33.root 5) :=
  Night6836Tree.sound w281 pick281 5 t566 _ (by decide +kernel)
theorem cov281_6 : PA.Covered 6 (OZ.Valid 6 w281.low w281.t w281.y w281.r w281.cap) (P33.root 6) :=
  Night6836Tree.sound w281 pick281 6 t567 _ (by decide +kernel)
theorem cov281_7 : PA.Covered 7 (OZ.Valid 7 w281.low w281.t w281.y w281.r w281.cap) (P33.root 7) :=
  Night6836Tree.sound w281 pick281 7 t2134 _ (by decide +kernel)
theorem window281 : P33.WindowCount w281 := by
  apply P33.window_count w281 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov281_1
  · exact cov281_2
  · exact cov281_3
  · exact cov281_4
  · exact cov281_5
  · exact cov281_6
  · exact cov281_7
def w282 : P33.Window := ⟨14,40,4198,3960,243848611743312072,41855,48000,5000000,81920000000⟩
def h282_0 : Height w282 := ⟨41855,48000,by decide +kernel⟩
def h282_1 : Height w282 := ⟨45987,45000,by decide +kernel⟩
def h282_2 : Height w282 := ⟨50761,42000,by decide +kernel⟩
def h282_3 : Height w282 := ⟨56445,39000,by decide +kernel⟩
def h282_4 : Height w282 := ⟨63475,36000,by decide +kernel⟩
def h282_5 : Height w282 := ⟨72625,33000,by decide +kernel⟩
def pick282 (cl : ℕ) : Height w282 := if cl<32 then (if cl<3 then (h282_0) else (if cl<10 then (h282_1) else (h282_2))) else (if cl<95 then (h282_3) else (if cl<302 then (h282_4) else (h282_5)))
private theorem k282_1_0 : check w282 pick282 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k282_1_1 : check w282 pick282 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k282_1_2 : check w282 pick282 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w282 pick282 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k282_1_0 k282_1_1
private theorem k282_1_3 : check w282 pick282 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k282_1_4 : check w282 pick282 1 t8752 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k282_1_5 : check w282 pick282 1 t8753 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w282 pick282 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t8752 k282_1_3 k282_1_4
private theorem k282_1_6 : check w282 pick282 1 t8754 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w282 pick282 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8753 k282_1_2 k282_1_5
theorem cov282_1 : PA.Covered 1 (OZ.Valid 1 w282.low w282.t w282.y w282.r w282.cap) (P33.root 1) :=
  Night6836Tree.sound w282 pick282 1 t8754 _ k282_1_6
theorem cov282_2 : PA.Covered 2 (OZ.Valid 2 w282.low w282.t w282.y w282.r w282.cap) (P33.root 2) :=
  Night6836Tree.sound w282 pick282 2 t5320 _ (by decide +kernel)
theorem cov282_3 : PA.Covered 3 (OZ.Valid 3 w282.low w282.t w282.y w282.r w282.cap) (P33.root 3) :=
  Night6836Tree.sound w282 pick282 3 t564 _ (by decide +kernel)
theorem cov282_4 : PA.Covered 4 (OZ.Valid 4 w282.low w282.t w282.y w282.r w282.cap) (P33.root 4) :=
  Night6836Tree.sound w282 pick282 4 t565 _ (by decide +kernel)
theorem cov282_5 : PA.Covered 5 (OZ.Valid 5 w282.low w282.t w282.y w282.r w282.cap) (P33.root 5) :=
  Night6836Tree.sound w282 pick282 5 t566 _ (by decide +kernel)
theorem cov282_6 : PA.Covered 6 (OZ.Valid 6 w282.low w282.t w282.y w282.r w282.cap) (P33.root 6) :=
  Night6836Tree.sound w282 pick282 6 t567 _ (by decide +kernel)
theorem cov282_7 : PA.Covered 7 (OZ.Valid 7 w282.low w282.t w282.y w282.r w282.cap) (P33.root 7) :=
  Night6836Tree.sound w282 pick282 7 t2134 _ (by decide +kernel)
theorem window282 : P33.WindowCount w282 := by
  apply P33.window_count w282 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov282_1
  · exact cov282_2
  · exact cov282_3
  · exact cov282_4
  · exact cov282_5
  · exact cov282_6
  · exact cov282_7
def w283 : P33.Window := ⟨14,41,3959,3716,241706265693245651,46914,51000,5000000,81920000000⟩
def h283_0 : Height w283 := ⟨46914,51000,by decide +kernel⟩
def h283_1 : Height w283 := ⟨51131,48000,by decide +kernel⟩
def h283_2 : Height w283 := ⟨55963,45000,by decide +kernel⟩
def h283_3 : Height w283 := ⟨61645,42000,by decide +kernel⟩
def h283_4 : Height w283 := ⟨68551,39000,by decide +kernel⟩
def h283_5 : Height w283 := ⟨77306,36000,by decide +kernel⟩
def pick283 (cl : ℕ) : Height w283 := if cl<32 then (if cl<4 then (h283_0) else (if cl<10 then (h283_1) else (h283_2))) else (if cl<83 then (h283_3) else (if cl<302 then (h283_4) else (h283_5)))
private theorem k283_1_0 : check w283 pick283 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k283_1_1 : check w283 pick283 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k283_1_2 : check w283 pick283 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w283 pick283 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k283_1_0 k283_1_1
private theorem k283_1_3 : check w283 pick283 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k283_1_4 : check w283 pick283 1 t8752 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k283_1_5 : check w283 pick283 1 t8753 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w283 pick283 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t8752 k283_1_3 k283_1_4
private theorem k283_1_6 : check w283 pick283 1 t8754 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w283 pick283 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8753 k283_1_2 k283_1_5
theorem cov283_1 : PA.Covered 1 (OZ.Valid 1 w283.low w283.t w283.y w283.r w283.cap) (P33.root 1) :=
  Night6836Tree.sound w283 pick283 1 t8754 _ k283_1_6
theorem cov283_2 : PA.Covered 2 (OZ.Valid 2 w283.low w283.t w283.y w283.r w283.cap) (P33.root 2) :=
  Night6836Tree.sound w283 pick283 2 t8952 _ (by decide +kernel)
theorem cov283_3 : PA.Covered 3 (OZ.Valid 3 w283.low w283.t w283.y w283.r w283.cap) (P33.root 3) :=
  Night6836Tree.sound w283 pick283 3 t564 _ (by decide +kernel)
theorem cov283_4 : PA.Covered 4 (OZ.Valid 4 w283.low w283.t w283.y w283.r w283.cap) (P33.root 4) :=
  Night6836Tree.sound w283 pick283 4 t565 _ (by decide +kernel)
theorem cov283_5 : PA.Covered 5 (OZ.Valid 5 w283.low w283.t w283.y w283.r w283.cap) (P33.root 5) :=
  Night6836Tree.sound w283 pick283 5 t566 _ (by decide +kernel)
theorem cov283_6 : PA.Covered 6 (OZ.Valid 6 w283.low w283.t w283.y w283.r w283.cap) (P33.root 6) :=
  Night6836Tree.sound w283 pick283 6 t567 _ (by decide +kernel)
theorem cov283_7 : PA.Covered 7 (OZ.Valid 7 w283.low w283.t w283.y w283.r w283.cap) (P33.root 7) :=
  Night6836Tree.sound w283 pick283 7 t2134 _ (by decide +kernel)
theorem window283 : P33.WindowCount w283 := by
  apply P33.window_count w283 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov283_1
  · exact cov283_2
  · exact cov283_3
  · exact cov283_4
  · exact cov283_5
  · exact cov283_6
  · exact cov283_7
def w284 : P33.Window := ⟨14,42,3715,3464,240164495445190219,49633,57000,5000000,81920000000⟩
def h284_0 : Height w284 := ⟨49633,57000,by decide +kernel⟩
def h284_1 : Height w284 := ⟨53560,54000,by decide +kernel⟩
def h284_2 : Height w284 := ⟨57954,51000,by decide +kernel⟩
def h284_3 : Height w284 := ⟨62965,48000,by decide +kernel⟩
def h284_4 : Height w284 := ⟨68812,45000,by decide +kernel⟩
def h284_5 : Height w284 := ⟨75834,42000,by decide +kernel⟩
def h284_6 : Height w284 := ⟨84577,39000,by decide +kernel⟩
def pick284 (cl : ℕ) : Height w284 := if cl<14 then (if cl<2 then (h284_0) else (if cl<5 then (h284_1) else (h284_2))) else (if cl<95 then (if cl<36 then (h284_3) else (h284_4)) else (if cl<302 then (h284_5) else (h284_6)))
private theorem k284_1_0 : check w284 pick284 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k284_1_1 : check w284 pick284 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k284_1_2 : check w284 pick284 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w284 pick284 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k284_1_0 k284_1_1
private theorem k284_1_3 : check w284 pick284 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k284_1_4 : check w284 pick284 1 t8752 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k284_1_5 : check w284 pick284 1 t8753 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w284 pick284 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t8752 k284_1_3 k284_1_4
private theorem k284_1_6 : check w284 pick284 1 t8754 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w284 pick284 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8753 k284_1_2 k284_1_5
theorem cov284_1 : PA.Covered 1 (OZ.Valid 1 w284.low w284.t w284.y w284.r w284.cap) (P33.root 1) :=
  Night6836Tree.sound w284 pick284 1 t8754 _ k284_1_6
theorem cov284_2 : PA.Covered 2 (OZ.Valid 2 w284.low w284.t w284.y w284.r w284.cap) (P33.root 2) :=
  Night6836Tree.sound w284 pick284 2 t8957 _ (by decide +kernel)
theorem cov284_3 : PA.Covered 3 (OZ.Valid 3 w284.low w284.t w284.y w284.r w284.cap) (P33.root 3) :=
  Night6836Tree.sound w284 pick284 3 t564 _ (by decide +kernel)
theorem cov284_4 : PA.Covered 4 (OZ.Valid 4 w284.low w284.t w284.y w284.r w284.cap) (P33.root 4) :=
  Night6836Tree.sound w284 pick284 4 t565 _ (by decide +kernel)
theorem cov284_5 : PA.Covered 5 (OZ.Valid 5 w284.low w284.t w284.y w284.r w284.cap) (P33.root 5) :=
  Night6836Tree.sound w284 pick284 5 t566 _ (by decide +kernel)
theorem cov284_6 : PA.Covered 6 (OZ.Valid 6 w284.low w284.t w284.y w284.r w284.cap) (P33.root 6) :=
  Night6836Tree.sound w284 pick284 6 t567 _ (by decide +kernel)
theorem cov284_7 : PA.Covered 7 (OZ.Valid 7 w284.low w284.t w284.y w284.r w284.cap) (P33.root 7) :=
  Night6836Tree.sound w284 pick284 7 t2134 _ (by decide +kernel)
theorem window284 : P33.WindowCount w284 := by
  apply P33.window_count w284 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov284_1
  · exact cov284_2
  · exact cov284_3
  · exact cov284_4
  · exact cov284_5
  · exact cov284_6
  · exact cov284_7
def w285 : P33.Window := ⟨14,43,3463,3206,237496976911519272,58072,60000,5000000,81920000000⟩
def h285_0 : Height w285 := ⟨58072,60000,by decide +kernel⟩
def h285_1 : Height w285 := ⟨62264,57000,by decide +kernel⟩
def h285_2 : Height w285 := ⟨66952,54000,by decide +kernel⟩
def h285_3 : Height w285 := ⟨72285,51000,by decide +kernel⟩
def h285_4 : Height w285 := ⟨78481,48000,by decide +kernel⟩
def h285_5 : Height w285 := ⟨85867,45000,by decide +kernel⟩
def h285_6 : Height w285 := ⟨94958,42000,by decide +kernel⟩
def pick285 (cl : ℕ) : Height w285 := if cl<32 then (if cl<4 then (h285_0) else (if cl<10 then (h285_1) else (h285_2))) else (if cl<120 then (if cl<43 then (h285_3) else (h285_4)) else (if cl<312 then (h285_5) else (h285_6)))
private theorem k285_1_0 : check w285 pick285 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k285_1_1 : check w285 pick285 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k285_1_2 : check w285 pick285 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w285 pick285 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k285_1_0 k285_1_1
private theorem k285_1_3 : check w285 pick285 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k285_1_4 : check w285 pick285 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k285_1_5 : check w285 pick285 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w285 pick285 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k285_1_3 k285_1_4
private theorem k285_1_6 : check w285 pick285 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w285 pick285 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k285_1_2 k285_1_5
theorem cov285_1 : PA.Covered 1 (OZ.Valid 1 w285.low w285.t w285.y w285.r w285.cap) (P33.root 1) :=
  Night6836Tree.sound w285 pick285 1 t8759 _ k285_1_6
theorem cov285_2 : PA.Covered 2 (OZ.Valid 2 w285.low w285.t w285.y w285.r w285.cap) (P33.root 2) :=
  Night6836Tree.sound w285 pick285 2 t6560 _ (by decide +kernel)
theorem cov285_3 : PA.Covered 3 (OZ.Valid 3 w285.low w285.t w285.y w285.r w285.cap) (P33.root 3) :=
  Night6836Tree.sound w285 pick285 3 t564 _ (by decide +kernel)
theorem cov285_4 : PA.Covered 4 (OZ.Valid 4 w285.low w285.t w285.y w285.r w285.cap) (P33.root 4) :=
  Night6836Tree.sound w285 pick285 4 t565 _ (by decide +kernel)
theorem cov285_5 : PA.Covered 5 (OZ.Valid 5 w285.low w285.t w285.y w285.r w285.cap) (P33.root 5) :=
  Night6836Tree.sound w285 pick285 5 t566 _ (by decide +kernel)
theorem cov285_6 : PA.Covered 6 (OZ.Valid 6 w285.low w285.t w285.y w285.r w285.cap) (P33.root 6) :=
  Night6836Tree.sound w285 pick285 6 t567 _ (by decide +kernel)
theorem cov285_7 : PA.Covered 7 (OZ.Valid 7 w285.low w285.t w285.y w285.r w285.cap) (P33.root 7) :=
  Night6836Tree.sound w285 pick285 7 t2134 _ (by decide +kernel)
theorem window285 : P33.WindowCount w285 := by
  apply P33.window_count w285 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov285_1
  · exact cov285_2
  · exact cov285_3
  · exact cov285_4
  · exact cov285_5
  · exact cov285_6
  · exact cov285_7
def w286 : P33.Window := ⟨14,44,3205,2941,235733036055936335,65145,66000,5000000,81920000000⟩
def h286_0 : Height w286 := ⟨65145,66000,by decide +kernel⟩
def h286_1 : Height w286 := ⟨69308,63000,by decide +kernel⟩
def h286_2 : Height w286 := ⟨73906,60000,by decide +kernel⟩
def h286_3 : Height w286 := ⟨79055,57000,by decide +kernel⟩
def h286_4 : Height w286 := ⟨84915,54000,by decide +kernel⟩
def h286_5 : Height w286 := ⟨91715,51000,by decide +kernel⟩
def h286_6 : Height w286 := ⟨99796,48000,by decide +kernel⟩
def h286_7 : Height w286 := ⟨109681,45000,by decide +kernel⟩
def pick286 (cl : ℕ) : Height w286 := if cl<36 then (if cl<6 then (if cl<4 then (h286_0) else (h286_1)) else (if cl<18 then (h286_2) else (h286_3))) else (if cl<312 then (if cl<83 then (h286_4) else (h286_5)) else (if cl<498 then (h286_6) else (h286_7)))
private theorem k286_1_0 : check w286 pick286 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k286_1_1 : check w286 pick286 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k286_1_2 : check w286 pick286 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w286 pick286 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k286_1_0 k286_1_1
private theorem k286_1_3 : check w286 pick286 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k286_1_4 : check w286 pick286 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k286_1_5 : check w286 pick286 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w286 pick286 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k286_1_3 k286_1_4
private theorem k286_1_6 : check w286 pick286 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w286 pick286 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k286_1_2 k286_1_5
theorem cov286_1 : PA.Covered 1 (OZ.Valid 1 w286.low w286.t w286.y w286.r w286.cap) (P33.root 1) :=
  Night6836Tree.sound w286 pick286 1 t8759 _ k286_1_6
theorem cov286_2 : PA.Covered 2 (OZ.Valid 2 w286.low w286.t w286.y w286.r w286.cap) (P33.root 2) :=
  Night6836Tree.sound w286 pick286 2 t6560 _ (by decide +kernel)
theorem cov286_3 : PA.Covered 3 (OZ.Valid 3 w286.low w286.t w286.y w286.r w286.cap) (P33.root 3) :=
  Night6836Tree.sound w286 pick286 3 t564 _ (by decide +kernel)
theorem cov286_4 : PA.Covered 4 (OZ.Valid 4 w286.low w286.t w286.y w286.r w286.cap) (P33.root 4) :=
  Night6836Tree.sound w286 pick286 4 t565 _ (by decide +kernel)
theorem cov286_5 : PA.Covered 5 (OZ.Valid 5 w286.low w286.t w286.y w286.r w286.cap) (P33.root 5) :=
  Night6836Tree.sound w286 pick286 5 t566 _ (by decide +kernel)
theorem cov286_6 : PA.Covered 6 (OZ.Valid 6 w286.low w286.t w286.y w286.r w286.cap) (P33.root 6) :=
  Night6836Tree.sound w286 pick286 6 t567 _ (by decide +kernel)
theorem cov286_7 : PA.Covered 7 (OZ.Valid 7 w286.low w286.t w286.y w286.r w286.cap) (P33.root 7) :=
  Night6836Tree.sound w286 pick286 7 t2134 _ (by decide +kernel)
theorem window286 : P33.WindowCount w286 := by
  apply P33.window_count w286 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov286_1
  · exact cov286_2
  · exact cov286_3
  · exact cov286_4
  · exact cov286_5
  · exact cov286_6
  · exact cov286_7
def w287 : P33.Window := ⟨14,45,2940,2669,230139886025045442,71692,75000,5000000,81920000000⟩
def h287_0 : Height w287 := ⟨71692,75000,by decide +kernel⟩
def h287_1 : Height w287 := ⟨75650,72000,by decide +kernel⟩
def h287_2 : Height w287 := ⟨79947,69000,by decide +kernel⟩
def h287_3 : Height w287 := ⟨84658,66000,by decide +kernel⟩
def h287_4 : Height w287 := ⟨89884,63000,by decide +kernel⟩
def h287_5 : Height w287 := ⟨95758,60000,by decide +kernel⟩
def h287_6 : Height w287 := ⟨102465,57000,by decide +kernel⟩
def h287_7 : Height w287 := ⟨119542,51000,by decide +kernel⟩
def pick287 (cl : ℕ) : Height w287 := if cl<32 then (if cl<4 then (if cl<2 then (h287_0) else (h287_1)) else (if cl<10 then (h287_2) else (h287_3))) else (if cl<83 then (if cl<36 then (h287_4) else (h287_5)) else (if cl<312 then (h287_6) else (h287_7)))
private theorem k287_1_0 : check w287 pick287 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k287_1_1 : check w287 pick287 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k287_1_2 : check w287 pick287 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w287 pick287 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k287_1_0 k287_1_1
private theorem k287_1_3 : check w287 pick287 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k287_1_4 : check w287 pick287 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k287_1_5 : check w287 pick287 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w287 pick287 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k287_1_3 k287_1_4
private theorem k287_1_6 : check w287 pick287 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w287 pick287 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k287_1_2 k287_1_5
theorem cov287_1 : PA.Covered 1 (OZ.Valid 1 w287.low w287.t w287.y w287.r w287.cap) (P33.root 1) :=
  Night6836Tree.sound w287 pick287 1 t8759 _ k287_1_6
theorem cov287_2 : PA.Covered 2 (OZ.Valid 2 w287.low w287.t w287.y w287.r w287.cap) (P33.root 2) :=
  Night6836Tree.sound w287 pick287 2 t6560 _ (by decide +kernel)
theorem cov287_3 : PA.Covered 3 (OZ.Valid 3 w287.low w287.t w287.y w287.r w287.cap) (P33.root 3) :=
  Night6836Tree.sound w287 pick287 3 t564 _ (by decide +kernel)
theorem cov287_4 : PA.Covered 4 (OZ.Valid 4 w287.low w287.t w287.y w287.r w287.cap) (P33.root 4) :=
  Night6836Tree.sound w287 pick287 4 t565 _ (by decide +kernel)
theorem cov287_5 : PA.Covered 5 (OZ.Valid 5 w287.low w287.t w287.y w287.r w287.cap) (P33.root 5) :=
  Night6836Tree.sound w287 pick287 5 t566 _ (by decide +kernel)
theorem cov287_6 : PA.Covered 6 (OZ.Valid 6 w287.low w287.t w287.y w287.r w287.cap) (P33.root 6) :=
  Night6836Tree.sound w287 pick287 6 t567 _ (by decide +kernel)
theorem cov287_7 : PA.Covered 7 (OZ.Valid 7 w287.low w287.t w287.y w287.r w287.cap) (P33.root 7) :=
  Night6836Tree.sound w287 pick287 7 t2134 _ (by decide +kernel)
theorem window287 : P33.WindowCount w287 := by
  apply P33.window_count w287 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov287_1
  · exact cov287_2
  · exact cov287_3
  · exact cov287_4
  · exact cov287_5
  · exact cov287_6
  · exact cov287_7
def w288 : P33.Window := ⟨14,46,2668,2388,219679917764685693,83060,84000,5000000,81920000000⟩
def h288_0 : Height w288 := ⟨83060,84000,by decide +kernel⟩
def h288_1 : Height w288 := ⟨87040,81000,by decide +kernel⟩
def h288_2 : Height w288 := ⟨91321,78000,by decide +kernel⟩
def h288_3 : Height w288 := ⟨95961,75000,by decide +kernel⟩
def h288_4 : Height w288 := ⟨101033,72000,by decide +kernel⟩
def h288_5 : Height w288 := ⟨106633,69000,by decide +kernel⟩
def h288_6 : Height w288 := ⟨112887,66000,by decide +kernel⟩
def h288_7 : Height w288 := ⟨119963,63000,by decide +kernel⟩
def h288_8 : Height w288 := ⟨128095,60000,by decide +kernel⟩
def h288_9 : Height w288 := ⟨137609,57000,by decide +kernel⟩
def pick288 (cl : ℕ) : Height w288 := if cl<32 then (if cl<4 then (if cl<2 then (h288_0) else (h288_1)) else (if cl<6 then (h288_2) else (if cl<18 then (h288_3) else (h288_4)))) else (if cl<100 then (if cl<46 then (h288_5) else (h288_6)) else (if cl<312 then (h288_7) else (if cl<318 then (h288_8) else (h288_9))))
private theorem k288_1_0 : check w288 pick288 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k288_1_1 : check w288 pick288 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k288_1_2 : check w288 pick288 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w288 pick288 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k288_1_0 k288_1_1
private theorem k288_1_3 : check w288 pick288 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k288_1_4 : check w288 pick288 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k288_1_5 : check w288 pick288 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w288 pick288 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k288_1_3 k288_1_4
private theorem k288_1_6 : check w288 pick288 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w288 pick288 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k288_1_2 k288_1_5
theorem cov288_1 : PA.Covered 1 (OZ.Valid 1 w288.low w288.t w288.y w288.r w288.cap) (P33.root 1) :=
  Night6836Tree.sound w288 pick288 1 t8759 _ k288_1_6
theorem cov288_2 : PA.Covered 2 (OZ.Valid 2 w288.low w288.t w288.y w288.r w288.cap) (P33.root 2) :=
  Night6836Tree.sound w288 pick288 2 t6560 _ (by decide +kernel)
theorem cov288_3 : PA.Covered 3 (OZ.Valid 3 w288.low w288.t w288.y w288.r w288.cap) (P33.root 3) :=
  Night6836Tree.sound w288 pick288 3 t564 _ (by decide +kernel)
theorem cov288_4 : PA.Covered 4 (OZ.Valid 4 w288.low w288.t w288.y w288.r w288.cap) (P33.root 4) :=
  Night6836Tree.sound w288 pick288 4 t565 _ (by decide +kernel)
theorem cov288_5 : PA.Covered 5 (OZ.Valid 5 w288.low w288.t w288.y w288.r w288.cap) (P33.root 5) :=
  Night6836Tree.sound w288 pick288 5 t566 _ (by decide +kernel)
theorem cov288_6 : PA.Covered 6 (OZ.Valid 6 w288.low w288.t w288.y w288.r w288.cap) (P33.root 6) :=
  Night6836Tree.sound w288 pick288 6 t567 _ (by decide +kernel)
theorem cov288_7 : PA.Covered 7 (OZ.Valid 7 w288.low w288.t w288.y w288.r w288.cap) (P33.root 7) :=
  Night6836Tree.sound w288 pick288 7 t2134 _ (by decide +kernel)
theorem window288 : P33.WindowCount w288 := by
  apply P33.window_count w288 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov288_1
  · exact cov288_2
  · exact cov288_3
  · exact cov288_4
  · exact cov288_5
  · exact cov288_6
  · exact cov288_7
def w289 : P33.Window := ⟨14,47,2387,2100,208260526675949593,97393,96000,5000000,81920000000⟩
def h289_0 : Height w289 := ⟨97393,96000,by decide +kernel⟩
def h289_1 : Height w289 := ⟨101370,93000,by decide +kernel⟩
def h289_2 : Height w289 := ⟨105605,90000,by decide +kernel⟩
def h289_3 : Height w289 := ⟨110139,87000,by decide +kernel⟩
def h289_4 : Height w289 := ⟨115025,84000,by decide +kernel⟩
def h289_5 : Height w289 := ⟨126125,78000,by decide +kernel⟩
def h289_6 : Height w289 := ⟨132524,75000,by decide +kernel⟩
def h289_7 : Height w289 := ⟨139659,72000,by decide +kernel⟩
def h289_8 : Height w289 := ⟨156908,66000,by decide +kernel⟩
def pick289 (cl : ℕ) : Height w289 := if cl<12 then (if cl<4 then (if cl<2 then (h289_0) else (h289_1)) else (if cl<6 then (h289_2) else (h289_3))) else (if cl<55 then (if cl<32 then (h289_4) else (h289_5)) else (if cl<105 then (h289_6) else (if cl<312 then (h289_7) else (h289_8))))
private theorem k289_1_0 : check w289 pick289 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k289_1_1 : check w289 pick289 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k289_1_2 : check w289 pick289 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w289 pick289 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k289_1_0 k289_1_1
private theorem k289_1_3 : check w289 pick289 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k289_1_4 : check w289 pick289 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k289_1_5 : check w289 pick289 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w289 pick289 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k289_1_3 k289_1_4
private theorem k289_1_6 : check w289 pick289 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w289 pick289 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k289_1_2 k289_1_5
theorem cov289_1 : PA.Covered 1 (OZ.Valid 1 w289.low w289.t w289.y w289.r w289.cap) (P33.root 1) :=
  Night6836Tree.sound w289 pick289 1 t8759 _ k289_1_6
theorem cov289_2 : PA.Covered 2 (OZ.Valid 2 w289.low w289.t w289.y w289.r w289.cap) (P33.root 2) :=
  Night6836Tree.sound w289 pick289 2 t6618 _ (by decide +kernel)
theorem cov289_3 : PA.Covered 3 (OZ.Valid 3 w289.low w289.t w289.y w289.r w289.cap) (P33.root 3) :=
  Night6836Tree.sound w289 pick289 3 t564 _ (by decide +kernel)
theorem cov289_4 : PA.Covered 4 (OZ.Valid 4 w289.low w289.t w289.y w289.r w289.cap) (P33.root 4) :=
  Night6836Tree.sound w289 pick289 4 t565 _ (by decide +kernel)
theorem cov289_5 : PA.Covered 5 (OZ.Valid 5 w289.low w289.t w289.y w289.r w289.cap) (P33.root 5) :=
  Night6836Tree.sound w289 pick289 5 t566 _ (by decide +kernel)
theorem cov289_6 : PA.Covered 6 (OZ.Valid 6 w289.low w289.t w289.y w289.r w289.cap) (P33.root 6) :=
  Night6836Tree.sound w289 pick289 6 t567 _ (by decide +kernel)
theorem cov289_7 : PA.Covered 7 (OZ.Valid 7 w289.low w289.t w289.y w289.r w289.cap) (P33.root 7) :=
  Night6836Tree.sound w289 pick289 7 t2134 _ (by decide +kernel)
theorem window289 : P33.WindowCount w289 := by
  apply P33.window_count w289 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov289_1
  · exact cov289_2
  · exact cov289_3
  · exact cov289_4
  · exact cov289_5
  · exact cov289_6
  · exact cov289_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w290 : P33.Window := ⟨14,48,2099,1803,231042094228945686,118603,111000,5000000,81920000000⟩
def h290_0 : Height w290 := ⟨118603,111000,by decide +kernel⟩
def h290_1 : Height w290 := ⟨122668,108000,by decide +kernel⟩
def h290_2 : Height w290 := ⟨126960,105000,by decide +kernel⟩
def h290_3 : Height w290 := ⟨131510,102000,by decide +kernel⟩
def h290_4 : Height w290 := ⟨136357,99000,by decide +kernel⟩
def h290_5 : Height w290 := ⟨147129,93000,by decide +kernel⟩
def h290_6 : Height w290 := ⟨153177,90000,by decide +kernel⟩
def h290_7 : Height w290 := ⟨159771,87000,by decide +kernel⟩
def h290_8 : Height w290 := ⟨167016,84000,by decide +kernel⟩
def h290_9 : Height w290 := ⟨184023,78000,by decide +kernel⟩
def h290_10 : Height w290 := ⟨194177,75000,by decide +kernel⟩
def pick290 (cl : ℕ) : Height w290 := if cl<32 then (if cl<4 then (if cl<2 then (h290_0) else (h290_1)) else (if cl<6 then (h290_2) else (if cl<12 then (h290_3) else (h290_4)))) else (if cl<107 then (if cl<40 then (h290_5) else (if cl<70 then (h290_6) else (h290_7))) else (if cl<312 then (h290_8) else (if cl<561 then (h290_9) else (h290_10))))
private theorem k290_1_0 : check w290 pick290 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k290_1_1 : check w290 pick290 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k290_1_2 : check w290 pick290 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w290 pick290 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k290_1_0 k290_1_1
private theorem k290_1_3 : check w290 pick290 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k290_1_4 : check w290 pick290 1 t8767 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k290_1_5 : check w290 pick290 1 t8768 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w290 pick290 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8767 k290_1_3 k290_1_4
private theorem k290_1_6 : check w290 pick290 1 t8958 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w290 pick290 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8768 k290_1_2 k290_1_5
theorem cov290_1 : PA.Covered 1 (OZ.Valid 1 w290.low w290.t w290.y w290.r w290.cap) (P33.root 1) :=
  Night6836Tree.sound w290 pick290 1 t8958 _ k290_1_6
theorem cov290_2 : PA.Covered 2 (OZ.Valid 2 w290.low w290.t w290.y w290.r w290.cap) (P33.root 2) :=
  Night6836Tree.sound w290 pick290 2 t6618 _ (by decide +kernel)
theorem cov290_3 : PA.Covered 3 (OZ.Valid 3 w290.low w290.t w290.y w290.r w290.cap) (P33.root 3) :=
  Night6836Tree.sound w290 pick290 3 t564 _ (by decide +kernel)
theorem cov290_4 : PA.Covered 4 (OZ.Valid 4 w290.low w290.t w290.y w290.r w290.cap) (P33.root 4) :=
  Night6836Tree.sound w290 pick290 4 t565 _ (by decide +kernel)
theorem cov290_5 : PA.Covered 5 (OZ.Valid 5 w290.low w290.t w290.y w290.r w290.cap) (P33.root 5) :=
  Night6836Tree.sound w290 pick290 5 t566 _ (by decide +kernel)
theorem cov290_6 : PA.Covered 6 (OZ.Valid 6 w290.low w290.t w290.y w290.r w290.cap) (P33.root 6) :=
  Night6836Tree.sound w290 pick290 6 t567 _ (by decide +kernel)
theorem cov290_7 : PA.Covered 7 (OZ.Valid 7 w290.low w290.t w290.y w290.r w290.cap) (P33.root 7) :=
  Night6836Tree.sound w290 pick290 7 t2134 _ (by decide +kernel)
theorem window290 : P33.WindowCount w290 := by
  apply P33.window_count w290 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov290_1
  · exact cov290_2
  · exact cov290_3
  · exact cov290_4
  · exact cov290_5
  · exact cov290_6
  · exact cov290_7
def w291 : P33.Window := ⟨14,49,1802,1704,205600287217529650,126555,120000,5000000,81920000000⟩
def h291_0 : Height w291 := ⟨126555,120000,by decide +kernel⟩
def h291_1 : Height w291 := ⟨130502,117000,by decide +kernel⟩
def h291_2 : Height w291 := ⟨134646,114000,by decide +kernel⟩
def h291_3 : Height w291 := ⟨139011,111000,by decide +kernel⟩
def h291_4 : Height w291 := ⟨143626,108000,by decide +kernel⟩
def h291_5 : Height w291 := ⟨148525,105000,by decide +kernel⟩
def h291_6 : Height w291 := ⟨159347,99000,by decide +kernel⟩
def h291_7 : Height w291 := ⟨165376,96000,by decide +kernel⟩
def h291_8 : Height w291 := ⟨171910,93000,by decide +kernel⟩
def h291_9 : Height w291 := ⟨179036,90000,by decide +kernel⟩
def h291_10 : Height w291 := ⟨195536,84000,by decide +kernel⟩
def h291_11 : Height w291 := ⟨205225,81000,by decide +kernel⟩
def pick291 (cl : ℕ) : Height w291 := if cl<32 then (if cl<5 then (if cl<2 then (h291_0) else (if cl<3 then (h291_1) else (h291_2))) else (if cl<6 then (h291_3) else (if cl<12 then (h291_4) else (h291_5)))) else (if cl<100 then (if cl<40 then (h291_6) else (if cl<62 then (h291_7) else (h291_8))) else (if cl<312 then (h291_9) else (if cl<359 then (h291_10) else (h291_11))))
private theorem k291_1_0 : check w291 pick291 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k291_1_1 : check w291 pick291 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k291_1_2 : check w291 pick291 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w291 pick291 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k291_1_0 k291_1_1
private theorem k291_1_3 : check w291 pick291 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k291_1_4 : check w291 pick291 1 t8767 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k291_1_5 : check w291 pick291 1 t8768 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w291 pick291 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8767 k291_1_3 k291_1_4
private theorem k291_1_6 : check w291 pick291 1 t8958 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w291 pick291 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8768 k291_1_2 k291_1_5
theorem cov291_1 : PA.Covered 1 (OZ.Valid 1 w291.low w291.t w291.y w291.r w291.cap) (P33.root 1) :=
  Night6836Tree.sound w291 pick291 1 t8958 _ k291_1_6
theorem cov291_2 : PA.Covered 2 (OZ.Valid 2 w291.low w291.t w291.y w291.r w291.cap) (P33.root 2) :=
  Night6836Tree.sound w291 pick291 2 t6666 _ (by decide +kernel)
theorem cov291_3 : PA.Covered 3 (OZ.Valid 3 w291.low w291.t w291.y w291.r w291.cap) (P33.root 3) :=
  Night6836Tree.sound w291 pick291 3 t564 _ (by decide +kernel)
theorem cov291_4 : PA.Covered 4 (OZ.Valid 4 w291.low w291.t w291.y w291.r w291.cap) (P33.root 4) :=
  Night6836Tree.sound w291 pick291 4 t565 _ (by decide +kernel)
theorem cov291_5 : PA.Covered 5 (OZ.Valid 5 w291.low w291.t w291.y w291.r w291.cap) (P33.root 5) :=
  Night6836Tree.sound w291 pick291 5 t566 _ (by decide +kernel)
theorem cov291_6 : PA.Covered 6 (OZ.Valid 6 w291.low w291.t w291.y w291.r w291.cap) (P33.root 6) :=
  Night6836Tree.sound w291 pick291 6 t567 _ (by decide +kernel)
theorem cov291_7 : PA.Covered 7 (OZ.Valid 7 w291.low w291.t w291.y w291.r w291.cap) (P33.root 7) :=
  Night6836Tree.sound w291 pick291 7 t2134 _ (by decide +kernel)
theorem window291 : P33.WindowCount w291 := by
  apply P33.window_count w291 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov291_1
  · exact cov291_2
  · exact cov291_3
  · exact cov291_4
  · exact cov291_5
  · exact cov291_6
  · exact cov291_7
def w292 : P33.Window := ⟨15,18,6922,6653,243847382217083371,6533,21000,5000000,81920000000⟩
def h292_0 : Height w292 := ⟨6533,21000,by decide +kernel⟩
def h292_1 : Height w292 := ⟨12092,18000,by decide +kernel⟩
def h292_2 : Height w292 := ⟨24086,15000,by decide +kernel⟩
def pick292 (cl : ℕ) : Height w292 := if cl<32 then (h292_0) else (if cl<922 then (h292_1) else (h292_2))
private theorem k292_1_0 : check w292 pick292 1 t8960 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k292_1_1 : check w292 pick292 1 t2523 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k292_1_2 : check w292 pick292 1 t8961 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w292 pick292 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t8960 t2523 k292_1_0 k292_1_1
private theorem k292_1_3 : check w292 pick292 1 t8982 ⟨1,7,2,16,1,52,84,145⟩ = true := by decide +kernel
private theorem k292_1_4 : check w292 pick292 1 t8983 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w292 pick292 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t8961 t8982 k292_1_2 k292_1_3
private theorem k292_1_5 : check w292 pick292 1 t8988 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k292_1_6 : check w292 pick292 1 t8999 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k292_1_7 : check w292 pick292 1 t9000 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w292 pick292 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t8988 t8999 k292_1_5 k292_1_6
private theorem k292_1_8 : check w292 pick292 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k292_1_9 : check w292 pick292 1 t9001 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w292 pick292 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t9000 t7097 k292_1_7 k292_1_8
private theorem k292_1_10 : check w292 pick292 1 t9002 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w292 pick292 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t8983 t9001 k292_1_4 k292_1_9
theorem cov292_1 : PA.Covered 1 (OZ.Valid 1 w292.low w292.t w292.y w292.r w292.cap) (P33.root 1) :=
  Night6836Tree.sound w292 pick292 1 t9002 _ k292_1_10
theorem cov292_2 : PA.Covered 2 (OZ.Valid 2 w292.low w292.t w292.y w292.r w292.cap) (P33.root 2) :=
  Night6836Tree.sound w292 pick292 2 t8398 _ (by decide +kernel)
theorem cov292_3 : PA.Covered 3 (OZ.Valid 3 w292.low w292.t w292.y w292.r w292.cap) (P33.root 3) :=
  Night6836Tree.sound w292 pick292 3 t564 _ (by decide +kernel)
theorem cov292_4 : PA.Covered 4 (OZ.Valid 4 w292.low w292.t w292.y w292.r w292.cap) (P33.root 4) :=
  Night6836Tree.sound w292 pick292 4 t565 _ (by decide +kernel)
theorem cov292_5 : PA.Covered 5 (OZ.Valid 5 w292.low w292.t w292.y w292.r w292.cap) (P33.root 5) :=
  Night6836Tree.sound w292 pick292 5 t566 _ (by decide +kernel)
theorem cov292_6 : PA.Covered 6 (OZ.Valid 6 w292.low w292.t w292.y w292.r w292.cap) (P33.root 6) :=
  Night6836Tree.sound w292 pick292 6 t567 _ (by decide +kernel)
theorem cov292_7 : PA.Covered 7 (OZ.Valid 7 w292.low w292.t w292.y w292.r w292.cap) (P33.root 7) :=
  Night6836Tree.sound w292 pick292 7 t568 _ (by decide +kernel)
theorem window292 : P33.WindowCount w292 := by
  apply P33.window_count w292 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov292_1
  · exact cov292_2
  · exact cov292_3
  · exact cov292_4
  · exact cov292_5
  · exact cov292_6
  · exact cov292_7
def w293 : P33.Window := ⟨15,19,6815,6653,244420371237161255,8153,21000,5000000,81920000000⟩
def h293_0 : Height w293 := ⟨8153,21000,by decide +kernel⟩
def h293_1 : Height w293 := ⟨14094,18000,by decide +kernel⟩
def h293_2 : Height w293 := ⟨27065,15000,by decide +kernel⟩
def pick293 (cl : ℕ) : Height w293 := if cl<36 then (h293_0) else (if cl<961 then (h293_1) else (h293_2))
private theorem k293_1_0 : check w293 pick293 1 t8960 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k293_1_1 : check w293 pick293 1 t2523 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k293_1_2 : check w293 pick293 1 t8961 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w293 pick293 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t8960 t2523 k293_1_0 k293_1_1
private theorem k293_1_3 : check w293 pick293 1 t9008 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k293_1_4 : check w293 pick293 1 t9009 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w293 pick293 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8961 t9008 k293_1_2 k293_1_3
private theorem k293_1_5 : check w293 pick293 1 t8821 ⟨1,7,2,16,1,52,139,192⟩ = true := by decide +kernel
private theorem k293_1_6 : check w293 pick293 1 t8824 ⟨1,7,2,16,1,52,193,450⟩ = true := by decide +kernel
private theorem k293_1_7 : check w293 pick293 1 t8825 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w293 pick293 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t8821 t8824 k293_1_5 k293_1_6
private theorem k293_1_8 : check w293 pick293 1 t9010 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w293 pick293 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9009 t8825 k293_1_4 k293_1_7
theorem cov293_1 : PA.Covered 1 (OZ.Valid 1 w293.low w293.t w293.y w293.r w293.cap) (P33.root 1) :=
  Night6836Tree.sound w293 pick293 1 t9010 _ k293_1_8
theorem cov293_2 : PA.Covered 2 (OZ.Valid 2 w293.low w293.t w293.y w293.r w293.cap) (P33.root 2) :=
  Night6836Tree.sound w293 pick293 2 t8398 _ (by decide +kernel)
theorem cov293_3 : PA.Covered 3 (OZ.Valid 3 w293.low w293.t w293.y w293.r w293.cap) (P33.root 3) :=
  Night6836Tree.sound w293 pick293 3 t564 _ (by decide +kernel)
theorem cov293_4 : PA.Covered 4 (OZ.Valid 4 w293.low w293.t w293.y w293.r w293.cap) (P33.root 4) :=
  Night6836Tree.sound w293 pick293 4 t565 _ (by decide +kernel)
theorem cov293_5 : PA.Covered 5 (OZ.Valid 5 w293.low w293.t w293.y w293.r w293.cap) (P33.root 5) :=
  Night6836Tree.sound w293 pick293 5 t566 _ (by decide +kernel)
theorem cov293_6 : PA.Covered 6 (OZ.Valid 6 w293.low w293.t w293.y w293.r w293.cap) (P33.root 6) :=
  Night6836Tree.sound w293 pick293 6 t567 _ (by decide +kernel)
theorem cov293_7 : PA.Covered 7 (OZ.Valid 7 w293.low w293.t w293.y w293.r w293.cap) (P33.root 7) :=
  Night6836Tree.sound w293 pick293 7 t568 _ (by decide +kernel)
theorem window293 : P33.WindowCount w293 := by
  apply P33.window_count w293 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov293_1
  · exact cov293_2
  · exact cov293_3
  · exact cov293_4
  · exact cov293_5
  · exact cov293_6
  · exact cov293_7
def w294 : P33.Window := ⟨15,20,6652,5792,243375323950963998,7231,27000,5000000,81920000000⟩
def h294_0 : Height w294 := ⟨7231,27000,by decide +kernel⟩
def h294_1 : Height w294 := ⟨11420,24000,by decide +kernel⟩
def h294_2 : Height w294 := ⟨17597,21000,by decide +kernel⟩
def h294_3 : Height w294 := ⟨29236,18000,by decide +kernel⟩
def pick294 (cl : ℕ) : Height w294 := if cl<43 then (if cl<4 then (h294_0) else (h294_1)) else (if cl<922 then (h294_2) else (h294_3))
private theorem k294_1_0 : check w294 pick294 1 t9016 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k294_1_1 : check w294 pick294 1 t9019 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k294_1_2 : check w294 pick294 1 t9020 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w294 pick294 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9016 t9019 k294_1_0 k294_1_1
private theorem k294_1_3 : check w294 pick294 1 t8821 ⟨1,7,2,16,1,52,139,192⟩ = true := by decide +kernel
private theorem k294_1_4 : check w294 pick294 1 t8824 ⟨1,7,2,16,1,52,193,450⟩ = true := by decide +kernel
private theorem k294_1_5 : check w294 pick294 1 t8825 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w294 pick294 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t8821 t8824 k294_1_3 k294_1_4
private theorem k294_1_6 : check w294 pick294 1 t9021 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w294 pick294 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9020 t8825 k294_1_2 k294_1_5
theorem cov294_1 : PA.Covered 1 (OZ.Valid 1 w294.low w294.t w294.y w294.r w294.cap) (P33.root 1) :=
  Night6836Tree.sound w294 pick294 1 t9021 _ k294_1_6
theorem cov294_2 : PA.Covered 2 (OZ.Valid 2 w294.low w294.t w294.y w294.r w294.cap) (P33.root 2) :=
  Night6836Tree.sound w294 pick294 2 t9024 _ (by decide +kernel)
theorem cov294_3 : PA.Covered 3 (OZ.Valid 3 w294.low w294.t w294.y w294.r w294.cap) (P33.root 3) :=
  Night6836Tree.sound w294 pick294 3 t564 _ (by decide +kernel)
theorem cov294_4 : PA.Covered 4 (OZ.Valid 4 w294.low w294.t w294.y w294.r w294.cap) (P33.root 4) :=
  Night6836Tree.sound w294 pick294 4 t565 _ (by decide +kernel)
theorem cov294_5 : PA.Covered 5 (OZ.Valid 5 w294.low w294.t w294.y w294.r w294.cap) (P33.root 5) :=
  Night6836Tree.sound w294 pick294 5 t566 _ (by decide +kernel)
theorem cov294_6 : PA.Covered 6 (OZ.Valid 6 w294.low w294.t w294.y w294.r w294.cap) (P33.root 6) :=
  Night6836Tree.sound w294 pick294 6 t567 _ (by decide +kernel)
theorem cov294_7 : PA.Covered 7 (OZ.Valid 7 w294.low w294.t w294.y w294.r w294.cap) (P33.root 7) :=
  Night6836Tree.sound w294 pick294 7 t568 _ (by decide +kernel)
theorem window294 : P33.WindowCount w294 := by
  apply P33.window_count w294 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov294_1
  · exact cov294_2
  · exact cov294_3
  · exact cov294_4
  · exact cov294_5
  · exact cov294_6
  · exact cov294_7
def w295 : P33.Window := ⟨15,21,6486,5792,243922883722046847,8887,27000,5000000,81920000000⟩
def h295_0 : Height w295 := ⟨8887,27000,by decide +kernel⟩
def h295_1 : Height w295 := ⟨13290,24000,by decide +kernel⟩
def h295_2 : Height w295 := ⟨19835,21000,by decide +kernel⟩
def h295_3 : Height w295 := ⟨32264,18000,by decide +kernel⟩
def pick295 (cl : ℕ) : Height w295 := if cl<62 then (if cl<5 then (h295_0) else (h295_1)) else (if cl<961 then (h295_2) else (h295_3))
private theorem k295_1_0 : check w295 pick295 1 t8960 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k295_1_1 : check w295 pick295 1 t2523 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k295_1_2 : check w295 pick295 1 t8961 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w295 pick295 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t8960 t2523 k295_1_0 k295_1_1
private theorem k295_1_3 : check w295 pick295 1 t9027 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k295_1_4 : check w295 pick295 1 t9028 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w295 pick295 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8961 t9027 k295_1_2 k295_1_3
private theorem k295_1_5 : check w295 pick295 1 t8821 ⟨1,7,2,16,1,52,139,192⟩ = true := by decide +kernel
private theorem k295_1_6 : check w295 pick295 1 t8824 ⟨1,7,2,16,1,52,193,450⟩ = true := by decide +kernel
private theorem k295_1_7 : check w295 pick295 1 t8825 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w295 pick295 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t8821 t8824 k295_1_5 k295_1_6
private theorem k295_1_8 : check w295 pick295 1 t9029 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w295 pick295 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9028 t8825 k295_1_4 k295_1_7
theorem cov295_1 : PA.Covered 1 (OZ.Valid 1 w295.low w295.t w295.y w295.r w295.cap) (P33.root 1) :=
  Night6836Tree.sound w295 pick295 1 t9029 _ k295_1_8
theorem cov295_2 : PA.Covered 2 (OZ.Valid 2 w295.low w295.t w295.y w295.r w295.cap) (P33.root 2) :=
  Night6836Tree.sound w295 pick295 2 t8398 _ (by decide +kernel)
theorem cov295_3 : PA.Covered 3 (OZ.Valid 3 w295.low w295.t w295.y w295.r w295.cap) (P33.root 3) :=
  Night6836Tree.sound w295 pick295 3 t564 _ (by decide +kernel)
theorem cov295_4 : PA.Covered 4 (OZ.Valid 4 w295.low w295.t w295.y w295.r w295.cap) (P33.root 4) :=
  Night6836Tree.sound w295 pick295 4 t565 _ (by decide +kernel)
theorem cov295_5 : PA.Covered 5 (OZ.Valid 5 w295.low w295.t w295.y w295.r w295.cap) (P33.root 5) :=
  Night6836Tree.sound w295 pick295 5 t566 _ (by decide +kernel)
theorem cov295_6 : PA.Covered 6 (OZ.Valid 6 w295.low w295.t w295.y w295.r w295.cap) (P33.root 6) :=
  Night6836Tree.sound w295 pick295 6 t567 _ (by decide +kernel)
theorem cov295_7 : PA.Covered 7 (OZ.Valid 7 w295.low w295.t w295.y w295.r w295.cap) (P33.root 7) :=
  Night6836Tree.sound w295 pick295 7 t568 _ (by decide +kernel)
theorem window295 : P33.WindowCount w295 := by
  apply P33.window_count w295 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov295_1
  · exact cov295_2
  · exact cov295_3
  · exact cov295_4
  · exact cov295_5
  · exact cov295_6
  · exact cov295_7
def w296 : P33.Window := ⟨15,22,6317,6146,244357627659879648,8020,27000,5000000,81920000000⟩
def h296_0 : Height w296 := ⟨8020,27000,by decide +kernel⟩
def h296_1 : Height w296 := ⟨11985,24000,by decide +kernel⟩
def h296_2 : Height w296 := ⟨17618,21000,by decide +kernel⟩
def h296_3 : Height w296 := ⟨27471,18000,by decide +kernel⟩
def pick296 (cl : ℕ) : Height w296 := if cl<32 then (if cl<2 then (h296_0) else (h296_1)) else (if cl<431 then (h296_2) else (h296_3))
private theorem k296_1_0 : check w296 pick296 1 t8960 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k296_1_1 : check w296 pick296 1 t2523 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k296_1_2 : check w296 pick296 1 t8961 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w296 pick296 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t8960 t2523 k296_1_0 k296_1_1
private theorem k296_1_3 : check w296 pick296 1 t9034 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k296_1_4 : check w296 pick296 1 t9035 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w296 pick296 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8961 t9034 k296_1_2 k296_1_3
private theorem k296_1_5 : check w296 pick296 1 t8821 ⟨1,7,2,16,1,52,139,192⟩ = true := by decide +kernel
private theorem k296_1_6 : check w296 pick296 1 t8824 ⟨1,7,2,16,1,52,193,450⟩ = true := by decide +kernel
private theorem k296_1_7 : check w296 pick296 1 t8825 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w296 pick296 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t8821 t8824 k296_1_5 k296_1_6
private theorem k296_1_8 : check w296 pick296 1 t9036 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w296 pick296 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9035 t8825 k296_1_4 k296_1_7
theorem cov296_1 : PA.Covered 1 (OZ.Valid 1 w296.low w296.t w296.y w296.r w296.cap) (P33.root 1) :=
  Night6836Tree.sound w296 pick296 1 t9036 _ k296_1_8
theorem cov296_2 : PA.Covered 2 (OZ.Valid 2 w296.low w296.t w296.y w296.r w296.cap) (P33.root 2) :=
  Night6836Tree.sound w296 pick296 2 t9037 _ (by decide +kernel)
theorem cov296_3 : PA.Covered 3 (OZ.Valid 3 w296.low w296.t w296.y w296.r w296.cap) (P33.root 3) :=
  Night6836Tree.sound w296 pick296 3 t564 _ (by decide +kernel)
theorem cov296_4 : PA.Covered 4 (OZ.Valid 4 w296.low w296.t w296.y w296.r w296.cap) (P33.root 4) :=
  Night6836Tree.sound w296 pick296 4 t565 _ (by decide +kernel)
theorem cov296_5 : PA.Covered 5 (OZ.Valid 5 w296.low w296.t w296.y w296.r w296.cap) (P33.root 5) :=
  Night6836Tree.sound w296 pick296 5 t566 _ (by decide +kernel)
theorem cov296_6 : PA.Covered 6 (OZ.Valid 6 w296.low w296.t w296.y w296.r w296.cap) (P33.root 6) :=
  Night6836Tree.sound w296 pick296 6 t567 _ (by decide +kernel)
theorem cov296_7 : PA.Covered 7 (OZ.Valid 7 w296.low w296.t w296.y w296.r w296.cap) (P33.root 7) :=
  Night6836Tree.sound w296 pick296 7 t2134 _ (by decide +kernel)
theorem window296 : P33.WindowCount w296 := by
  apply P33.window_count w296 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov296_1
  · exact cov296_2
  · exact cov296_3
  · exact cov296_4
  · exact cov296_5
  · exact cov296_6
  · exact cov296_7
def w297 : P33.Window := ⟨15,23,6145,5900,239996244431133655,11312,27000,5000000,81920000000⟩
def h297_0 : Height w297 := ⟨11312,27000,by decide +kernel⟩
def h297_1 : Height w297 := ⟨15900,24000,by decide +kernel⟩
def h297_2 : Height w297 := ⟨22704,21000,by decide +kernel⟩
def h297_3 : Height w297 := ⟨35411,18000,by decide +kernel⟩
def pick297 (cl : ℕ) : Height w297 := if cl<83 then (if cl<6 then (h297_0) else (h297_1)) else (if cl<961 then (h297_2) else (h297_3))
private theorem k297_1_0 : check w297 pick297 1 t9040 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k297_1_1 : check w297 pick297 1 t9050 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k297_1_2 : check w297 pick297 1 t9051 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w297 pick297 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t9040 t9050 k297_1_0 k297_1_1
private theorem k297_1_3 : check w297 pick297 1 t8848 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k297_1_4 : check w297 pick297 1 t8814 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k297_1_5 : check w297 pick297 1 t8849 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w297 pick297 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t8848 t8814 k297_1_3 k297_1_4
private theorem k297_1_6 : check w297 pick297 1 t9052 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w297 pick297 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9051 t8849 k297_1_2 k297_1_5
private theorem k297_1_7 : check w297 pick297 1 t8819 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k297_1_8 : check w297 pick297 1 t9054 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k297_1_9 : check w297 pick297 1 t9055 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w297 pick297 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t8819 t9054 k297_1_7 k297_1_8
private theorem k297_1_10 : check w297 pick297 1 t9056 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k297_1_11 : check w297 pick297 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k297_1_12 : check w297 pick297 1 t9057 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w297 pick297 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t9056 t7318 k297_1_10 k297_1_11
private theorem k297_1_13 : check w297 pick297 1 t9058 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w297 pick297 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9055 t9057 k297_1_9 k297_1_12
private theorem k297_1_14 : check w297 pick297 1 t9059 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w297 pick297 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9052 t9058 k297_1_6 k297_1_13
theorem cov297_1 : PA.Covered 1 (OZ.Valid 1 w297.low w297.t w297.y w297.r w297.cap) (P33.root 1) :=
  Night6836Tree.sound w297 pick297 1 t9059 _ k297_1_14
theorem cov297_2 : PA.Covered 2 (OZ.Valid 2 w297.low w297.t w297.y w297.r w297.cap) (P33.root 2) :=
  Night6836Tree.sound w297 pick297 2 t8873 _ (by decide +kernel)
theorem cov297_3 : PA.Covered 3 (OZ.Valid 3 w297.low w297.t w297.y w297.r w297.cap) (P33.root 3) :=
  Night6836Tree.sound w297 pick297 3 t564 _ (by decide +kernel)
theorem cov297_4 : PA.Covered 4 (OZ.Valid 4 w297.low w297.t w297.y w297.r w297.cap) (P33.root 4) :=
  Night6836Tree.sound w297 pick297 4 t565 _ (by decide +kernel)
theorem cov297_5 : PA.Covered 5 (OZ.Valid 5 w297.low w297.t w297.y w297.r w297.cap) (P33.root 5) :=
  Night6836Tree.sound w297 pick297 5 t566 _ (by decide +kernel)
theorem cov297_6 : PA.Covered 6 (OZ.Valid 6 w297.low w297.t w297.y w297.r w297.cap) (P33.root 6) :=
  Night6836Tree.sound w297 pick297 6 t567 _ (by decide +kernel)
theorem cov297_7 : PA.Covered 7 (OZ.Valid 7 w297.low w297.t w297.y w297.r w297.cap) (P33.root 7) :=
  Night6836Tree.sound w297 pick297 7 t2134 _ (by decide +kernel)
theorem window297 : P33.WindowCount w297 := by
  apply P33.window_count w297 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov297_1
  · exact cov297_2
  · exact cov297_3
  · exact cov297_4
  · exact cov297_5
  · exact cov297_6
  · exact cov297_7
def w298 : P33.Window := ⟨15,24,5970,5792,244220157376483291,13853,27000,5000000,81920000000⟩
def h298_0 : Height w298 := ⟨13853,27000,by decide +kernel⟩
def h298_1 : Height w298 := ⟨18893,24000,by decide +kernel⟩
def h298_2 : Height w298 := ⟨26540,21000,by decide +kernel⟩
def h298_3 : Height w298 := ⟨41322,18000,by decide +kernel⟩
def pick298 (cl : ℕ) : Height w298 := if cl<302 then (if cl<14 then (h298_0) else (h298_1)) else (if cl<1021 then (h298_2) else (h298_3))
private theorem k298_1_0 : check w298 pick298 1 t7116 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k298_1_1 : check w298 pick298 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k298_1_2 : check w298 pick298 1 t7117 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w298 pick298 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7116 t7032 k298_1_0 k298_1_1
private theorem k298_1_3 : check w298 pick298 1 t7064 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k298_1_4 : check w298 pick298 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k298_1_5 : check w298 pick298 1 t7098 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w298 pick298 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7064 t7097 k298_1_3 k298_1_4
private theorem k298_1_6 : check w298 pick298 1 t7118 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w298 pick298 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7117 t7098 k298_1_2 k298_1_5
theorem cov298_1 : PA.Covered 1 (OZ.Valid 1 w298.low w298.t w298.y w298.r w298.cap) (P33.root 1) :=
  Night6836Tree.sound w298 pick298 1 t7118 _ k298_1_6
theorem cov298_2 : PA.Covered 2 (OZ.Valid 2 w298.low w298.t w298.y w298.r w298.cap) (P33.root 2) :=
  Night6836Tree.sound w298 pick298 2 t8398 _ (by decide +kernel)
theorem cov298_3 : PA.Covered 3 (OZ.Valid 3 w298.low w298.t w298.y w298.r w298.cap) (P33.root 3) :=
  Night6836Tree.sound w298 pick298 3 t564 _ (by decide +kernel)
theorem cov298_4 : PA.Covered 4 (OZ.Valid 4 w298.low w298.t w298.y w298.r w298.cap) (P33.root 4) :=
  Night6836Tree.sound w298 pick298 4 t565 _ (by decide +kernel)
theorem cov298_5 : PA.Covered 5 (OZ.Valid 5 w298.low w298.t w298.y w298.r w298.cap) (P33.root 5) :=
  Night6836Tree.sound w298 pick298 5 t566 _ (by decide +kernel)
theorem cov298_6 : PA.Covered 6 (OZ.Valid 6 w298.low w298.t w298.y w298.r w298.cap) (P33.root 6) :=
  Night6836Tree.sound w298 pick298 6 t567 _ (by decide +kernel)
theorem cov298_7 : PA.Covered 7 (OZ.Valid 7 w298.low w298.t w298.y w298.r w298.cap) (P33.root 7) :=
  Night6836Tree.sound w298 pick298 7 t2134 _ (by decide +kernel)
theorem window298 : P33.WindowCount w298 := by
  apply P33.window_count w298 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov298_1
  · exact cov298_2
  · exact cov298_3
  · exact cov298_4
  · exact cov298_5
  · exact cov298_6
  · exact cov298_7
def w299 : P33.Window := ⟨15,25,5791,5609,243554666577433312,13131,30000,5000000,81920000000⟩
def h299_0 : Height w299 := ⟨13131,30000,by decide +kernel⟩
def h299_1 : Height w299 := ⟨17377,27000,by decide +kernel⟩
def h299_2 : Height w299 := ⟨23159,24000,by decide +kernel⟩
def h299_3 : Height w299 := ⟨32262,21000,by decide +kernel⟩
def pick299 (cl : ℕ) : Height w299 := if cl<32 then (if cl<4 then (h299_0) else (h299_1)) else (if cl<302 then (h299_2) else (h299_3))
private theorem k299_1_0 : check w299 pick299 1 t7116 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k299_1_1 : check w299 pick299 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k299_1_2 : check w299 pick299 1 t7117 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w299 pick299 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7116 t7032 k299_1_0 k299_1_1
private theorem k299_1_3 : check w299 pick299 1 t7064 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k299_1_4 : check w299 pick299 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k299_1_5 : check w299 pick299 1 t7098 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w299 pick299 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7064 t7097 k299_1_3 k299_1_4
private theorem k299_1_6 : check w299 pick299 1 t7118 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w299 pick299 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7117 t7098 k299_1_2 k299_1_5
theorem cov299_1 : PA.Covered 1 (OZ.Valid 1 w299.low w299.t w299.y w299.r w299.cap) (P33.root 1) :=
  Night6836Tree.sound w299 pick299 1 t7118 _ k299_1_6
theorem cov299_2 : PA.Covered 2 (OZ.Valid 2 w299.low w299.t w299.y w299.r w299.cap) (P33.root 2) :=
  Night6836Tree.sound w299 pick299 2 t5320 _ (by decide +kernel)
theorem cov299_3 : PA.Covered 3 (OZ.Valid 3 w299.low w299.t w299.y w299.r w299.cap) (P33.root 3) :=
  Night6836Tree.sound w299 pick299 3 t564 _ (by decide +kernel)
theorem cov299_4 : PA.Covered 4 (OZ.Valid 4 w299.low w299.t w299.y w299.r w299.cap) (P33.root 4) :=
  Night6836Tree.sound w299 pick299 4 t565 _ (by decide +kernel)
theorem cov299_5 : PA.Covered 5 (OZ.Valid 5 w299.low w299.t w299.y w299.r w299.cap) (P33.root 5) :=
  Night6836Tree.sound w299 pick299 5 t566 _ (by decide +kernel)
theorem cov299_6 : PA.Covered 6 (OZ.Valid 6 w299.low w299.t w299.y w299.r w299.cap) (P33.root 6) :=
  Night6836Tree.sound w299 pick299 6 t567 _ (by decide +kernel)
theorem cov299_7 : PA.Covered 7 (OZ.Valid 7 w299.low w299.t w299.y w299.r w299.cap) (P33.root 7) :=
  Night6836Tree.sound w299 pick299 7 t2134 _ (by decide +kernel)
theorem window299 : P33.WindowCount w299 := by
  apply P33.window_count w299 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov299_1
  · exact cov299_2
  · exact cov299_3
  · exact cov299_4
  · exact cov299_5
  · exact cov299_6
  · exact cov299_7
end ProximityPrize.SubmissionLower.Night6836Bank
