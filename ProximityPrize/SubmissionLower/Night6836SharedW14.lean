/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT03
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w420 : P33.Window := ⟨7,41,5440,4441,198250073714549590,46037,27000,5000000,81920000000⟩
def h420_0 : Height w420 := ⟨46037,27000,by decide +kernel⟩
def h420_1 : Height w420 := ⟨52585,23000,by decide +kernel⟩
def h420_2 : Height w420 := ⟨62371,19000,by decide +kernel⟩
def pick420 (cl : ℕ) : Height w420 := if cl<13 then (h420_0) else (if cl<117 then (h420_1) else (h420_2))
private theorem k420_1_0 : check w420 pick420 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k420_1_1 : check w420 pick420 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k420_1_2 : check w420 pick420 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w420 pick420 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k420_1_0 k420_1_1
private theorem k420_1_3 : check w420 pick420 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k420_1_4 : check w420 pick420 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k420_1_5 : check w420 pick420 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w420 pick420 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k420_1_3 k420_1_4
private theorem k420_1_6 : check w420 pick420 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w420 pick420 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k420_1_2 k420_1_5
private theorem k420_1_7 : check w420 pick420 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k420_1_8 : check w420 pick420 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k420_1_9 : check w420 pick420 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w420 pick420 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k420_1_7 k420_1_8
private theorem k420_1_10 : check w420 pick420 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k420_1_11 : check w420 pick420 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k420_1_12 : check w420 pick420 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w420 pick420 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k420_1_10 k420_1_11
private theorem k420_1_13 : check w420 pick420 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w420 pick420 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k420_1_9 k420_1_12
private theorem k420_1_14 : check w420 pick420 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w420 pick420 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k420_1_6 k420_1_13
theorem cov420_1 : PA.Covered 1 (OZ.Valid 1 w420.low w420.t w420.y w420.r w420.cap) (P33.root 1) :=
  Night6836Tree.sound w420 pick420 1 t9554 _ k420_1_14
private theorem k420_2_0 : check w420 pick420 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k420_2_1 : check w420 pick420 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k420_2_2 : check w420 pick420 2 t9556 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w420 pick420 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9133 k420_2_0 k420_2_1
theorem cov420_2 : PA.Covered 2 (OZ.Valid 2 w420.low w420.t w420.y w420.r w420.cap) (P33.root 2) :=
  Night6836Tree.sound w420 pick420 2 t9556 _ k420_2_2
theorem cov420_3 : PA.Covered 3 (OZ.Valid 3 w420.low w420.t w420.y w420.r w420.cap) (P33.root 3) :=
  Night6836Tree.sound w420 pick420 3 t564 _ (by decide +kernel)
theorem cov420_4 : PA.Covered 4 (OZ.Valid 4 w420.low w420.t w420.y w420.r w420.cap) (P33.root 4) :=
  Night6836Tree.sound w420 pick420 4 t565 _ (by decide +kernel)
theorem cov420_5 : PA.Covered 5 (OZ.Valid 5 w420.low w420.t w420.y w420.r w420.cap) (P33.root 5) :=
  Night6836Tree.sound w420 pick420 5 t566 _ (by decide +kernel)
theorem cov420_6 : PA.Covered 6 (OZ.Valid 6 w420.low w420.t w420.y w420.r w420.cap) (P33.root 6) :=
  Night6836Tree.sound w420 pick420 6 t567 _ (by decide +kernel)
theorem cov420_7 : PA.Covered 7 (OZ.Valid 7 w420.low w420.t w420.y w420.r w420.cap) (P33.root 7) :=
  Night6836Tree.sound w420 pick420 7 t2134 _ (by decide +kernel)
theorem window420 : P33.WindowCount w420 := by
  apply P33.window_count w420 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov420_1
  · exact cov420_2
  · exact cov420_3
  · exact cov420_4
  · exact cov420_5
  · exact cov420_6
  · exact cov420_7
def w421 : P33.Window := ⟨7,41,7441,7395,245443102764100524,25378,18000,5000000,81920000000⟩
def h421_0 : Height w421 := ⟨25378,18000,by decide +kernel⟩
def h421_1 : Height w421 := ⟨29504,15000,by decide +kernel⟩
def h421_2 : Height w421 := ⟨35786,12000,by decide +kernel⟩
def h421_3 : Height w421 := ⟨48716,9000,by decide +kernel⟩
def pick421 (cl : ℕ) : Height w421 := if cl<47 then (if cl<3 then (h421_0) else (h421_1)) else (if cl<961 then (h421_2) else (h421_3))
private theorem k421_1_0 : check w421 pick421 1 t9283 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k421_1_1 : check w421 pick421 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k421_1_2 : check w421 pick421 1 t9284 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w421 pick421 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9283 t9190 k421_1_0 k421_1_1
private theorem k421_1_3 : check w421 pick421 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k421_1_4 : check w421 pick421 1 t9579 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k421_1_5 : check w421 pick421 1 t9580 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w421 pick421 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9579 k421_1_3 k421_1_4
private theorem k421_1_6 : check w421 pick421 1 t9583 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w421 pick421 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9284 t9580 k421_1_2 k421_1_5
private theorem k421_1_7 : check w421 pick421 1 t9594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k421_1_8 : check w421 pick421 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k421_1_9 : check w421 pick421 1 t9595 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w421 pick421 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t9594 t3123 k421_1_7 k421_1_8
private theorem k421_1_10 : check w421 pick421 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k421_1_11 : check w421 pick421 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k421_1_12 : check w421 pick421 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w421 pick421 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k421_1_10 k421_1_11
private theorem k421_1_13 : check w421 pick421 1 t9596 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w421 pick421 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t9595 t3709 k421_1_9 k421_1_12
private theorem k421_1_14 : check w421 pick421 1 t9597 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w421 pick421 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9583 t9596 k421_1_6 k421_1_13
theorem cov421_1 : PA.Covered 1 (OZ.Valid 1 w421.low w421.t w421.y w421.r w421.cap) (P33.root 1) :=
  Night6836Tree.sound w421 pick421 1 t9597 _ k421_1_14
private theorem k421_2_0 : check w421 pick421 2 t9598 ⟨2,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k421_2_1 : check w421 pick421 2 t9600 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k421_2_2 : check w421 pick421 2 t9601 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w421 pick421 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9598 t9600 k421_2_0 k421_2_1
theorem cov421_2 : PA.Covered 2 (OZ.Valid 2 w421.low w421.t w421.y w421.r w421.cap) (P33.root 2) :=
  Night6836Tree.sound w421 pick421 2 t9601 _ k421_2_2
theorem cov421_3 : PA.Covered 3 (OZ.Valid 3 w421.low w421.t w421.y w421.r w421.cap) (P33.root 3) :=
  Night6836Tree.sound w421 pick421 3 t564 _ (by decide +kernel)
theorem cov421_4 : PA.Covered 4 (OZ.Valid 4 w421.low w421.t w421.y w421.r w421.cap) (P33.root 4) :=
  Night6836Tree.sound w421 pick421 4 t565 _ (by decide +kernel)
theorem cov421_5 : PA.Covered 5 (OZ.Valid 5 w421.low w421.t w421.y w421.r w421.cap) (P33.root 5) :=
  Night6836Tree.sound w421 pick421 5 t566 _ (by decide +kernel)
theorem cov421_6 : PA.Covered 6 (OZ.Valid 6 w421.low w421.t w421.y w421.r w421.cap) (P33.root 6) :=
  Night6836Tree.sound w421 pick421 6 t567 _ (by decide +kernel)
theorem cov421_7 : PA.Covered 7 (OZ.Valid 7 w421.low w421.t w421.y w421.r w421.cap) (P33.root 7) :=
  Night6836Tree.sound w421 pick421 7 t568 _ (by decide +kernel)
theorem window421 : P33.WindowCount w421 := by
  apply P33.window_count w421 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov421_1
  · exact cov421_2
  · exact cov421_3
  · exact cov421_4
  · exact cov421_5
  · exact cov421_6
  · exact cov421_7
def w422 : P33.Window := ⟨7,42,4641,3642,201752347393392437,55247,35000,5000000,81920000000⟩
def h422_0 : Height w422 := ⟨55247,35000,by decide +kernel⟩
def h422_1 : Height w422 := ⟨60936,31000,by decide +kernel⟩
def h422_2 : Height w422 := ⟨68308,27000,by decide +kernel⟩
def h422_3 : Height w422 := ⟨78845,23000,by decide +kernel⟩
def pick422 (cl : ℕ) : Height w422 := if cl<32 then (if cl<4 then (h422_0) else (h422_1)) else (if cl<172 then (h422_2) else (h422_3))
private theorem k422_1_0 : check w422 pick422 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k422_1_1 : check w422 pick422 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k422_1_2 : check w422 pick422 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w422 pick422 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k422_1_0 k422_1_1
private theorem k422_1_3 : check w422 pick422 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k422_1_4 : check w422 pick422 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k422_1_5 : check w422 pick422 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w422 pick422 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k422_1_3 k422_1_4
private theorem k422_1_6 : check w422 pick422 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w422 pick422 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k422_1_2 k422_1_5
private theorem k422_1_7 : check w422 pick422 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k422_1_8 : check w422 pick422 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k422_1_9 : check w422 pick422 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w422 pick422 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k422_1_7 k422_1_8
private theorem k422_1_10 : check w422 pick422 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k422_1_11 : check w422 pick422 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k422_1_12 : check w422 pick422 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w422 pick422 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k422_1_10 k422_1_11
private theorem k422_1_13 : check w422 pick422 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w422 pick422 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k422_1_9 k422_1_12
private theorem k422_1_14 : check w422 pick422 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w422 pick422 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k422_1_6 k422_1_13
theorem cov422_1 : PA.Covered 1 (OZ.Valid 1 w422.low w422.t w422.y w422.r w422.cap) (P33.root 1) :=
  Night6836Tree.sound w422 pick422 1 t9554 _ k422_1_14
theorem cov422_2 : PA.Covered 2 (OZ.Valid 2 w422.low w422.t w422.y w422.r w422.cap) (P33.root 2) :=
  Night6836Tree.sound w422 pick422 2 t9593 _ (by decide +kernel)
theorem cov422_3 : PA.Covered 3 (OZ.Valid 3 w422.low w422.t w422.y w422.r w422.cap) (P33.root 3) :=
  Night6836Tree.sound w422 pick422 3 t564 _ (by decide +kernel)
theorem cov422_4 : PA.Covered 4 (OZ.Valid 4 w422.low w422.t w422.y w422.r w422.cap) (P33.root 4) :=
  Night6836Tree.sound w422 pick422 4 t565 _ (by decide +kernel)
theorem cov422_5 : PA.Covered 5 (OZ.Valid 5 w422.low w422.t w422.y w422.r w422.cap) (P33.root 5) :=
  Night6836Tree.sound w422 pick422 5 t566 _ (by decide +kernel)
theorem cov422_6 : PA.Covered 6 (OZ.Valid 6 w422.low w422.t w422.y w422.r w422.cap) (P33.root 6) :=
  Night6836Tree.sound w422 pick422 6 t567 _ (by decide +kernel)
theorem cov422_7 : PA.Covered 7 (OZ.Valid 7 w422.low w422.t w422.y w422.r w422.cap) (P33.root 7) :=
  Night6836Tree.sound w422 pick422 7 t2134 _ (by decide +kernel)
theorem window422 : P33.WindowCount w422 := by
  apply P33.window_count w422 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov422_1
  · exact cov422_2
  · exact cov422_3
  · exact cov422_4
  · exact cov422_5
  · exact cov422_6
  · exact cov422_7
def w423 : P33.Window := ⟨7,42,7394,7348,245427308044363676,26600,18000,5000000,81920000000⟩
def h423_0 : Height w423 := ⟨26600,18000,by decide +kernel⟩
def h423_1 : Height w423 := ⟨30844,15000,by decide +kernel⟩
def h423_2 : Height w423 := ⟨37350,12000,by decide +kernel⟩
def h423_3 : Height w423 := ⟨50860,9000,by decide +kernel⟩
def pick423 (cl : ℕ) : Height w423 := if cl<60 then (if cl<4 then (h423_0) else (h423_1)) else (if cl<961 then (h423_2) else (h423_3))
private theorem k423_1_0 : check w423 pick423 1 t5078 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k423_1_1 : check w423 pick423 1 t5105 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k423_1_2 : check w423 pick423 1 t5106 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w423 pick423 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5078 t5105 k423_1_0 k423_1_1
private theorem k423_1_3 : check w423 pick423 1 t5112 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k423_1_4 : check w423 pick423 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k423_1_5 : check w423 pick423 1 t9607 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w423 pick423 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t5112 t9606 k423_1_3 k423_1_4
private theorem k423_1_6 : check w423 pick423 1 t9608 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w423 pick423 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t5106 t9607 k423_1_2 k423_1_5
private theorem k423_1_7 : check w423 pick423 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k423_1_8 : check w423 pick423 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k423_1_9 : check w423 pick423 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w423 pick423 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k423_1_7 k423_1_8
private theorem k423_1_10 : check w423 pick423 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k423_1_11 : check w423 pick423 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k423_1_12 : check w423 pick423 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w423 pick423 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k423_1_10 k423_1_11
private theorem k423_1_13 : check w423 pick423 1 t3710 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w423 pick423 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t3709 k423_1_9 k423_1_12
private theorem k423_1_14 : check w423 pick423 1 t9609 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w423 pick423 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9608 t3710 k423_1_6 k423_1_13
theorem cov423_1 : PA.Covered 1 (OZ.Valid 1 w423.low w423.t w423.y w423.r w423.cap) (P33.root 1) :=
  Night6836Tree.sound w423 pick423 1 t9609 _ k423_1_14
private theorem k423_2_0 : check w423 pick423 2 t3447 ⟨2,7,4,16,2,52,2,56⟩ = true := by decide +kernel
private theorem k423_2_1 : check w423 pick423 2 t9610 ⟨2,7,4,16,2,52,57,111⟩ = true := by decide +kernel
private theorem k423_2_2 : check w423 pick423 2 t9611 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w423 pick423 2 ⟨2,7,4,16,2,52,2,111⟩ 3 56 t3447 t9610 k423_2_0 k423_2_1
private theorem k423_2_3 : check w423 pick423 2 t9254 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k423_2_4 : check w423 pick423 2 t9613 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k423_2_5 : check w423 pick423 2 t9614 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w423 pick423 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t9254 t9613 k423_2_3 k423_2_4
private theorem k423_2_6 : check w423 pick423 2 t9615 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w423 pick423 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t9611 t9614 k423_2_2 k423_2_5
theorem cov423_2 : PA.Covered 2 (OZ.Valid 2 w423.low w423.t w423.y w423.r w423.cap) (P33.root 2) :=
  Night6836Tree.sound w423 pick423 2 t9615 _ k423_2_6
theorem cov423_3 : PA.Covered 3 (OZ.Valid 3 w423.low w423.t w423.y w423.r w423.cap) (P33.root 3) :=
  Night6836Tree.sound w423 pick423 3 t564 _ (by decide +kernel)
theorem cov423_4 : PA.Covered 4 (OZ.Valid 4 w423.low w423.t w423.y w423.r w423.cap) (P33.root 4) :=
  Night6836Tree.sound w423 pick423 4 t565 _ (by decide +kernel)
theorem cov423_5 : PA.Covered 5 (OZ.Valid 5 w423.low w423.t w423.y w423.r w423.cap) (P33.root 5) :=
  Night6836Tree.sound w423 pick423 5 t566 _ (by decide +kernel)
theorem cov423_6 : PA.Covered 6 (OZ.Valid 6 w423.low w423.t w423.y w423.r w423.cap) (P33.root 6) :=
  Night6836Tree.sound w423 pick423 6 t567 _ (by decide +kernel)
theorem cov423_7 : PA.Covered 7 (OZ.Valid 7 w423.low w423.t w423.y w423.r w423.cap) (P33.root 7) :=
  Night6836Tree.sound w423 pick423 7 t568 _ (by decide +kernel)
theorem window423 : P33.WindowCount w423 := by
  apply P33.window_count w423 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov423_1
  · exact cov423_2
  · exact cov423_3
  · exact cov423_4
  · exact cov423_5
  · exact cov423_6
  · exact cov423_7
def w424 : P33.Window := ⟨7,43,4642,3643,187538499866854088,57103,35000,5000000,81920000000⟩
def h424_0 : Height w424 := ⟨57103,35000,by decide +kernel⟩
def h424_1 : Height w424 := ⟨62884,31000,by decide +kernel⟩
def h424_2 : Height w424 := ⟨70388,27000,by decide +kernel⟩
def h424_3 : Height w424 := ⟨81133,23000,by decide +kernel⟩
def pick424 (cl : ℕ) : Height w424 := if cl<32 then (if cl<5 then (h424_0) else (h424_1)) else (if cl<195 then (h424_2) else (h424_3))
private theorem k424_1_0 : check w424 pick424 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k424_1_1 : check w424 pick424 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k424_1_2 : check w424 pick424 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w424 pick424 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k424_1_0 k424_1_1
private theorem k424_1_3 : check w424 pick424 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k424_1_4 : check w424 pick424 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k424_1_5 : check w424 pick424 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w424 pick424 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k424_1_3 k424_1_4
private theorem k424_1_6 : check w424 pick424 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w424 pick424 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k424_1_2 k424_1_5
private theorem k424_1_7 : check w424 pick424 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k424_1_8 : check w424 pick424 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k424_1_9 : check w424 pick424 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w424 pick424 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k424_1_7 k424_1_8
private theorem k424_1_10 : check w424 pick424 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k424_1_11 : check w424 pick424 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k424_1_12 : check w424 pick424 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w424 pick424 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k424_1_10 k424_1_11
private theorem k424_1_13 : check w424 pick424 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w424 pick424 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k424_1_9 k424_1_12
private theorem k424_1_14 : check w424 pick424 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w424 pick424 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k424_1_6 k424_1_13
theorem cov424_1 : PA.Covered 1 (OZ.Valid 1 w424.low w424.t w424.y w424.r w424.cap) (P33.root 1) :=
  Night6836Tree.sound w424 pick424 1 t9554 _ k424_1_14
theorem cov424_2 : PA.Covered 2 (OZ.Valid 2 w424.low w424.t w424.y w424.r w424.cap) (P33.root 2) :=
  Night6836Tree.sound w424 pick424 2 t4654 _ (by decide +kernel)
theorem cov424_3 : PA.Covered 3 (OZ.Valid 3 w424.low w424.t w424.y w424.r w424.cap) (P33.root 3) :=
  Night6836Tree.sound w424 pick424 3 t564 _ (by decide +kernel)
theorem cov424_4 : PA.Covered 4 (OZ.Valid 4 w424.low w424.t w424.y w424.r w424.cap) (P33.root 4) :=
  Night6836Tree.sound w424 pick424 4 t565 _ (by decide +kernel)
theorem cov424_5 : PA.Covered 5 (OZ.Valid 5 w424.low w424.t w424.y w424.r w424.cap) (P33.root 5) :=
  Night6836Tree.sound w424 pick424 5 t566 _ (by decide +kernel)
theorem cov424_6 : PA.Covered 6 (OZ.Valid 6 w424.low w424.t w424.y w424.r w424.cap) (P33.root 6) :=
  Night6836Tree.sound w424 pick424 6 t567 _ (by decide +kernel)
theorem cov424_7 : PA.Covered 7 (OZ.Valid 7 w424.low w424.t w424.y w424.r w424.cap) (P33.root 7) :=
  Night6836Tree.sound w424 pick424 7 t2134 _ (by decide +kernel)
theorem window424 : P33.WindowCount w424 := by
  apply P33.window_count w424 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov424_1
  · exact cov424_2
  · exact cov424_3
  · exact cov424_4
  · exact cov424_5
  · exact cov424_6
  · exact cov424_7
def w425 : P33.Window := ⟨7,43,7347,7194,244176409007995131,28593,18000,5000000,81920000000⟩
def h425_0 : Height w425 := ⟨28593,18000,by decide +kernel⟩
def h425_1 : Height w425 := ⟨33081,15000,by decide +kernel⟩
def h425_2 : Height w425 := ⟨40065,12000,by decide +kernel⟩
def h425_3 : Height w425 := ⟨54902,9000,by decide +kernel⟩
def pick425 (cl : ℕ) : Height w425 := if cl<90 then (if cl<5 then (h425_0) else (h425_1)) else (if cl<1002 then (h425_2) else (h425_3))
private theorem k425_1_0 : check w425 pick425 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k425_1_1 : check w425 pick425 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k425_1_2 : check w425 pick425 1 t9618 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w425 pick425 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t9617 k425_1_0 k425_1_1
private theorem k425_1_3 : check w425 pick425 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k425_1_4 : check w425 pick425 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k425_1_5 : check w425 pick425 1 t9619 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w425 pick425 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t9606 k425_1_3 k425_1_4
private theorem k425_1_6 : check w425 pick425 1 t9620 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w425 pick425 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9618 t9619 k425_1_2 k425_1_5
private theorem k425_1_7 : check w425 pick425 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k425_1_8 : check w425 pick425 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k425_1_9 : check w425 pick425 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w425 pick425 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k425_1_7 k425_1_8
private theorem k425_1_10 : check w425 pick425 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k425_1_11 : check w425 pick425 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k425_1_12 : check w425 pick425 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w425 pick425 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k425_1_10 k425_1_11
private theorem k425_1_13 : check w425 pick425 1 t3710 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w425 pick425 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t3709 k425_1_9 k425_1_12
private theorem k425_1_14 : check w425 pick425 1 t9621 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w425 pick425 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9620 t3710 k425_1_6 k425_1_13
theorem cov425_1 : PA.Covered 1 (OZ.Valid 1 w425.low w425.t w425.y w425.r w425.cap) (P33.root 1) :=
  Night6836Tree.sound w425 pick425 1 t9621 _ k425_1_14
private theorem k425_2_0 : check w425 pick425 2 t9626 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k425_2_1 : check w425 pick425 2 t9628 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k425_2_2 : check w425 pick425 2 t9629 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w425 pick425 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t9626 t9628 k425_2_0 k425_2_1
private theorem k425_2_3 : check w425 pick425 2 t9632 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k425_2_4 : check w425 pick425 2 t9633 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k425_2_5 : check w425 pick425 2 t9634 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w425 pick425 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t9632 t9633 k425_2_3 k425_2_4
private theorem k425_2_6 : check w425 pick425 2 t9635 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w425 pick425 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t9629 t9634 k425_2_2 k425_2_5
theorem cov425_2 : PA.Covered 2 (OZ.Valid 2 w425.low w425.t w425.y w425.r w425.cap) (P33.root 2) :=
  Night6836Tree.sound w425 pick425 2 t9635 _ k425_2_6
theorem cov425_3 : PA.Covered 3 (OZ.Valid 3 w425.low w425.t w425.y w425.r w425.cap) (P33.root 3) :=
  Night6836Tree.sound w425 pick425 3 t564 _ (by decide +kernel)
theorem cov425_4 : PA.Covered 4 (OZ.Valid 4 w425.low w425.t w425.y w425.r w425.cap) (P33.root 4) :=
  Night6836Tree.sound w425 pick425 4 t565 _ (by decide +kernel)
theorem cov425_5 : PA.Covered 5 (OZ.Valid 5 w425.low w425.t w425.y w425.r w425.cap) (P33.root 5) :=
  Night6836Tree.sound w425 pick425 5 t566 _ (by decide +kernel)
theorem cov425_6 : PA.Covered 6 (OZ.Valid 6 w425.low w425.t w425.y w425.r w425.cap) (P33.root 6) :=
  Night6836Tree.sound w425 pick425 6 t567 _ (by decide +kernel)
theorem cov425_7 : PA.Covered 7 (OZ.Valid 7 w425.low w425.t w425.y w425.r w425.cap) (P33.root 7) :=
  Night6836Tree.sound w425 pick425 7 t568 _ (by decide +kernel)
theorem window425 : P33.WindowCount w425 := by
  apply P33.window_count w425 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov425_1
  · exact cov425_2
  · exact cov425_3
  · exact cov425_4
  · exact cov425_5
  · exact cov425_6
  · exact cov425_7
def w426 : P33.Window := ⟨7,44,4643,3644,190465972105690802,58958,35000,5000000,81920000000⟩
def h426_0 : Height w426 := ⟨58958,35000,by decide +kernel⟩
def h426_1 : Height w426 := ⟨64830,31000,by decide +kernel⟩
def h426_2 : Height w426 := ⟨72465,27000,by decide +kernel⟩
def h426_3 : Height w426 := ⟨83419,23000,by decide +kernel⟩
def pick426 (cl : ℕ) : Height w426 := if cl<32 then (if cl<5 then (h426_0) else (h426_1)) else (if cl<213 then (h426_2) else (h426_3))
private theorem k426_1_0 : check w426 pick426 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k426_1_1 : check w426 pick426 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k426_1_2 : check w426 pick426 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w426 pick426 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k426_1_0 k426_1_1
private theorem k426_1_3 : check w426 pick426 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k426_1_4 : check w426 pick426 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k426_1_5 : check w426 pick426 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w426 pick426 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k426_1_3 k426_1_4
private theorem k426_1_6 : check w426 pick426 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w426 pick426 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k426_1_2 k426_1_5
private theorem k426_1_7 : check w426 pick426 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k426_1_8 : check w426 pick426 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k426_1_9 : check w426 pick426 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w426 pick426 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k426_1_7 k426_1_8
private theorem k426_1_10 : check w426 pick426 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k426_1_11 : check w426 pick426 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k426_1_12 : check w426 pick426 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w426 pick426 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k426_1_10 k426_1_11
private theorem k426_1_13 : check w426 pick426 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w426 pick426 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k426_1_9 k426_1_12
private theorem k426_1_14 : check w426 pick426 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w426 pick426 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k426_1_6 k426_1_13
theorem cov426_1 : PA.Covered 1 (OZ.Valid 1 w426.low w426.t w426.y w426.r w426.cap) (P33.root 1) :=
  Night6836Tree.sound w426 pick426 1 t9554 _ k426_1_14
theorem cov426_2 : PA.Covered 2 (OZ.Valid 2 w426.low w426.t w426.y w426.r w426.cap) (P33.root 2) :=
  Night6836Tree.sound w426 pick426 2 t4654 _ (by decide +kernel)
theorem cov426_3 : PA.Covered 3 (OZ.Valid 3 w426.low w426.t w426.y w426.r w426.cap) (P33.root 3) :=
  Night6836Tree.sound w426 pick426 3 t564 _ (by decide +kernel)
theorem cov426_4 : PA.Covered 4 (OZ.Valid 4 w426.low w426.t w426.y w426.r w426.cap) (P33.root 4) :=
  Night6836Tree.sound w426 pick426 4 t565 _ (by decide +kernel)
theorem cov426_5 : PA.Covered 5 (OZ.Valid 5 w426.low w426.t w426.y w426.r w426.cap) (P33.root 5) :=
  Night6836Tree.sound w426 pick426 5 t566 _ (by decide +kernel)
theorem cov426_6 : PA.Covered 6 (OZ.Valid 6 w426.low w426.t w426.y w426.r w426.cap) (P33.root 6) :=
  Night6836Tree.sound w426 pick426 6 t567 _ (by decide +kernel)
theorem cov426_7 : PA.Covered 7 (OZ.Valid 7 w426.low w426.t w426.y w426.r w426.cap) (P33.root 7) :=
  Night6836Tree.sound w426 pick426 7 t2134 _ (by decide +kernel)
theorem window426 : P33.WindowCount w426 := by
  apply P33.window_count w426 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov426_1
  · exact cov426_2
  · exact cov426_3
  · exact cov426_4
  · exact cov426_5
  · exact cov426_6
  · exact cov426_7
def w427 : P33.Window := ⟨7,44,5143,4144,201453100980563520,51566,31000,5000000,81920000000⟩
def h427_0 : Height w427 := ⟨51566,31000,by decide +kernel⟩
def h427_1 : Height w427 := ⟨57460,27000,by decide +kernel⟩
def h427_2 : Height w427 := ⟨65475,23000,by decide +kernel⟩
def h427_3 : Height w427 := ⟨77985,19000,by decide +kernel⟩
def pick427 (cl : ℕ) : Height w427 := if cl<40 then (if cl<5 then (h427_0) else (h427_1)) else (if cl<302 then (h427_2) else (h427_3))
private theorem k427_1_0 : check w427 pick427 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k427_1_1 : check w427 pick427 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k427_1_2 : check w427 pick427 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w427 pick427 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k427_1_0 k427_1_1
private theorem k427_1_3 : check w427 pick427 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k427_1_4 : check w427 pick427 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k427_1_5 : check w427 pick427 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w427 pick427 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k427_1_3 k427_1_4
private theorem k427_1_6 : check w427 pick427 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w427 pick427 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k427_1_2 k427_1_5
private theorem k427_1_7 : check w427 pick427 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k427_1_8 : check w427 pick427 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k427_1_9 : check w427 pick427 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w427 pick427 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k427_1_7 k427_1_8
private theorem k427_1_10 : check w427 pick427 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k427_1_11 : check w427 pick427 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k427_1_12 : check w427 pick427 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w427 pick427 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k427_1_10 k427_1_11
private theorem k427_1_13 : check w427 pick427 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w427 pick427 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k427_1_9 k427_1_12
private theorem k427_1_14 : check w427 pick427 1 t9636 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w427 pick427 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t9097 k427_1_6 k427_1_13
theorem cov427_1 : PA.Covered 1 (OZ.Valid 1 w427.low w427.t w427.y w427.r w427.cap) (P33.root 1) :=
  Night6836Tree.sound w427 pick427 1 t9636 _ k427_1_14
private theorem k427_2_0 : check w427 pick427 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k427_2_1 : check w427 pick427 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k427_2_2 : check w427 pick427 2 t9556 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w427 pick427 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9133 k427_2_0 k427_2_1
theorem cov427_2 : PA.Covered 2 (OZ.Valid 2 w427.low w427.t w427.y w427.r w427.cap) (P33.root 2) :=
  Night6836Tree.sound w427 pick427 2 t9556 _ k427_2_2
theorem cov427_3 : PA.Covered 3 (OZ.Valid 3 w427.low w427.t w427.y w427.r w427.cap) (P33.root 3) :=
  Night6836Tree.sound w427 pick427 3 t564 _ (by decide +kernel)
theorem cov427_4 : PA.Covered 4 (OZ.Valid 4 w427.low w427.t w427.y w427.r w427.cap) (P33.root 4) :=
  Night6836Tree.sound w427 pick427 4 t565 _ (by decide +kernel)
theorem cov427_5 : PA.Covered 5 (OZ.Valid 5 w427.low w427.t w427.y w427.r w427.cap) (P33.root 5) :=
  Night6836Tree.sound w427 pick427 5 t566 _ (by decide +kernel)
theorem cov427_6 : PA.Covered 6 (OZ.Valid 6 w427.low w427.t w427.y w427.r w427.cap) (P33.root 6) :=
  Night6836Tree.sound w427 pick427 6 t567 _ (by decide +kernel)
theorem cov427_7 : PA.Covered 7 (OZ.Valid 7 w427.low w427.t w427.y w427.r w427.cap) (P33.root 7) :=
  Night6836Tree.sound w427 pick427 7 t2134 _ (by decide +kernel)
theorem window427 : P33.WindowCount w427 := by
  apply P33.window_count w427 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov427_1
  · exact cov427_2
  · exact cov427_3
  · exact cov427_4
  · exact cov427_5
  · exact cov427_6
  · exact cov427_7
def w428 : P33.Window := ⟨7,44,7299,7251,245362154789348760,29130,18000,5000000,81920000000⟩
def h428_0 : Height w428 := ⟨29130,18000,by decide +kernel⟩
def h428_1 : Height w428 := ⟨33625,15000,by decide +kernel⟩
def h428_2 : Height w428 := ⟨40610,12000,by decide +kernel⟩
def h428_3 : Height w428 := ⟨55376,9000,by decide +kernel⟩
def pick428 (cl : ℕ) : Height w428 := if cl<90 then (if cl<5 then (h428_0) else (h428_1)) else (if cl<1002 then (h428_2) else (h428_3))
private theorem k428_1_0 : check w428 pick428 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k428_1_1 : check w428 pick428 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k428_1_2 : check w428 pick428 1 t9618 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w428 pick428 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t9617 k428_1_0 k428_1_1
private theorem k428_1_3 : check w428 pick428 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k428_1_4 : check w428 pick428 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k428_1_5 : check w428 pick428 1 t9619 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w428 pick428 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t9606 k428_1_3 k428_1_4
private theorem k428_1_6 : check w428 pick428 1 t9620 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w428 pick428 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9618 t9619 k428_1_2 k428_1_5
private theorem k428_1_7 : check w428 pick428 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k428_1_8 : check w428 pick428 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k428_1_9 : check w428 pick428 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w428 pick428 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k428_1_7 k428_1_8
private theorem k428_1_10 : check w428 pick428 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k428_1_11 : check w428 pick428 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k428_1_12 : check w428 pick428 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w428 pick428 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k428_1_10 k428_1_11
private theorem k428_1_13 : check w428 pick428 1 t3710 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w428 pick428 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t3709 k428_1_9 k428_1_12
private theorem k428_1_14 : check w428 pick428 1 t9621 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w428 pick428 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9620 t3710 k428_1_6 k428_1_13
theorem cov428_1 : PA.Covered 1 (OZ.Valid 1 w428.low w428.t w428.y w428.r w428.cap) (P33.root 1) :=
  Night6836Tree.sound w428 pick428 1 t9621 _ k428_1_14
private theorem k428_2_0 : check w428 pick428 2 t9626 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k428_2_1 : check w428 pick428 2 t9628 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k428_2_2 : check w428 pick428 2 t9629 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w428 pick428 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t9626 t9628 k428_2_0 k428_2_1
private theorem k428_2_3 : check w428 pick428 2 t9637 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k428_2_4 : check w428 pick428 2 t9638 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k428_2_5 : check w428 pick428 2 t9639 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w428 pick428 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t9637 t9638 k428_2_3 k428_2_4
private theorem k428_2_6 : check w428 pick428 2 t9640 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w428 pick428 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t9629 t9639 k428_2_2 k428_2_5
theorem cov428_2 : PA.Covered 2 (OZ.Valid 2 w428.low w428.t w428.y w428.r w428.cap) (P33.root 2) :=
  Night6836Tree.sound w428 pick428 2 t9640 _ k428_2_6
theorem cov428_3 : PA.Covered 3 (OZ.Valid 3 w428.low w428.t w428.y w428.r w428.cap) (P33.root 3) :=
  Night6836Tree.sound w428 pick428 3 t564 _ (by decide +kernel)
theorem cov428_4 : PA.Covered 4 (OZ.Valid 4 w428.low w428.t w428.y w428.r w428.cap) (P33.root 4) :=
  Night6836Tree.sound w428 pick428 4 t565 _ (by decide +kernel)
theorem cov428_5 : PA.Covered 5 (OZ.Valid 5 w428.low w428.t w428.y w428.r w428.cap) (P33.root 5) :=
  Night6836Tree.sound w428 pick428 5 t566 _ (by decide +kernel)
theorem cov428_6 : PA.Covered 6 (OZ.Valid 6 w428.low w428.t w428.y w428.r w428.cap) (P33.root 6) :=
  Night6836Tree.sound w428 pick428 6 t567 _ (by decide +kernel)
theorem cov428_7 : PA.Covered 7 (OZ.Valid 7 w428.low w428.t w428.y w428.r w428.cap) (P33.root 7) :=
  Night6836Tree.sound w428 pick428 7 t568 _ (by decide +kernel)
theorem window428 : P33.WindowCount w428 := by
  apply P33.window_count w428 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov428_1
  · exact cov428_2
  · exact cov428_3
  · exact cov428_4
  · exact cov428_5
  · exact cov428_6
  · exact cov428_7
def w429 : P33.Window := ⟨7,45,4644,3645,193393627629821475,60811,35000,5000000,81920000000⟩
def h429_0 : Height w429 := ⟨60811,35000,by decide +kernel⟩
def h429_1 : Height w429 := ⟨66774,31000,by decide +kernel⟩
def h429_2 : Height w429 := ⟨74541,27000,by decide +kernel⟩
def h429_3 : Height w429 := ⟨85701,23000,by decide +kernel⟩
def pick429 (cl : ℕ) : Height w429 := if cl<32 then (if cl<5 then (h429_0) else (h429_1)) else (if cl<223 then (h429_2) else (h429_3))
private theorem k429_1_0 : check w429 pick429 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k429_1_1 : check w429 pick429 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k429_1_2 : check w429 pick429 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w429 pick429 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k429_1_0 k429_1_1
private theorem k429_1_3 : check w429 pick429 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k429_1_4 : check w429 pick429 1 t9551 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k429_1_5 : check w429 pick429 1 t9552 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w429 pick429 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t9551 k429_1_3 k429_1_4
private theorem k429_1_6 : check w429 pick429 1 t9553 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w429 pick429 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9552 k429_1_2 k429_1_5
private theorem k429_1_7 : check w429 pick429 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k429_1_8 : check w429 pick429 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k429_1_9 : check w429 pick429 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w429 pick429 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k429_1_7 k429_1_8
private theorem k429_1_10 : check w429 pick429 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k429_1_11 : check w429 pick429 1 t3547 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k429_1_12 : check w429 pick429 1 t3548 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w429 pick429 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t3547 k429_1_10 k429_1_11
private theorem k429_1_13 : check w429 pick429 1 t3549 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w429 pick429 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t3548 k429_1_9 k429_1_12
private theorem k429_1_14 : check w429 pick429 1 t9554 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w429 pick429 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9553 t3549 k429_1_6 k429_1_13
theorem cov429_1 : PA.Covered 1 (OZ.Valid 1 w429.low w429.t w429.y w429.r w429.cap) (P33.root 1) :=
  Night6836Tree.sound w429 pick429 1 t9554 _ k429_1_14
theorem cov429_2 : PA.Covered 2 (OZ.Valid 2 w429.low w429.t w429.y w429.r w429.cap) (P33.root 2) :=
  Night6836Tree.sound w429 pick429 2 t4654 _ (by decide +kernel)
theorem cov429_3 : PA.Covered 3 (OZ.Valid 3 w429.low w429.t w429.y w429.r w429.cap) (P33.root 3) :=
  Night6836Tree.sound w429 pick429 3 t564 _ (by decide +kernel)
theorem cov429_4 : PA.Covered 4 (OZ.Valid 4 w429.low w429.t w429.y w429.r w429.cap) (P33.root 4) :=
  Night6836Tree.sound w429 pick429 4 t565 _ (by decide +kernel)
theorem cov429_5 : PA.Covered 5 (OZ.Valid 5 w429.low w429.t w429.y w429.r w429.cap) (P33.root 5) :=
  Night6836Tree.sound w429 pick429 5 t566 _ (by decide +kernel)
theorem cov429_6 : PA.Covered 6 (OZ.Valid 6 w429.low w429.t w429.y w429.r w429.cap) (P33.root 6) :=
  Night6836Tree.sound w429 pick429 6 t567 _ (by decide +kernel)
theorem cov429_7 : PA.Covered 7 (OZ.Valid 7 w429.low w429.t w429.y w429.r w429.cap) (P33.root 7) :=
  Night6836Tree.sound w429 pick429 7 t2134 _ (by decide +kernel)
theorem window429 : P33.WindowCount w429 := by
  apply P33.window_count w429 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov429_1
  · exact cov429_2
  · exact cov429_3
  · exact cov429_4
  · exact cov429_5
  · exact cov429_6
  · exact cov429_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w430 : P33.Window := ⟨7,45,5744,4745,203747780668635665,46587,27000,5000000,81920000000⟩
def h430_0 : Height w430 := ⟨46587,27000,by decide +kernel⟩
def h430_1 : Height w430 := ⟨52745,23000,by decide +kernel⟩
def h430_2 : Height w430 := ⟨61739,19000,by decide +kernel⟩
def h430_3 : Height w430 := ⟨77953,15000,by decide +kernel⟩
def pick430 (cl : ℕ) : Height w430 := if cl<75 then (if cl<6 then (h430_0) else (h430_1)) else (if cl<922 then (h430_2) else (h430_3))
private theorem k430_1_0 : check w430 pick430 1 t9283 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k430_1_1 : check w430 pick430 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k430_1_2 : check w430 pick430 1 t9284 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w430 pick430 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9283 t9190 k430_1_0 k430_1_1
private theorem k430_1_3 : check w430 pick430 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k430_1_4 : check w430 pick430 1 t9579 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k430_1_5 : check w430 pick430 1 t9580 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w430 pick430 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9579 k430_1_3 k430_1_4
private theorem k430_1_6 : check w430 pick430 1 t9583 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w430 pick430 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9284 t9580 k430_1_2 k430_1_5
private theorem k430_1_7 : check w430 pick430 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k430_1_8 : check w430 pick430 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k430_1_9 : check w430 pick430 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w430 pick430 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k430_1_7 k430_1_8
private theorem k430_1_10 : check w430 pick430 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k430_1_11 : check w430 pick430 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k430_1_12 : check w430 pick430 1 t9575 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w430 pick430 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t3708 k430_1_10 k430_1_11
private theorem k430_1_13 : check w430 pick430 1 t9576 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w430 pick430 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9575 k430_1_9 k430_1_12
private theorem k430_1_14 : check w430 pick430 1 t9584 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w430 pick430 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9583 t9576 k430_1_6 k430_1_13
theorem cov430_1 : PA.Covered 1 (OZ.Valid 1 w430.low w430.t w430.y w430.r w430.cap) (P33.root 1) :=
  Night6836Tree.sound w430 pick430 1 t9584 _ k430_1_14
private theorem k430_2_0 : check w430 pick430 2 t9641 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k430_2_1 : check w430 pick430 2 t9644 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k430_2_2 : check w430 pick430 2 t9645 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w430 pick430 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9641 t9644 k430_2_0 k430_2_1
private theorem k430_2_3 : check w430 pick430 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k430_2_4 : check w430 pick430 2 t4902 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k430_2_5 : check w430 pick430 2 t4903 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w430 pick430 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4902 k430_2_3 k430_2_4
private theorem k430_2_6 : check w430 pick430 2 t9646 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w430 pick430 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9645 t4903 k430_2_2 k430_2_5
theorem cov430_2 : PA.Covered 2 (OZ.Valid 2 w430.low w430.t w430.y w430.r w430.cap) (P33.root 2) :=
  Night6836Tree.sound w430 pick430 2 t9646 _ k430_2_6
theorem cov430_3 : PA.Covered 3 (OZ.Valid 3 w430.low w430.t w430.y w430.r w430.cap) (P33.root 3) :=
  Night6836Tree.sound w430 pick430 3 t564 _ (by decide +kernel)
theorem cov430_4 : PA.Covered 4 (OZ.Valid 4 w430.low w430.t w430.y w430.r w430.cap) (P33.root 4) :=
  Night6836Tree.sound w430 pick430 4 t565 _ (by decide +kernel)
theorem cov430_5 : PA.Covered 5 (OZ.Valid 5 w430.low w430.t w430.y w430.r w430.cap) (P33.root 5) :=
  Night6836Tree.sound w430 pick430 5 t566 _ (by decide +kernel)
theorem cov430_6 : PA.Covered 6 (OZ.Valid 6 w430.low w430.t w430.y w430.r w430.cap) (P33.root 6) :=
  Night6836Tree.sound w430 pick430 6 t567 _ (by decide +kernel)
theorem cov430_7 : PA.Covered 7 (OZ.Valid 7 w430.low w430.t w430.y w430.r w430.cap) (P33.root 7) :=
  Night6836Tree.sound w430 pick430 7 t2134 _ (by decide +kernel)
theorem window430 : P33.WindowCount w430 := by
  apply P33.window_count w430 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov430_1
  · exact cov430_2
  · exact cov430_3
  · exact cov430_4
  · exact cov430_5
  · exact cov430_6
  · exact cov430_7
def w431 : P33.Window := ⟨7,45,7250,7201,245783815156953164,30441,18000,5000000,81920000000⟩
def h431_0 : Height w431 := ⟨30441,18000,by decide +kernel⟩
def h431_1 : Height w431 := ⟨35070,15000,by decide +kernel⟩
def h431_2 : Height w431 := ⟨42311,12000,by decide +kernel⟩
def h431_3 : Height w431 := ⟨57758,9000,by decide +kernel⟩
def pick431 (cl : ℕ) : Height w431 := if cl<107 then (if cl<6 then (h431_0) else (h431_1)) else (if cl<1013 then (h431_2) else (h431_3))
private theorem k431_1_0 : check w431 pick431 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k431_1_1 : check w431 pick431 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k431_1_2 : check w431 pick431 1 t9618 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w431 pick431 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t9617 k431_1_0 k431_1_1
private theorem k431_1_3 : check w431 pick431 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k431_1_4 : check w431 pick431 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k431_1_5 : check w431 pick431 1 t9619 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w431 pick431 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t9606 k431_1_3 k431_1_4
private theorem k431_1_6 : check w431 pick431 1 t9620 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w431 pick431 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9618 t9619 k431_1_2 k431_1_5
private theorem k431_1_7 : check w431 pick431 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k431_1_8 : check w431 pick431 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k431_1_9 : check w431 pick431 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w431 pick431 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k431_1_7 k431_1_8
private theorem k431_1_10 : check w431 pick431 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k431_1_11 : check w431 pick431 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k431_1_12 : check w431 pick431 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w431 pick431 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k431_1_10 k431_1_11
private theorem k431_1_13 : check w431 pick431 1 t3710 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w431 pick431 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t3709 k431_1_9 k431_1_12
private theorem k431_1_14 : check w431 pick431 1 t9621 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w431 pick431 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9620 t3710 k431_1_6 k431_1_13
theorem cov431_1 : PA.Covered 1 (OZ.Valid 1 w431.low w431.t w431.y w431.r w431.cap) (P33.root 1) :=
  Night6836Tree.sound w431 pick431 1 t9621 _ k431_1_14
private theorem k431_2_0 : check w431 pick431 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k431_2_1 : check w431 pick431 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k431_2_2 : check w431 pick431 2 t3491 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w431 pick431 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3490 k431_2_0 k431_2_1
private theorem k431_2_3 : check w431 pick431 2 t9650 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k431_2_4 : check w431 pick431 2 t9651 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w431 pick431 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3491 t9650 k431_2_2 k431_2_3
theorem cov431_2 : PA.Covered 2 (OZ.Valid 2 w431.low w431.t w431.y w431.r w431.cap) (P33.root 2) :=
  Night6836Tree.sound w431 pick431 2 t9651 _ k431_2_4
theorem cov431_3 : PA.Covered 3 (OZ.Valid 3 w431.low w431.t w431.y w431.r w431.cap) (P33.root 3) :=
  Night6836Tree.sound w431 pick431 3 t564 _ (by decide +kernel)
theorem cov431_4 : PA.Covered 4 (OZ.Valid 4 w431.low w431.t w431.y w431.r w431.cap) (P33.root 4) :=
  Night6836Tree.sound w431 pick431 4 t565 _ (by decide +kernel)
theorem cov431_5 : PA.Covered 5 (OZ.Valid 5 w431.low w431.t w431.y w431.r w431.cap) (P33.root 5) :=
  Night6836Tree.sound w431 pick431 5 t566 _ (by decide +kernel)
theorem cov431_6 : PA.Covered 6 (OZ.Valid 6 w431.low w431.t w431.y w431.r w431.cap) (P33.root 6) :=
  Night6836Tree.sound w431 pick431 6 t567 _ (by decide +kernel)
theorem cov431_7 : PA.Covered 7 (OZ.Valid 7 w431.low w431.t w431.y w431.r w431.cap) (P33.root 7) :=
  Night6836Tree.sound w431 pick431 7 t568 _ (by decide +kernel)
theorem window431 : P33.WindowCount w431 := by
  apply P33.window_count w431 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov431_1
  · exact cov431_2
  · exact cov431_3
  · exact cov431_4
  · exact cov431_5
  · exact cov431_6
  · exact cov431_7
def w432 : P33.Window := ⟨7,46,5145,4146,203673611831446943,54823,31000,5000000,81920000000⟩
def h432_0 : Height w432 := ⟨54823,31000,by decide +kernel⟩
def h432_1 : Height w432 := ⟨60901,27000,by decide +kernel⟩
def h432_2 : Height w432 := ⟨69198,23000,by decide +kernel⟩
def h432_3 : Height w432 := ⟨82196,19000,by decide +kernel⟩
def pick432 (cl : ℕ) : Height w432 := if cl<44 then (if cl<6 then (h432_0) else (h432_1)) else (if cl<386 then (h432_2) else (h432_3))
private theorem k432_1_0 : check w432 pick432 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k432_1_1 : check w432 pick432 1 t5141 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k432_1_2 : check w432 pick432 1 t9137 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w432 pick432 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t5141 k432_1_0 k432_1_1
private theorem k432_1_3 : check w432 pick432 1 t9655 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k432_1_4 : check w432 pick432 1 t9664 ⟨1,7,2,16,1,52,118,152⟩ = true := by decide +kernel
private theorem k432_1_5 : check w432 pick432 1 t9665 ⟨1,7,2,16,1,52,84,152⟩ = true := glue w432 pick432 1 ⟨1,7,2,16,1,52,84,152⟩ 3 117 t9655 t9664 k432_1_3 k432_1_4
private theorem k432_1_6 : check w432 pick432 1 t9666 ⟨1,7,2,16,1,52,1,152⟩ = true := glue w432 pick432 1 ⟨1,7,2,16,1,52,1,152⟩ 3 83 t9137 t9665 k432_1_2 k432_1_5
private theorem k432_1_7 : check w432 pick432 1 t9667 ⟨1,7,2,16,1,52,153,179⟩ = true := by decide +kernel
private theorem k432_1_8 : check w432 pick432 1 t2374 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k432_1_9 : check w432 pick432 1 t9668 ⟨1,7,2,16,1,52,153,206⟩ = true := glue w432 pick432 1 ⟨1,7,2,16,1,52,153,206⟩ 3 179 t9667 t2374 k432_1_7 k432_1_8
private theorem k432_1_10 : check w432 pick432 1 t2385 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k432_1_11 : check w432 pick432 1 t9150 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k432_1_12 : check w432 pick432 1 t9183 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w432 pick432 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t2385 t9150 k432_1_10 k432_1_11
private theorem k432_1_13 : check w432 pick432 1 t9669 ⟨1,7,2,16,1,52,153,450⟩ = true := glue w432 pick432 1 ⟨1,7,2,16,1,52,153,450⟩ 3 206 t9668 t9183 k432_1_9 k432_1_12
private theorem k432_1_14 : check w432 pick432 1 t9670 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w432 pick432 1 ⟨1,7,2,16,0,52,0,450⟩ 3 152 t9666 t9669 k432_1_6 k432_1_13
theorem cov432_1 : PA.Covered 1 (OZ.Valid 1 w432.low w432.t w432.y w432.r w432.cap) (P33.root 1) :=
  Night6836Tree.sound w432 pick432 1 t9670 _ k432_1_14
private theorem k432_2_0 : check w432 pick432 2 t3223 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k432_2_1 : check w432 pick432 2 t9675 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k432_2_2 : check w432 pick432 2 t9676 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w432 pick432 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t3223 t9675 k432_2_0 k432_2_1
theorem cov432_2 : PA.Covered 2 (OZ.Valid 2 w432.low w432.t w432.y w432.r w432.cap) (P33.root 2) :=
  Night6836Tree.sound w432 pick432 2 t9676 _ k432_2_2
theorem cov432_3 : PA.Covered 3 (OZ.Valid 3 w432.low w432.t w432.y w432.r w432.cap) (P33.root 3) :=
  Night6836Tree.sound w432 pick432 3 t564 _ (by decide +kernel)
theorem cov432_4 : PA.Covered 4 (OZ.Valid 4 w432.low w432.t w432.y w432.r w432.cap) (P33.root 4) :=
  Night6836Tree.sound w432 pick432 4 t565 _ (by decide +kernel)
theorem cov432_5 : PA.Covered 5 (OZ.Valid 5 w432.low w432.t w432.y w432.r w432.cap) (P33.root 5) :=
  Night6836Tree.sound w432 pick432 5 t566 _ (by decide +kernel)
theorem cov432_6 : PA.Covered 6 (OZ.Valid 6 w432.low w432.t w432.y w432.r w432.cap) (P33.root 6) :=
  Night6836Tree.sound w432 pick432 6 t567 _ (by decide +kernel)
theorem cov432_7 : PA.Covered 7 (OZ.Valid 7 w432.low w432.t w432.y w432.r w432.cap) (P33.root 7) :=
  Night6836Tree.sound w432 pick432 7 t2134 _ (by decide +kernel)
theorem window432 : P33.WindowCount w432 := by
  apply P33.window_count w432 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov432_1
  · exact cov432_2
  · exact cov432_3
  · exact cov432_4
  · exact cov432_5
  · exact cov432_6
  · exact cov432_7
def w433 : P33.Window := ⟨7,46,5745,4746,203840188948154559,48014,27000,5000000,81920000000⟩
def h433_0 : Height w433 := ⟨48014,27000,by decide +kernel⟩
def h433_1 : Height w433 := ⟨54268,23000,by decide +kernel⟩
def h433_2 : Height w433 := ⟨63423,19000,by decide +kernel⟩
def h433_3 : Height w433 := ⟨79959,15000,by decide +kernel⟩
def pick433 (cl : ℕ) : Height w433 := if cl<82 then (if cl<10 then (h433_0) else (h433_1)) else (if cl<961 then (h433_2) else (h433_3))
private theorem k433_1_0 : check w433 pick433 1 t9283 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k433_1_1 : check w433 pick433 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k433_1_2 : check w433 pick433 1 t9284 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w433 pick433 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9283 t9190 k433_1_0 k433_1_1
private theorem k433_1_3 : check w433 pick433 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k433_1_4 : check w433 pick433 1 t9678 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k433_1_5 : check w433 pick433 1 t9679 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w433 pick433 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9678 k433_1_3 k433_1_4
private theorem k433_1_6 : check w433 pick433 1 t9680 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w433 pick433 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9284 t9679 k433_1_2 k433_1_5
private theorem k433_1_7 : check w433 pick433 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k433_1_8 : check w433 pick433 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k433_1_9 : check w433 pick433 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w433 pick433 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k433_1_7 k433_1_8
private theorem k433_1_10 : check w433 pick433 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k433_1_11 : check w433 pick433 1 t3708 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k433_1_12 : check w433 pick433 1 t3709 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w433 pick433 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t3708 k433_1_10 k433_1_11
private theorem k433_1_13 : check w433 pick433 1 t3710 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w433 pick433 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t3709 k433_1_9 k433_1_12
private theorem k433_1_14 : check w433 pick433 1 t9681 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w433 pick433 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9680 t3710 k433_1_6 k433_1_13
theorem cov433_1 : PA.Covered 1 (OZ.Valid 1 w433.low w433.t w433.y w433.r w433.cap) (P33.root 1) :=
  Night6836Tree.sound w433 pick433 1 t9681 _ k433_1_14
private theorem k433_2_0 : check w433 pick433 2 t9626 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k433_2_1 : check w433 pick433 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k433_2_2 : check w433 pick433 2 t9682 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w433 pick433 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9626 t9321 k433_2_0 k433_2_1
private theorem k433_2_3 : check w433 pick433 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k433_2_4 : check w433 pick433 2 t4902 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k433_2_5 : check w433 pick433 2 t4903 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w433 pick433 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4902 k433_2_3 k433_2_4
private theorem k433_2_6 : check w433 pick433 2 t9683 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w433 pick433 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9682 t4903 k433_2_2 k433_2_5
theorem cov433_2 : PA.Covered 2 (OZ.Valid 2 w433.low w433.t w433.y w433.r w433.cap) (P33.root 2) :=
  Night6836Tree.sound w433 pick433 2 t9683 _ k433_2_6
theorem cov433_3 : PA.Covered 3 (OZ.Valid 3 w433.low w433.t w433.y w433.r w433.cap) (P33.root 3) :=
  Night6836Tree.sound w433 pick433 3 t564 _ (by decide +kernel)
theorem cov433_4 : PA.Covered 4 (OZ.Valid 4 w433.low w433.t w433.y w433.r w433.cap) (P33.root 4) :=
  Night6836Tree.sound w433 pick433 4 t565 _ (by decide +kernel)
theorem cov433_5 : PA.Covered 5 (OZ.Valid 5 w433.low w433.t w433.y w433.r w433.cap) (P33.root 5) :=
  Night6836Tree.sound w433 pick433 5 t566 _ (by decide +kernel)
theorem cov433_6 : PA.Covered 6 (OZ.Valid 6 w433.low w433.t w433.y w433.r w433.cap) (P33.root 6) :=
  Night6836Tree.sound w433 pick433 6 t567 _ (by decide +kernel)
theorem cov433_7 : PA.Covered 7 (OZ.Valid 7 w433.low w433.t w433.y w433.r w433.cap) (P33.root 7) :=
  Night6836Tree.sound w433 pick433 7 t2134 _ (by decide +kernel)
theorem window433 : P33.WindowCount w433 := by
  apply P33.window_count w433 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov433_1
  · exact cov433_2
  · exact cov433_3
  · exact cov433_4
  · exact cov433_5
  · exact cov433_6
  · exact cov433_7
def w434 : P33.Window := ⟨7,46,7200,7150,245733714723588843,31785,18000,5000000,81920000000⟩
def h434_0 : Height w434 := ⟨31785,18000,by decide +kernel⟩
def h434_1 : Height w434 := ⟨36554,15000,by decide +kernel⟩
def h434_2 : Height w434 := ⟨44064,12000,by decide +kernel⟩
def h434_3 : Height w434 := ⟨60230,9000,by decide +kernel⟩
def pick434 (cl : ℕ) : Height w434 := if cl<135 then (if cl<10 then (h434_0) else (h434_1)) else (if cl<1021 then (h434_2) else (h434_3))
private theorem k434_1_0 : check w434 pick434 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k434_1_1 : check w434 pick434 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k434_1_2 : check w434 pick434 1 t9618 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w434 pick434 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t9617 k434_1_0 k434_1_1
private theorem k434_1_3 : check w434 pick434 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k434_1_4 : check w434 pick434 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k434_1_5 : check w434 pick434 1 t9619 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w434 pick434 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t9606 k434_1_3 k434_1_4
private theorem k434_1_6 : check w434 pick434 1 t9620 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w434 pick434 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9618 t9619 k434_1_2 k434_1_5
private theorem k434_1_7 : check w434 pick434 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k434_1_8 : check w434 pick434 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k434_1_9 : check w434 pick434 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w434 pick434 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k434_1_7 k434_1_8
private theorem k434_1_10 : check w434 pick434 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k434_1_11 : check w434 pick434 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k434_1_12 : check w434 pick434 1 t9364 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w434 pick434 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t9210 k434_1_10 k434_1_11
private theorem k434_1_13 : check w434 pick434 1 t9365 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w434 pick434 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t9364 k434_1_9 k434_1_12
private theorem k434_1_14 : check w434 pick434 1 t9684 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w434 pick434 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9620 t9365 k434_1_6 k434_1_13
theorem cov434_1 : PA.Covered 1 (OZ.Valid 1 w434.low w434.t w434.y w434.r w434.cap) (P33.root 1) :=
  Night6836Tree.sound w434 pick434 1 t9684 _ k434_1_14
private theorem k434_2_0 : check w434 pick434 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k434_2_1 : check w434 pick434 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k434_2_2 : check w434 pick434 2 t3491 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w434 pick434 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3490 k434_2_0 k434_2_1
private theorem k434_2_3 : check w434 pick434 2 t9691 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k434_2_4 : check w434 pick434 2 t9692 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w434 pick434 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3491 t9691 k434_2_2 k434_2_3
theorem cov434_2 : PA.Covered 2 (OZ.Valid 2 w434.low w434.t w434.y w434.r w434.cap) (P33.root 2) :=
  Night6836Tree.sound w434 pick434 2 t9692 _ k434_2_4
theorem cov434_3 : PA.Covered 3 (OZ.Valid 3 w434.low w434.t w434.y w434.r w434.cap) (P33.root 3) :=
  Night6836Tree.sound w434 pick434 3 t564 _ (by decide +kernel)
theorem cov434_4 : PA.Covered 4 (OZ.Valid 4 w434.low w434.t w434.y w434.r w434.cap) (P33.root 4) :=
  Night6836Tree.sound w434 pick434 4 t565 _ (by decide +kernel)
theorem cov434_5 : PA.Covered 5 (OZ.Valid 5 w434.low w434.t w434.y w434.r w434.cap) (P33.root 5) :=
  Night6836Tree.sound w434 pick434 5 t566 _ (by decide +kernel)
theorem cov434_6 : PA.Covered 6 (OZ.Valid 6 w434.low w434.t w434.y w434.r w434.cap) (P33.root 6) :=
  Night6836Tree.sound w434 pick434 6 t567 _ (by decide +kernel)
theorem cov434_7 : PA.Covered 7 (OZ.Valid 7 w434.low w434.t w434.y w434.r w434.cap) (P33.root 7) :=
  Night6836Tree.sound w434 pick434 7 t568 _ (by decide +kernel)
theorem window434 : P33.WindowCount w434 := by
  apply P33.window_count w434 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov434_1
  · exact cov434_2
  · exact cov434_3
  · exact cov434_4
  · exact cov434_5
  · exact cov434_6
  · exact cov434_7
def w435 : P33.Window := ⟨7,47,5146,4147,203715094309936395,56450,31000,5000000,81920000000⟩
def h435_0 : Height w435 := ⟨56450,31000,by decide +kernel⟩
def h435_1 : Height w435 := ⟨62619,27000,by decide +kernel⟩
def h435_2 : Height w435 := ⟨71057,23000,by decide +kernel⟩
def h435_3 : Height w435 := ⟨84297,19000,by decide +kernel⟩
def pick435 (cl : ℕ) : Height w435 := if cl<49 then (if cl<6 then (h435_0) else (h435_1)) else (if cl<458 then (h435_2) else (h435_3))
private theorem k435_1_0 : check w435 pick435 1 t9154 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k435_1_1 : check w435 pick435 1 t9568 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k435_1_2 : check w435 pick435 1 t9569 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w435 pick435 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t9154 t9568 k435_1_0 k435_1_1
private theorem k435_1_3 : check w435 pick435 1 t9693 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k435_1_4 : check w435 pick435 1 t9694 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w435 pick435 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9569 t9693 k435_1_2 k435_1_3
private theorem k435_1_5 : check w435 pick435 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k435_1_6 : check w435 pick435 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k435_1_7 : check w435 pick435 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w435 pick435 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k435_1_5 k435_1_6
private theorem k435_1_8 : check w435 pick435 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k435_1_9 : check w435 pick435 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k435_1_10 : check w435 pick435 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w435 pick435 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k435_1_8 k435_1_9
private theorem k435_1_11 : check w435 pick435 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w435 pick435 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k435_1_7 k435_1_10
private theorem k435_1_12 : check w435 pick435 1 t9695 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w435 pick435 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9694 t9212 k435_1_4 k435_1_11
theorem cov435_1 : PA.Covered 1 (OZ.Valid 1 w435.low w435.t w435.y w435.r w435.cap) (P33.root 1) :=
  Night6836Tree.sound w435 pick435 1 t9695 _ k435_1_12
private theorem k435_2_0 : check w435 pick435 2 t5184 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k435_2_1 : check w435 pick435 2 t9700 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k435_2_2 : check w435 pick435 2 t9701 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w435 pick435 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5184 t9700 k435_2_0 k435_2_1
theorem cov435_2 : PA.Covered 2 (OZ.Valid 2 w435.low w435.t w435.y w435.r w435.cap) (P33.root 2) :=
  Night6836Tree.sound w435 pick435 2 t9701 _ k435_2_2
theorem cov435_3 : PA.Covered 3 (OZ.Valid 3 w435.low w435.t w435.y w435.r w435.cap) (P33.root 3) :=
  Night6836Tree.sound w435 pick435 3 t564 _ (by decide +kernel)
theorem cov435_4 : PA.Covered 4 (OZ.Valid 4 w435.low w435.t w435.y w435.r w435.cap) (P33.root 4) :=
  Night6836Tree.sound w435 pick435 4 t565 _ (by decide +kernel)
theorem cov435_5 : PA.Covered 5 (OZ.Valid 5 w435.low w435.t w435.y w435.r w435.cap) (P33.root 5) :=
  Night6836Tree.sound w435 pick435 5 t566 _ (by decide +kernel)
theorem cov435_6 : PA.Covered 6 (OZ.Valid 6 w435.low w435.t w435.y w435.r w435.cap) (P33.root 6) :=
  Night6836Tree.sound w435 pick435 6 t567 _ (by decide +kernel)
theorem cov435_7 : PA.Covered 7 (OZ.Valid 7 w435.low w435.t w435.y w435.r w435.cap) (P33.root 7) :=
  Night6836Tree.sound w435 pick435 7 t2134 _ (by decide +kernel)
theorem window435 : P33.WindowCount w435 := by
  apply P33.window_count w435 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov435_1
  · exact cov435_2
  · exact cov435_3
  · exact cov435_4
  · exact cov435_5
  · exact cov435_6
  · exact cov435_7
def w436 : P33.Window := ⟨7,47,7149,6856,244747396836929367,35235,18000,5000000,81920000000⟩
def h436_0 : Height w436 := ⟨35235,18000,by decide +kernel⟩
def h436_1 : Height w436 := ⟨40507,15000,by decide +kernel⟩
def h436_2 : Height w436 := ⟨49035,12000,by decide +kernel⟩
def pick436 (cl : ℕ) : Height w436 := if cl<25 then (h436_0) else (if cl<260 then (h436_1) else (h436_2))
private theorem k436_1_0 : check w436 pick436 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k436_1_1 : check w436 pick436 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k436_1_2 : check w436 pick436 1 t9618 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w436 pick436 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t9617 k436_1_0 k436_1_1
private theorem k436_1_3 : check w436 pick436 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k436_1_4 : check w436 pick436 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k436_1_5 : check w436 pick436 1 t9619 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w436 pick436 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t9606 k436_1_3 k436_1_4
private theorem k436_1_6 : check w436 pick436 1 t9620 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w436 pick436 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9618 t9619 k436_1_2 k436_1_5
private theorem k436_1_7 : check w436 pick436 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k436_1_8 : check w436 pick436 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k436_1_9 : check w436 pick436 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w436 pick436 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k436_1_7 k436_1_8
private theorem k436_1_10 : check w436 pick436 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k436_1_11 : check w436 pick436 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k436_1_12 : check w436 pick436 1 t9364 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w436 pick436 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t9210 k436_1_10 k436_1_11
private theorem k436_1_13 : check w436 pick436 1 t9365 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w436 pick436 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t9364 k436_1_9 k436_1_12
private theorem k436_1_14 : check w436 pick436 1 t9684 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w436 pick436 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9620 t9365 k436_1_6 k436_1_13
theorem cov436_1 : PA.Covered 1 (OZ.Valid 1 w436.low w436.t w436.y w436.r w436.cap) (P33.root 1) :=
  Night6836Tree.sound w436 pick436 1 t9684 _ k436_1_14
private theorem k436_2_0 : check w436 pick436 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k436_2_1 : check w436 pick436 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k436_2_2 : check w436 pick436 2 t3491 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w436 pick436 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3490 k436_2_0 k436_2_1
private theorem k436_2_3 : check w436 pick436 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k436_2_4 : check w436 pick436 2 t4902 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k436_2_5 : check w436 pick436 2 t4903 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w436 pick436 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4902 k436_2_3 k436_2_4
private theorem k436_2_6 : check w436 pick436 2 t9702 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w436 pick436 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3491 t4903 k436_2_2 k436_2_5
theorem cov436_2 : PA.Covered 2 (OZ.Valid 2 w436.low w436.t w436.y w436.r w436.cap) (P33.root 2) :=
  Night6836Tree.sound w436 pick436 2 t9702 _ k436_2_6
theorem cov436_3 : PA.Covered 3 (OZ.Valid 3 w436.low w436.t w436.y w436.r w436.cap) (P33.root 3) :=
  Night6836Tree.sound w436 pick436 3 t564 _ (by decide +kernel)
theorem cov436_4 : PA.Covered 4 (OZ.Valid 4 w436.low w436.t w436.y w436.r w436.cap) (P33.root 4) :=
  Night6836Tree.sound w436 pick436 4 t565 _ (by decide +kernel)
theorem cov436_5 : PA.Covered 5 (OZ.Valid 5 w436.low w436.t w436.y w436.r w436.cap) (P33.root 5) :=
  Night6836Tree.sound w436 pick436 5 t566 _ (by decide +kernel)
theorem cov436_6 : PA.Covered 6 (OZ.Valid 6 w436.low w436.t w436.y w436.r w436.cap) (P33.root 6) :=
  Night6836Tree.sound w436 pick436 6 t567 _ (by decide +kernel)
theorem cov436_7 : PA.Covered 7 (OZ.Valid 7 w436.low w436.t w436.y w436.r w436.cap) (P33.root 7) :=
  Night6836Tree.sound w436 pick436 7 t568 _ (by decide +kernel)
theorem window436 : P33.WindowCount w436 := by
  apply P33.window_count w436 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov436_1
  · exact cov436_2
  · exact cov436_3
  · exact cov436_4
  · exact cov436_5
  · exact cov436_6
  · exact cov436_7
def w437 : P33.Window := ⟨7,48,7098,6920,245985523292074287,35670,18000,5000000,81920000000⟩
def h437_0 : Height w437 := ⟨35670,18000,by decide +kernel⟩
def h437_1 : Height w437 := ⟨40926,15000,by decide +kernel⟩
def h437_2 : Height w437 := ⟨49402,12000,by decide +kernel⟩
def pick437 (cl : ℕ) : Height w437 := if cl<25 then (h437_0) else (if cl<237 then (h437_1) else (h437_2))
private theorem k437_1_0 : check w437 pick437 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k437_1_1 : check w437 pick437 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k437_1_2 : check w437 pick437 1 t9618 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w437 pick437 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t9617 k437_1_0 k437_1_1
private theorem k437_1_3 : check w437 pick437 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k437_1_4 : check w437 pick437 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k437_1_5 : check w437 pick437 1 t9619 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w437 pick437 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t9606 k437_1_3 k437_1_4
private theorem k437_1_6 : check w437 pick437 1 t9620 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w437 pick437 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9618 t9619 k437_1_2 k437_1_5
private theorem k437_1_7 : check w437 pick437 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k437_1_8 : check w437 pick437 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k437_1_9 : check w437 pick437 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w437 pick437 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k437_1_7 k437_1_8
private theorem k437_1_10 : check w437 pick437 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k437_1_11 : check w437 pick437 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k437_1_12 : check w437 pick437 1 t9364 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w437 pick437 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t9210 k437_1_10 k437_1_11
private theorem k437_1_13 : check w437 pick437 1 t9365 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w437 pick437 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t9364 k437_1_9 k437_1_12
private theorem k437_1_14 : check w437 pick437 1 t9684 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w437 pick437 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9620 t9365 k437_1_6 k437_1_13
theorem cov437_1 : PA.Covered 1 (OZ.Valid 1 w437.low w437.t w437.y w437.r w437.cap) (P33.root 1) :=
  Night6836Tree.sound w437 pick437 1 t9684 _ k437_1_14
private theorem k437_2_0 : check w437 pick437 2 t9710 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k437_2_1 : check w437 pick437 2 t9719 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k437_2_2 : check w437 pick437 2 t9720 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w437 pick437 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9710 t9719 k437_2_0 k437_2_1
private theorem k437_2_3 : check w437 pick437 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k437_2_4 : check w437 pick437 2 t9721 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k437_2_5 : check w437 pick437 2 t9722 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w437 pick437 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t9721 k437_2_3 k437_2_4
private theorem k437_2_6 : check w437 pick437 2 t9723 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w437 pick437 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9720 t9722 k437_2_2 k437_2_5
theorem cov437_2 : PA.Covered 2 (OZ.Valid 2 w437.low w437.t w437.y w437.r w437.cap) (P33.root 2) :=
  Night6836Tree.sound w437 pick437 2 t9723 _ k437_2_6
theorem cov437_3 : PA.Covered 3 (OZ.Valid 3 w437.low w437.t w437.y w437.r w437.cap) (P33.root 3) :=
  Night6836Tree.sound w437 pick437 3 t564 _ (by decide +kernel)
theorem cov437_4 : PA.Covered 4 (OZ.Valid 4 w437.low w437.t w437.y w437.r w437.cap) (P33.root 4) :=
  Night6836Tree.sound w437 pick437 4 t565 _ (by decide +kernel)
theorem cov437_5 : PA.Covered 5 (OZ.Valid 5 w437.low w437.t w437.y w437.r w437.cap) (P33.root 5) :=
  Night6836Tree.sound w437 pick437 5 t566 _ (by decide +kernel)
theorem cov437_6 : PA.Covered 6 (OZ.Valid 6 w437.low w437.t w437.y w437.r w437.cap) (P33.root 6) :=
  Night6836Tree.sound w437 pick437 6 t567 _ (by decide +kernel)
theorem cov437_7 : PA.Covered 7 (OZ.Valid 7 w437.low w437.t w437.y w437.r w437.cap) (P33.root 7) :=
  Night6836Tree.sound w437 pick437 7 t568 _ (by decide +kernel)
theorem window437 : P33.WindowCount w437 := by
  apply P33.window_count w437 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov437_1
  · exact cov437_2
  · exact cov437_3
  · exact cov437_4
  · exact cov437_5
  · exact cov437_6
  · exact cov437_7
def w438 : P33.Window := ⟨7,49,7043,6982,246447061863185280,36111,18000,5000000,81920000000⟩
def h438_0 : Height w438 := ⟨36111,18000,by decide +kernel⟩
def h438_1 : Height w438 := ⟨41354,15000,by decide +kernel⟩
def h438_2 : Height w438 := ⟨49784,12000,by decide +kernel⟩
def pick438 (cl : ℕ) : Height w438 := if cl<25 then (h438_0) else (if cl<231 then (h438_1) else (h438_2))
private theorem k438_1_0 : check w438 pick438 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k438_1_1 : check w438 pick438 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k438_1_2 : check w438 pick438 1 t9618 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w438 pick438 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t9617 k438_1_0 k438_1_1
private theorem k438_1_3 : check w438 pick438 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k438_1_4 : check w438 pick438 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k438_1_5 : check w438 pick438 1 t9619 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w438 pick438 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t9606 k438_1_3 k438_1_4
private theorem k438_1_6 : check w438 pick438 1 t9620 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w438 pick438 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9618 t9619 k438_1_2 k438_1_5
private theorem k438_1_7 : check w438 pick438 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k438_1_8 : check w438 pick438 1 t3371 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k438_1_9 : check w438 pick438 1 t3372 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w438 pick438 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t3199 t3371 k438_1_7 k438_1_8
private theorem k438_1_10 : check w438 pick438 1 t9726 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k438_1_11 : check w438 pick438 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k438_1_12 : check w438 pick438 1 t9727 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w438 pick438 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t9726 t9397 k438_1_10 k438_1_11
private theorem k438_1_13 : check w438 pick438 1 t9728 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w438 pick438 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t3372 t9727 k438_1_9 k438_1_12
private theorem k438_1_14 : check w438 pick438 1 t9729 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w438 pick438 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9620 t9728 k438_1_6 k438_1_13
theorem cov438_1 : PA.Covered 1 (OZ.Valid 1 w438.low w438.t w438.y w438.r w438.cap) (P33.root 1) :=
  Night6836Tree.sound w438 pick438 1 t9729 _ k438_1_14
private theorem k438_2_0 : check w438 pick438 2 t9710 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k438_2_1 : check w438 pick438 2 t9719 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k438_2_2 : check w438 pick438 2 t9720 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w438 pick438 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9710 t9719 k438_2_0 k438_2_1
private theorem k438_2_3 : check w438 pick438 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k438_2_4 : check w438 pick438 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k438_2_5 : check w438 pick438 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w438 pick438 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k438_2_3 k438_2_4
private theorem k438_2_6 : check w438 pick438 2 t9730 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w438 pick438 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9720 t9436 k438_2_2 k438_2_5
theorem cov438_2 : PA.Covered 2 (OZ.Valid 2 w438.low w438.t w438.y w438.r w438.cap) (P33.root 2) :=
  Night6836Tree.sound w438 pick438 2 t9730 _ k438_2_6
theorem cov438_3 : PA.Covered 3 (OZ.Valid 3 w438.low w438.t w438.y w438.r w438.cap) (P33.root 3) :=
  Night6836Tree.sound w438 pick438 3 t564 _ (by decide +kernel)
theorem cov438_4 : PA.Covered 4 (OZ.Valid 4 w438.low w438.t w438.y w438.r w438.cap) (P33.root 4) :=
  Night6836Tree.sound w438 pick438 4 t565 _ (by decide +kernel)
theorem cov438_5 : PA.Covered 5 (OZ.Valid 5 w438.low w438.t w438.y w438.r w438.cap) (P33.root 5) :=
  Night6836Tree.sound w438 pick438 5 t566 _ (by decide +kernel)
theorem cov438_6 : PA.Covered 6 (OZ.Valid 6 w438.low w438.t w438.y w438.r w438.cap) (P33.root 6) :=
  Night6836Tree.sound w438 pick438 6 t567 _ (by decide +kernel)
theorem cov438_7 : PA.Covered 7 (OZ.Valid 7 w438.low w438.t w438.y w438.r w438.cap) (P33.root 7) :=
  Night6836Tree.sound w438 pick438 7 t568 _ (by decide +kernel)
theorem window438 : P33.WindowCount w438 := by
  apply P33.window_count w438 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov438_1
  · exact cov438_2
  · exact cov438_3
  · exact cov438_4
  · exact cov438_5
  · exact cov438_6
  · exact cov438_7
def w439 : P33.Window := ⟨7,50,6669,5720,241086906644927205,42495,24000,5000000,81920000000⟩
def h439_0 : Height w439 := ⟨42495,24000,by decide +kernel⟩
def h439_1 : Height w439 := ⟨46771,21000,by decide +kernel⟩
def h439_2 : Height w439 := ⟨52439,18000,by decide +kernel⟩
def h439_3 : Height w439 := ⟨60897,15000,by decide +kernel⟩
def h439_4 : Height w439 := ⟨76332,12000,by decide +kernel⟩
def pick439 (cl : ℕ) : Height w439 := if cl<27 then (if cl<4 then (h439_0) else (h439_1)) else (if cl<236 then (h439_2) else (if cl<1013 then (h439_3) else (h439_4)))
private theorem k439_1_0 : check w439 pick439 1 t3241 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k439_1_1 : check w439 pick439 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k439_1_2 : check w439 pick439 1 t9618 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w439 pick439 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t3241 t9617 k439_1_0 k439_1_1
private theorem k439_1_3 : check w439 pick439 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k439_1_4 : check w439 pick439 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k439_1_5 : check w439 pick439 1 t9619 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w439 pick439 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t9606 k439_1_3 k439_1_4
private theorem k439_1_6 : check w439 pick439 1 t9620 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w439 pick439 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9618 t9619 k439_1_2 k439_1_5
private theorem k439_1_7 : check w439 pick439 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k439_1_8 : check w439 pick439 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k439_1_9 : check w439 pick439 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w439 pick439 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k439_1_7 k439_1_8
private theorem k439_1_10 : check w439 pick439 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k439_1_11 : check w439 pick439 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k439_1_12 : check w439 pick439 1 t9364 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w439 pick439 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t9210 k439_1_10 k439_1_11
private theorem k439_1_13 : check w439 pick439 1 t9365 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w439 pick439 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t9364 k439_1_9 k439_1_12
private theorem k439_1_14 : check w439 pick439 1 t9684 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w439 pick439 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9620 t9365 k439_1_6 k439_1_13
theorem cov439_1 : PA.Covered 1 (OZ.Valid 1 w439.low w439.t w439.y w439.r w439.cap) (P33.root 1) :=
  Night6836Tree.sound w439 pick439 1 t9684 _ k439_1_14
private theorem k439_2_0 : check w439 pick439 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k439_2_1 : check w439 pick439 2 t3490 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k439_2_2 : check w439 pick439 2 t3491 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w439 pick439 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3490 k439_2_0 k439_2_1
private theorem k439_2_3 : check w439 pick439 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k439_2_4 : check w439 pick439 2 t4902 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k439_2_5 : check w439 pick439 2 t4903 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w439 pick439 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4902 k439_2_3 k439_2_4
private theorem k439_2_6 : check w439 pick439 2 t9702 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w439 pick439 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3491 t4903 k439_2_2 k439_2_5
theorem cov439_2 : PA.Covered 2 (OZ.Valid 2 w439.low w439.t w439.y w439.r w439.cap) (P33.root 2) :=
  Night6836Tree.sound w439 pick439 2 t9702 _ k439_2_6
theorem cov439_3 : PA.Covered 3 (OZ.Valid 3 w439.low w439.t w439.y w439.r w439.cap) (P33.root 3) :=
  Night6836Tree.sound w439 pick439 3 t564 _ (by decide +kernel)
theorem cov439_4 : PA.Covered 4 (OZ.Valid 4 w439.low w439.t w439.y w439.r w439.cap) (P33.root 4) :=
  Night6836Tree.sound w439 pick439 4 t565 _ (by decide +kernel)
theorem cov439_5 : PA.Covered 5 (OZ.Valid 5 w439.low w439.t w439.y w439.r w439.cap) (P33.root 5) :=
  Night6836Tree.sound w439 pick439 5 t566 _ (by decide +kernel)
theorem cov439_6 : PA.Covered 6 (OZ.Valid 6 w439.low w439.t w439.y w439.r w439.cap) (P33.root 6) :=
  Night6836Tree.sound w439 pick439 6 t567 _ (by decide +kernel)
theorem cov439_7 : PA.Covered 7 (OZ.Valid 7 w439.low w439.t w439.y w439.r w439.cap) (P33.root 7) :=
  Night6836Tree.sound w439 pick439 7 t568 _ (by decide +kernel)
theorem window439 : P33.WindowCount w439 := by
  apply P33.window_count w439 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov439_1
  · exact cov439_2
  · exact cov439_3
  · exact cov439_4
  · exact cov439_5
  · exact cov439_6
  · exact cov439_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w440 : P33.Window := ⟨7,50,6981,6920,246455092424621097,33722,21000,5000000,81920000000⟩
def h440_0 : Height w440 := ⟨33722,21000,by decide +kernel⟩
def h440_1 : Height w440 := ⟨37674,18000,by decide +kernel⟩
def h440_2 : Height w440 := ⟨43097,15000,by decide +kernel⟩
def h440_3 : Height w440 := ⟨51881,12000,by decide +kernel⟩
def pick440 (cl : ℕ) : Height w440 := if cl<25 then (if cl<2 then (h440_0) else (h440_1)) else (if cl<267 then (h440_2) else (h440_3))
private theorem k440_1_0 : check w440 pick440 1 t9733 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k440_1_1 : check w440 pick440 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k440_1_2 : check w440 pick440 1 t9734 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w440 pick440 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9733 t9617 k440_1_0 k440_1_1
private theorem k440_1_3 : check w440 pick440 1 t3263 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k440_1_4 : check w440 pick440 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k440_1_5 : check w440 pick440 1 t9619 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w440 pick440 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t3263 t9606 k440_1_3 k440_1_4
private theorem k440_1_6 : check w440 pick440 1 t9735 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w440 pick440 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9734 t9619 k440_1_2 k440_1_5
private theorem k440_1_7 : check w440 pick440 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k440_1_8 : check w440 pick440 1 t1828 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k440_1_9 : check w440 pick440 1 t9741 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w440 pick440 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t9740 t1828 k440_1_7 k440_1_8
private theorem k440_1_10 : check w440 pick440 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k440_1_11 : check w440 pick440 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k440_1_12 : check w440 pick440 1 t9442 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w440 pick440 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t9397 k440_1_10 k440_1_11
private theorem k440_1_13 : check w440 pick440 1 t9742 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w440 pick440 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t9741 t9442 k440_1_9 k440_1_12
private theorem k440_1_14 : check w440 pick440 1 t9743 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w440 pick440 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9735 t9742 k440_1_6 k440_1_13
theorem cov440_1 : PA.Covered 1 (OZ.Valid 1 w440.low w440.t w440.y w440.r w440.cap) (P33.root 1) :=
  Night6836Tree.sound w440 pick440 1 t9743 _ k440_1_14
private theorem k440_2_0 : check w440 pick440 2 t9748 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k440_2_1 : check w440 pick440 2 t9750 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k440_2_2 : check w440 pick440 2 t9751 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w440 pick440 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9748 t9750 k440_2_0 k440_2_1
private theorem k440_2_3 : check w440 pick440 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k440_2_4 : check w440 pick440 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k440_2_5 : check w440 pick440 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w440 pick440 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k440_2_3 k440_2_4
private theorem k440_2_6 : check w440 pick440 2 t9752 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w440 pick440 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9751 t9436 k440_2_2 k440_2_5
theorem cov440_2 : PA.Covered 2 (OZ.Valid 2 w440.low w440.t w440.y w440.r w440.cap) (P33.root 2) :=
  Night6836Tree.sound w440 pick440 2 t9752 _ k440_2_6
theorem cov440_3 : PA.Covered 3 (OZ.Valid 3 w440.low w440.t w440.y w440.r w440.cap) (P33.root 3) :=
  Night6836Tree.sound w440 pick440 3 t564 _ (by decide +kernel)
theorem cov440_4 : PA.Covered 4 (OZ.Valid 4 w440.low w440.t w440.y w440.r w440.cap) (P33.root 4) :=
  Night6836Tree.sound w440 pick440 4 t565 _ (by decide +kernel)
theorem cov440_5 : PA.Covered 5 (OZ.Valid 5 w440.low w440.t w440.y w440.r w440.cap) (P33.root 5) :=
  Night6836Tree.sound w440 pick440 5 t566 _ (by decide +kernel)
theorem cov440_6 : PA.Covered 6 (OZ.Valid 6 w440.low w440.t w440.y w440.r w440.cap) (P33.root 6) :=
  Night6836Tree.sound w440 pick440 6 t567 _ (by decide +kernel)
theorem cov440_7 : PA.Covered 7 (OZ.Valid 7 w440.low w440.t w440.y w440.r w440.cap) (P33.root 7) :=
  Night6836Tree.sound w440 pick440 7 t568 _ (by decide +kernel)
theorem window440 : P33.WindowCount w440 := by
  apply P33.window_count w440 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov440_1
  · exact cov440_2
  · exact cov440_3
  · exact cov440_4
  · exact cov440_5
  · exact cov440_6
  · exact cov440_7
def w441 : P33.Window := ⟨7,51,6919,6856,246139795249483546,35228,21000,5000000,81920000000⟩
def h441_0 : Height w441 := ⟨35228,21000,by decide +kernel⟩
def h441_1 : Height w441 := ⟨39295,18000,by decide +kernel⟩
def h441_2 : Height w441 := ⟨44910,15000,by decide +kernel⟩
def h441_3 : Height w441 := ⟨54074,12000,by decide +kernel⟩
def pick441 (cl : ℕ) : Height w441 := if cl<26 then (if cl<2 then (h441_0) else (h441_1)) else (if cl<302 then (h441_2) else (h441_3))
private theorem k441_1_0 : check w441 pick441 1 t9753 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k441_1_1 : check w441 pick441 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k441_1_2 : check w441 pick441 1 t9754 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w441 pick441 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9753 t9617 k441_1_0 k441_1_1
private theorem k441_1_3 : check w441 pick441 1 t9756 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k441_1_4 : check w441 pick441 1 t9760 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k441_1_5 : check w441 pick441 1 t9761 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w441 pick441 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9756 t9760 k441_1_3 k441_1_4
private theorem k441_1_6 : check w441 pick441 1 t9762 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w441 pick441 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9754 t9761 k441_1_2 k441_1_5
private theorem k441_1_7 : check w441 pick441 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k441_1_8 : check w441 pick441 1 t1828 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k441_1_9 : check w441 pick441 1 t9741 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w441 pick441 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t9740 t1828 k441_1_7 k441_1_8
private theorem k441_1_10 : check w441 pick441 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k441_1_11 : check w441 pick441 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k441_1_12 : check w441 pick441 1 t9442 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w441 pick441 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t9397 k441_1_10 k441_1_11
private theorem k441_1_13 : check w441 pick441 1 t9742 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w441 pick441 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t9741 t9442 k441_1_9 k441_1_12
private theorem k441_1_14 : check w441 pick441 1 t9763 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w441 pick441 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9762 t9742 k441_1_6 k441_1_13
theorem cov441_1 : PA.Covered 1 (OZ.Valid 1 w441.low w441.t w441.y w441.r w441.cap) (P33.root 1) :=
  Night6836Tree.sound w441 pick441 1 t9763 _ k441_1_14
private theorem k441_2_0 : check w441 pick441 2 t9748 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k441_2_1 : check w441 pick441 2 t9750 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k441_2_2 : check w441 pick441 2 t9751 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w441 pick441 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9748 t9750 k441_2_0 k441_2_1
private theorem k441_2_3 : check w441 pick441 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k441_2_4 : check w441 pick441 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k441_2_5 : check w441 pick441 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w441 pick441 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k441_2_3 k441_2_4
private theorem k441_2_6 : check w441 pick441 2 t9752 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w441 pick441 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9751 t9436 k441_2_2 k441_2_5
theorem cov441_2 : PA.Covered 2 (OZ.Valid 2 w441.low w441.t w441.y w441.r w441.cap) (P33.root 2) :=
  Night6836Tree.sound w441 pick441 2 t9752 _ k441_2_6
theorem cov441_3 : PA.Covered 3 (OZ.Valid 3 w441.low w441.t w441.y w441.r w441.cap) (P33.root 3) :=
  Night6836Tree.sound w441 pick441 3 t564 _ (by decide +kernel)
theorem cov441_4 : PA.Covered 4 (OZ.Valid 4 w441.low w441.t w441.y w441.r w441.cap) (P33.root 4) :=
  Night6836Tree.sound w441 pick441 4 t565 _ (by decide +kernel)
theorem cov441_5 : PA.Covered 5 (OZ.Valid 5 w441.low w441.t w441.y w441.r w441.cap) (P33.root 5) :=
  Night6836Tree.sound w441 pick441 5 t566 _ (by decide +kernel)
theorem cov441_6 : PA.Covered 6 (OZ.Valid 6 w441.low w441.t w441.y w441.r w441.cap) (P33.root 6) :=
  Night6836Tree.sound w441 pick441 6 t567 _ (by decide +kernel)
theorem cov441_7 : PA.Covered 7 (OZ.Valid 7 w441.low w441.t w441.y w441.r w441.cap) (P33.root 7) :=
  Night6836Tree.sound w441 pick441 7 t568 _ (by decide +kernel)
theorem window441 : P33.WindowCount w441 := by
  apply P33.window_count w441 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov441_1
  · exact cov441_2
  · exact cov441_3
  · exact cov441_4
  · exact cov441_5
  · exact cov441_6
  · exact cov441_7
def w442 : P33.Window := ⟨7,52,6855,6788,245416786357619025,36808,21000,5000000,81920000000⟩
def h442_0 : Height w442 := ⟨36808,21000,by decide +kernel⟩
def h442_1 : Height w442 := ⟨41000,18000,by decide +kernel⟩
def h442_2 : Height w442 := ⟨46823,15000,by decide +kernel⟩
def h442_3 : Height w442 := ⟨56401,12000,by decide +kernel⟩
def pick442 (cl : ℕ) : Height w442 := if cl<32 then (if cl<4 then (h442_0) else (h442_1)) else (if cl<331 then (h442_2) else (h442_3))
private theorem k442_1_0 : check w442 pick442 1 t9766 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k442_1_1 : check w442 pick442 1 t9773 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k442_1_2 : check w442 pick442 1 t9774 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w442 pick442 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9766 t9773 k442_1_0 k442_1_1
private theorem k442_1_3 : check w442 pick442 1 t9776 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k442_1_4 : check w442 pick442 1 t9760 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k442_1_5 : check w442 pick442 1 t9777 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w442 pick442 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9776 t9760 k442_1_3 k442_1_4
private theorem k442_1_6 : check w442 pick442 1 t9778 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w442 pick442 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9774 t9777 k442_1_2 k442_1_5
private theorem k442_1_7 : check w442 pick442 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k442_1_8 : check w442 pick442 1 t1828 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k442_1_9 : check w442 pick442 1 t9741 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w442 pick442 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t9740 t1828 k442_1_7 k442_1_8
private theorem k442_1_10 : check w442 pick442 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k442_1_11 : check w442 pick442 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k442_1_12 : check w442 pick442 1 t9442 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w442 pick442 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t9397 k442_1_10 k442_1_11
private theorem k442_1_13 : check w442 pick442 1 t9742 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w442 pick442 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t9741 t9442 k442_1_9 k442_1_12
private theorem k442_1_14 : check w442 pick442 1 t9779 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w442 pick442 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9778 t9742 k442_1_6 k442_1_13
theorem cov442_1 : PA.Covered 1 (OZ.Valid 1 w442.low w442.t w442.y w442.r w442.cap) (P33.root 1) :=
  Night6836Tree.sound w442 pick442 1 t9779 _ k442_1_14
private theorem k442_2_0 : check w442 pick442 2 t9748 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k442_2_1 : check w442 pick442 2 t9750 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k442_2_2 : check w442 pick442 2 t9751 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w442 pick442 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9748 t9750 k442_2_0 k442_2_1
private theorem k442_2_3 : check w442 pick442 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k442_2_4 : check w442 pick442 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k442_2_5 : check w442 pick442 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w442 pick442 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k442_2_3 k442_2_4
private theorem k442_2_6 : check w442 pick442 2 t9752 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w442 pick442 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9751 t9436 k442_2_2 k442_2_5
theorem cov442_2 : PA.Covered 2 (OZ.Valid 2 w442.low w442.t w442.y w442.r w442.cap) (P33.root 2) :=
  Night6836Tree.sound w442 pick442 2 t9752 _ k442_2_6
theorem cov442_3 : PA.Covered 3 (OZ.Valid 3 w442.low w442.t w442.y w442.r w442.cap) (P33.root 3) :=
  Night6836Tree.sound w442 pick442 3 t564 _ (by decide +kernel)
theorem cov442_4 : PA.Covered 4 (OZ.Valid 4 w442.low w442.t w442.y w442.r w442.cap) (P33.root 4) :=
  Night6836Tree.sound w442 pick442 4 t565 _ (by decide +kernel)
theorem cov442_5 : PA.Covered 5 (OZ.Valid 5 w442.low w442.t w442.y w442.r w442.cap) (P33.root 5) :=
  Night6836Tree.sound w442 pick442 5 t566 _ (by decide +kernel)
theorem cov442_6 : PA.Covered 6 (OZ.Valid 6 w442.low w442.t w442.y w442.r w442.cap) (P33.root 6) :=
  Night6836Tree.sound w442 pick442 6 t567 _ (by decide +kernel)
theorem cov442_7 : PA.Covered 7 (OZ.Valid 7 w442.low w442.t w442.y w442.r w442.cap) (P33.root 7) :=
  Night6836Tree.sound w442 pick442 7 t568 _ (by decide +kernel)
theorem window442 : P33.WindowCount w442 := by
  apply P33.window_count w442 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov442_1
  · exact cov442_2
  · exact cov442_3
  · exact cov442_4
  · exact cov442_5
  · exact cov442_6
  · exact cov442_7
def w443 : P33.Window := ⟨7,53,6669,5720,245498114025536350,46004,24000,5000000,81920000000⟩
def h443_0 : Height w443 := ⟨46004,24000,by decide +kernel⟩
def h443_1 : Height w443 := ⟨50457,21000,by decide +kernel⟩
def h443_2 : Height w443 := ⟨56390,18000,by decide +kernel⟩
def h443_3 : Height w443 := ⟨65288,15000,by decide +kernel⟩
def h443_4 : Height w443 := ⟨81596,12000,by decide +kernel⟩
def pick443 (cl : ℕ) : Height w443 := if cl<36 then (if cl<5 then (h443_0) else (h443_1)) else (if cl<273 then (h443_2) else (if cl<1021 then (h443_3) else (h443_4)))
private theorem k443_1_0 : check w443 pick443 1 t9753 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k443_1_1 : check w443 pick443 1 t9617 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k443_1_2 : check w443 pick443 1 t9754 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w443 pick443 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9753 t9617 k443_1_0 k443_1_1
private theorem k443_1_3 : check w443 pick443 1 t9756 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k443_1_4 : check w443 pick443 1 t9760 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k443_1_5 : check w443 pick443 1 t9761 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w443 pick443 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9756 t9760 k443_1_3 k443_1_4
private theorem k443_1_6 : check w443 pick443 1 t9762 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w443 pick443 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9754 t9761 k443_1_2 k443_1_5
private theorem k443_1_7 : check w443 pick443 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k443_1_8 : check w443 pick443 1 t1828 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k443_1_9 : check w443 pick443 1 t9741 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w443 pick443 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t9740 t1828 k443_1_7 k443_1_8
private theorem k443_1_10 : check w443 pick443 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k443_1_11 : check w443 pick443 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k443_1_12 : check w443 pick443 1 t9442 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w443 pick443 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t9397 k443_1_10 k443_1_11
private theorem k443_1_13 : check w443 pick443 1 t9742 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w443 pick443 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t9741 t9442 k443_1_9 k443_1_12
private theorem k443_1_14 : check w443 pick443 1 t9763 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w443 pick443 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9762 t9742 k443_1_6 k443_1_13
theorem cov443_1 : PA.Covered 1 (OZ.Valid 1 w443.low w443.t w443.y w443.r w443.cap) (P33.root 1) :=
  Night6836Tree.sound w443 pick443 1 t9763 _ k443_1_14
private theorem k443_2_0 : check w443 pick443 2 t9748 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k443_2_1 : check w443 pick443 2 t9750 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k443_2_2 : check w443 pick443 2 t9751 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w443 pick443 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9748 t9750 k443_2_0 k443_2_1
private theorem k443_2_3 : check w443 pick443 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k443_2_4 : check w443 pick443 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k443_2_5 : check w443 pick443 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w443 pick443 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k443_2_3 k443_2_4
private theorem k443_2_6 : check w443 pick443 2 t9752 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w443 pick443 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9751 t9436 k443_2_2 k443_2_5
theorem cov443_2 : PA.Covered 2 (OZ.Valid 2 w443.low w443.t w443.y w443.r w443.cap) (P33.root 2) :=
  Night6836Tree.sound w443 pick443 2 t9752 _ k443_2_6
theorem cov443_3 : PA.Covered 3 (OZ.Valid 3 w443.low w443.t w443.y w443.r w443.cap) (P33.root 3) :=
  Night6836Tree.sound w443 pick443 3 t564 _ (by decide +kernel)
theorem cov443_4 : PA.Covered 4 (OZ.Valid 4 w443.low w443.t w443.y w443.r w443.cap) (P33.root 4) :=
  Night6836Tree.sound w443 pick443 4 t565 _ (by decide +kernel)
theorem cov443_5 : PA.Covered 5 (OZ.Valid 5 w443.low w443.t w443.y w443.r w443.cap) (P33.root 5) :=
  Night6836Tree.sound w443 pick443 5 t566 _ (by decide +kernel)
theorem cov443_6 : PA.Covered 6 (OZ.Valid 6 w443.low w443.t w443.y w443.r w443.cap) (P33.root 6) :=
  Night6836Tree.sound w443 pick443 6 t567 _ (by decide +kernel)
theorem cov443_7 : PA.Covered 7 (OZ.Valid 7 w443.low w443.t w443.y w443.r w443.cap) (P33.root 7) :=
  Night6836Tree.sound w443 pick443 7 t568 _ (by decide +kernel)
theorem window443 : P33.WindowCount w443 := by
  apply P33.window_count w443 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov443_1
  · exact cov443_2
  · exact cov443_3
  · exact cov443_4
  · exact cov443_5
  · exact cov443_6
  · exact cov443_7
def w444 : P33.Window := ⟨7,53,6787,6709,243925327209258062,38536,21000,5000000,81920000000⟩
def h444_0 : Height w444 := ⟨38536,21000,by decide +kernel⟩
def h444_1 : Height w444 := ⟨42872,18000,by decide +kernel⟩
def h444_2 : Height w444 := ⟨48936,15000,by decide +kernel⟩
def h444_3 : Height w444 := ⟨58996,12000,by decide +kernel⟩
def pick444 (cl : ℕ) : Height w444 := if cl<40 then (if cl<5 then (h444_0) else (h444_1)) else (if cl<507 then (h444_2) else (h444_3))
private theorem k444_1_0 : check w444 pick444 1 t9766 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k444_1_1 : check w444 pick444 1 t9773 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k444_1_2 : check w444 pick444 1 t9774 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w444 pick444 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9766 t9773 k444_1_0 k444_1_1
private theorem k444_1_3 : check w444 pick444 1 t9776 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k444_1_4 : check w444 pick444 1 t9760 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k444_1_5 : check w444 pick444 1 t9777 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w444 pick444 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9776 t9760 k444_1_3 k444_1_4
private theorem k444_1_6 : check w444 pick444 1 t9778 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w444 pick444 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9774 t9777 k444_1_2 k444_1_5
private theorem k444_1_7 : check w444 pick444 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k444_1_8 : check w444 pick444 1 t1828 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k444_1_9 : check w444 pick444 1 t9741 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w444 pick444 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t9740 t1828 k444_1_7 k444_1_8
private theorem k444_1_10 : check w444 pick444 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k444_1_11 : check w444 pick444 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k444_1_12 : check w444 pick444 1 t9442 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w444 pick444 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t9397 k444_1_10 k444_1_11
private theorem k444_1_13 : check w444 pick444 1 t9742 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w444 pick444 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t9741 t9442 k444_1_9 k444_1_12
private theorem k444_1_14 : check w444 pick444 1 t9779 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w444 pick444 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9778 t9742 k444_1_6 k444_1_13
theorem cov444_1 : PA.Covered 1 (OZ.Valid 1 w444.low w444.t w444.y w444.r w444.cap) (P33.root 1) :=
  Night6836Tree.sound w444 pick444 1 t9779 _ k444_1_14
private theorem k444_2_0 : check w444 pick444 2 t9748 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k444_2_1 : check w444 pick444 2 t5002 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k444_2_2 : check w444 pick444 2 t9780 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w444 pick444 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9748 t5002 k444_2_0 k444_2_1
private theorem k444_2_3 : check w444 pick444 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k444_2_4 : check w444 pick444 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k444_2_5 : check w444 pick444 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w444 pick444 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k444_2_3 k444_2_4
private theorem k444_2_6 : check w444 pick444 2 t9781 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w444 pick444 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9780 t9436 k444_2_2 k444_2_5
theorem cov444_2 : PA.Covered 2 (OZ.Valid 2 w444.low w444.t w444.y w444.r w444.cap) (P33.root 2) :=
  Night6836Tree.sound w444 pick444 2 t9781 _ k444_2_6
theorem cov444_3 : PA.Covered 3 (OZ.Valid 3 w444.low w444.t w444.y w444.r w444.cap) (P33.root 3) :=
  Night6836Tree.sound w444 pick444 3 t564 _ (by decide +kernel)
theorem cov444_4 : PA.Covered 4 (OZ.Valid 4 w444.low w444.t w444.y w444.r w444.cap) (P33.root 4) :=
  Night6836Tree.sound w444 pick444 4 t565 _ (by decide +kernel)
theorem cov444_5 : PA.Covered 5 (OZ.Valid 5 w444.low w444.t w444.y w444.r w444.cap) (P33.root 5) :=
  Night6836Tree.sound w444 pick444 5 t566 _ (by decide +kernel)
theorem cov444_6 : PA.Covered 6 (OZ.Valid 6 w444.low w444.t w444.y w444.r w444.cap) (P33.root 6) :=
  Night6836Tree.sound w444 pick444 6 t567 _ (by decide +kernel)
theorem cov444_7 : PA.Covered 7 (OZ.Valid 7 w444.low w444.t w444.y w444.r w444.cap) (P33.root 7) :=
  Night6836Tree.sound w444 pick444 7 t568 _ (by decide +kernel)
theorem window444 : P33.WindowCount w444 := by
  apply P33.window_count w444 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov444_1
  · exact cov444_2
  · exact cov444_3
  · exact cov444_4
  · exact cov444_5
  · exact cov444_6
  · exact cov444_7
def w445 : P33.Window := ⟨7,54,6708,6623,244571001279386486,40391,21000,5000000,81920000000⟩
def h445_0 : Height w445 := ⟨40391,21000,by decide +kernel⟩
def h445_1 : Height w445 := ⟨44887,18000,by decide +kernel⟩
def h445_2 : Height w445 := ⟨51220,15000,by decide +kernel⟩
def h445_3 : Height w445 := ⟨61827,12000,by decide +kernel⟩
def pick445 (cl : ℕ) : Height w445 := if cl<49 then (if cl<5 then (h445_0) else (h445_1)) else (if cl<728 then (h445_2) else (h445_3))
private theorem k445_1_0 : check w445 pick445 1 t9766 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k445_1_1 : check w445 pick445 1 t9773 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k445_1_2 : check w445 pick445 1 t9774 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w445 pick445 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9766 t9773 k445_1_0 k445_1_1
private theorem k445_1_3 : check w445 pick445 1 t9776 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k445_1_4 : check w445 pick445 1 t9760 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k445_1_5 : check w445 pick445 1 t9777 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w445 pick445 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9776 t9760 k445_1_3 k445_1_4
private theorem k445_1_6 : check w445 pick445 1 t9778 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w445 pick445 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9774 t9777 k445_1_2 k445_1_5
private theorem k445_1_7 : check w445 pick445 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k445_1_8 : check w445 pick445 1 t1828 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k445_1_9 : check w445 pick445 1 t9741 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w445 pick445 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t9740 t1828 k445_1_7 k445_1_8
private theorem k445_1_10 : check w445 pick445 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k445_1_11 : check w445 pick445 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k445_1_12 : check w445 pick445 1 t9442 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w445 pick445 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t9397 k445_1_10 k445_1_11
private theorem k445_1_13 : check w445 pick445 1 t9742 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w445 pick445 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t9741 t9442 k445_1_9 k445_1_12
private theorem k445_1_14 : check w445 pick445 1 t9779 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w445 pick445 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9778 t9742 k445_1_6 k445_1_13
theorem cov445_1 : PA.Covered 1 (OZ.Valid 1 w445.low w445.t w445.y w445.r w445.cap) (P33.root 1) :=
  Night6836Tree.sound w445 pick445 1 t9779 _ k445_1_14
private theorem k445_2_0 : check w445 pick445 2 t9748 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k445_2_1 : check w445 pick445 2 t5002 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k445_2_2 : check w445 pick445 2 t9780 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w445 pick445 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9748 t5002 k445_2_0 k445_2_1
private theorem k445_2_3 : check w445 pick445 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k445_2_4 : check w445 pick445 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k445_2_5 : check w445 pick445 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w445 pick445 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k445_2_3 k445_2_4
private theorem k445_2_6 : check w445 pick445 2 t9781 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w445 pick445 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9780 t9436 k445_2_2 k445_2_5
theorem cov445_2 : PA.Covered 2 (OZ.Valid 2 w445.low w445.t w445.y w445.r w445.cap) (P33.root 2) :=
  Night6836Tree.sound w445 pick445 2 t9781 _ k445_2_6
theorem cov445_3 : PA.Covered 3 (OZ.Valid 3 w445.low w445.t w445.y w445.r w445.cap) (P33.root 3) :=
  Night6836Tree.sound w445 pick445 3 t564 _ (by decide +kernel)
theorem cov445_4 : PA.Covered 4 (OZ.Valid 4 w445.low w445.t w445.y w445.r w445.cap) (P33.root 4) :=
  Night6836Tree.sound w445 pick445 4 t565 _ (by decide +kernel)
theorem cov445_5 : PA.Covered 5 (OZ.Valid 5 w445.low w445.t w445.y w445.r w445.cap) (P33.root 5) :=
  Night6836Tree.sound w445 pick445 5 t566 _ (by decide +kernel)
theorem cov445_6 : PA.Covered 6 (OZ.Valid 6 w445.low w445.t w445.y w445.r w445.cap) (P33.root 6) :=
  Night6836Tree.sound w445 pick445 6 t567 _ (by decide +kernel)
theorem cov445_7 : PA.Covered 7 (OZ.Valid 7 w445.low w445.t w445.y w445.r w445.cap) (P33.root 7) :=
  Night6836Tree.sound w445 pick445 7 t568 _ (by decide +kernel)
theorem window445 : P33.WindowCount w445 := by
  apply P33.window_count w445 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov445_1
  · exact cov445_2
  · exact cov445_3
  · exact cov445_4
  · exact cov445_5
  · exact cov445_6
  · exact cov445_7
def w446 : P33.Window := ⟨7,55,5506,4557,243742064919216422,60825,30000,5000000,81920000000⟩
def h446_0 : Height w446 := ⟨60825,30000,by decide +kernel⟩
def h446_1 : Height w446 := ⟨65302,27000,by decide +kernel⟩
def h446_2 : Height w446 := ⟨70865,24000,by decide +kernel⟩
def h446_3 : Height w446 := ⟨78238,21000,by decide +kernel⟩
def h446_4 : Height w446 := ⟨88974,18000,by decide +kernel⟩
def pick446 (cl : ℕ) : Height w446 := if cl<32 then (if cl<5 then (h446_0) else (h446_1)) else (if cl<117 then (h446_2) else (if cl<922 then (h446_3) else (h446_4)))
private theorem k446_1_0 : check w446 pick446 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k446_1_1 : check w446 pick446 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k446_1_2 : check w446 pick446 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w446 pick446 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k446_1_0 k446_1_1
private theorem k446_1_3 : check w446 pick446 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k446_1_4 : check w446 pick446 1 t9579 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k446_1_5 : check w446 pick446 1 t9580 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w446 pick446 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9579 k446_1_3 k446_1_4
private theorem k446_1_6 : check w446 pick446 1 t9581 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w446 pick446 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9580 k446_1_2 k446_1_5
private theorem k446_1_7 : check w446 pick446 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k446_1_8 : check w446 pick446 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k446_1_9 : check w446 pick446 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w446 pick446 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k446_1_7 k446_1_8
private theorem k446_1_10 : check w446 pick446 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k446_1_11 : check w446 pick446 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k446_1_12 : check w446 pick446 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w446 pick446 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k446_1_10 k446_1_11
private theorem k446_1_13 : check w446 pick446 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w446 pick446 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k446_1_9 k446_1_12
private theorem k446_1_14 : check w446 pick446 1 t9782 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w446 pick446 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9581 t9212 k446_1_6 k446_1_13
theorem cov446_1 : PA.Covered 1 (OZ.Valid 1 w446.low w446.t w446.y w446.r w446.cap) (P33.root 1) :=
  Night6836Tree.sound w446 pick446 1 t9782 _ k446_1_14
private theorem k446_2_0 : check w446 pick446 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k446_2_1 : check w446 pick446 2 t4017 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k446_2_2 : check w446 pick446 2 t9783 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w446 pick446 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t4017 k446_2_0 k446_2_1
theorem cov446_2 : PA.Covered 2 (OZ.Valid 2 w446.low w446.t w446.y w446.r w446.cap) (P33.root 2) :=
  Night6836Tree.sound w446 pick446 2 t9783 _ k446_2_2
theorem cov446_3 : PA.Covered 3 (OZ.Valid 3 w446.low w446.t w446.y w446.r w446.cap) (P33.root 3) :=
  Night6836Tree.sound w446 pick446 3 t564 _ (by decide +kernel)
theorem cov446_4 : PA.Covered 4 (OZ.Valid 4 w446.low w446.t w446.y w446.r w446.cap) (P33.root 4) :=
  Night6836Tree.sound w446 pick446 4 t565 _ (by decide +kernel)
theorem cov446_5 : PA.Covered 5 (OZ.Valid 5 w446.low w446.t w446.y w446.r w446.cap) (P33.root 5) :=
  Night6836Tree.sound w446 pick446 5 t566 _ (by decide +kernel)
theorem cov446_6 : PA.Covered 6 (OZ.Valid 6 w446.low w446.t w446.y w446.r w446.cap) (P33.root 6) :=
  Night6836Tree.sound w446 pick446 6 t567 _ (by decide +kernel)
theorem cov446_7 : PA.Covered 7 (OZ.Valid 7 w446.low w446.t w446.y w446.r w446.cap) (P33.root 7) :=
  Night6836Tree.sound w446 pick446 7 t2134 _ (by decide +kernel)
theorem window446 : P33.WindowCount w446 := by
  apply P33.window_count w446 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov446_1
  · exact cov446_2
  · exact cov446_3
  · exact cov446_4
  · exact cov446_5
  · exact cov446_6
  · exact cov446_7
def w447 : P33.Window := ⟨7,55,6622,6421,244888847282417060,43595,21000,5000000,81920000000⟩
def h447_0 : Height w447 := ⟨43595,21000,by decide +kernel⟩
def h447_1 : Height w447 := ⟨48421,18000,by decide +kernel⟩
def h447_2 : Height w447 := ⟨55320,15000,by decide +kernel⟩
def h447_3 : Height w447 := ⟨67107,12000,by decide +kernel⟩
def pick447 (cl : ℕ) : Height w447 := if cl<83 then (if cl<10 then (h447_0) else (h447_1)) else (if cl<922 then (h447_2) else (h447_3))
private theorem k447_1_0 : check w447 pick447 1 t9766 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k447_1_1 : check w447 pick447 1 t9773 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k447_1_2 : check w447 pick447 1 t9774 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w447 pick447 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9766 t9773 k447_1_0 k447_1_1
private theorem k447_1_3 : check w447 pick447 1 t9776 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k447_1_4 : check w447 pick447 1 t9760 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k447_1_5 : check w447 pick447 1 t9777 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w447 pick447 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9776 t9760 k447_1_3 k447_1_4
private theorem k447_1_6 : check w447 pick447 1 t9778 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w447 pick447 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9774 t9777 k447_1_2 k447_1_5
private theorem k447_1_7 : check w447 pick447 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k447_1_8 : check w447 pick447 1 t1828 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k447_1_9 : check w447 pick447 1 t9741 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w447 pick447 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t9740 t1828 k447_1_7 k447_1_8
private theorem k447_1_10 : check w447 pick447 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k447_1_11 : check w447 pick447 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k447_1_12 : check w447 pick447 1 t9442 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w447 pick447 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t9397 k447_1_10 k447_1_11
private theorem k447_1_13 : check w447 pick447 1 t9742 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w447 pick447 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t9741 t9442 k447_1_9 k447_1_12
private theorem k447_1_14 : check w447 pick447 1 t9779 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w447 pick447 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9778 t9742 k447_1_6 k447_1_13
theorem cov447_1 : PA.Covered 1 (OZ.Valid 1 w447.low w447.t w447.y w447.r w447.cap) (P33.root 1) :=
  Night6836Tree.sound w447 pick447 1 t9779 _ k447_1_14
private theorem k447_2_0 : check w447 pick447 2 t9748 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k447_2_1 : check w447 pick447 2 t5002 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k447_2_2 : check w447 pick447 2 t9780 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w447 pick447 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9748 t5002 k447_2_0 k447_2_1
private theorem k447_2_3 : check w447 pick447 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k447_2_4 : check w447 pick447 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k447_2_5 : check w447 pick447 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w447 pick447 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k447_2_3 k447_2_4
private theorem k447_2_6 : check w447 pick447 2 t9781 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w447 pick447 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9780 t9436 k447_2_2 k447_2_5
theorem cov447_2 : PA.Covered 2 (OZ.Valid 2 w447.low w447.t w447.y w447.r w447.cap) (P33.root 2) :=
  Night6836Tree.sound w447 pick447 2 t9781 _ k447_2_6
theorem cov447_3 : PA.Covered 3 (OZ.Valid 3 w447.low w447.t w447.y w447.r w447.cap) (P33.root 3) :=
  Night6836Tree.sound w447 pick447 3 t564 _ (by decide +kernel)
theorem cov447_4 : PA.Covered 4 (OZ.Valid 4 w447.low w447.t w447.y w447.r w447.cap) (P33.root 4) :=
  Night6836Tree.sound w447 pick447 4 t565 _ (by decide +kernel)
theorem cov447_5 : PA.Covered 5 (OZ.Valid 5 w447.low w447.t w447.y w447.r w447.cap) (P33.root 5) :=
  Night6836Tree.sound w447 pick447 5 t566 _ (by decide +kernel)
theorem cov447_6 : PA.Covered 6 (OZ.Valid 6 w447.low w447.t w447.y w447.r w447.cap) (P33.root 6) :=
  Night6836Tree.sound w447 pick447 6 t567 _ (by decide +kernel)
theorem cov447_7 : PA.Covered 7 (OZ.Valid 7 w447.low w447.t w447.y w447.r w447.cap) (P33.root 7) :=
  Night6836Tree.sound w447 pick447 7 t568 _ (by decide +kernel)
theorem window447 : P33.WindowCount w447 := by
  apply P33.window_count w447 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov447_1
  · exact cov447_2
  · exact cov447_3
  · exact cov447_4
  · exact cov447_5
  · exact cov447_6
  · exact cov447_7
def w448 : P33.Window := ⟨7,56,6420,6078,240920478635709054,44760,24000,5000000,81920000000⟩
def h448_0 : Height w448 := ⟨44760,24000,by decide +kernel⟩
def h448_1 : Height w448 := ⟨48916,21000,by decide +kernel⟩
def h448_2 : Height w448 := ⟨54366,18000,by decide +kernel⟩
def h448_3 : Height w448 := ⟨62358,15000,by decide +kernel⟩
def h448_4 : Height w448 := ⟨76496,12000,by decide +kernel⟩
def pick448 (cl : ℕ) : Height w448 := if cl<23 then (if cl<4 then (h448_0) else (h448_1)) else (if cl<182 then (h448_2) else (if cl<984 then (h448_3) else (h448_4)))
private theorem k448_1_0 : check w448 pick448 1 t9766 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k448_1_1 : check w448 pick448 1 t9773 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k448_1_2 : check w448 pick448 1 t9774 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w448 pick448 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9766 t9773 k448_1_0 k448_1_1
private theorem k448_1_3 : check w448 pick448 1 t9776 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k448_1_4 : check w448 pick448 1 t9760 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k448_1_5 : check w448 pick448 1 t9777 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w448 pick448 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9776 t9760 k448_1_3 k448_1_4
private theorem k448_1_6 : check w448 pick448 1 t9778 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w448 pick448 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9774 t9777 k448_1_2 k448_1_5
private theorem k448_1_7 : check w448 pick448 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k448_1_8 : check w448 pick448 1 t1828 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k448_1_9 : check w448 pick448 1 t9741 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w448 pick448 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t9740 t1828 k448_1_7 k448_1_8
private theorem k448_1_10 : check w448 pick448 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k448_1_11 : check w448 pick448 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k448_1_12 : check w448 pick448 1 t9442 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w448 pick448 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t9397 k448_1_10 k448_1_11
private theorem k448_1_13 : check w448 pick448 1 t9742 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w448 pick448 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t9741 t9442 k448_1_9 k448_1_12
private theorem k448_1_14 : check w448 pick448 1 t9779 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w448 pick448 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9778 t9742 k448_1_6 k448_1_13
theorem cov448_1 : PA.Covered 1 (OZ.Valid 1 w448.low w448.t w448.y w448.r w448.cap) (P33.root 1) :=
  Night6836Tree.sound w448 pick448 1 t9779 _ k448_1_14
private theorem k448_2_0 : check w448 pick448 2 t9748 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k448_2_1 : check w448 pick448 2 t5002 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k448_2_2 : check w448 pick448 2 t9780 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w448 pick448 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9748 t5002 k448_2_0 k448_2_1
private theorem k448_2_3 : check w448 pick448 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k448_2_4 : check w448 pick448 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k448_2_5 : check w448 pick448 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w448 pick448 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k448_2_3 k448_2_4
private theorem k448_2_6 : check w448 pick448 2 t9781 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w448 pick448 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9780 t9436 k448_2_2 k448_2_5
theorem cov448_2 : PA.Covered 2 (OZ.Valid 2 w448.low w448.t w448.y w448.r w448.cap) (P33.root 2) :=
  Night6836Tree.sound w448 pick448 2 t9781 _ k448_2_6
theorem cov448_3 : PA.Covered 3 (OZ.Valid 3 w448.low w448.t w448.y w448.r w448.cap) (P33.root 3) :=
  Night6836Tree.sound w448 pick448 3 t564 _ (by decide +kernel)
theorem cov448_4 : PA.Covered 4 (OZ.Valid 4 w448.low w448.t w448.y w448.r w448.cap) (P33.root 4) :=
  Night6836Tree.sound w448 pick448 4 t565 _ (by decide +kernel)
theorem cov448_5 : PA.Covered 5 (OZ.Valid 5 w448.low w448.t w448.y w448.r w448.cap) (P33.root 5) :=
  Night6836Tree.sound w448 pick448 5 t566 _ (by decide +kernel)
theorem cov448_6 : PA.Covered 6 (OZ.Valid 6 w448.low w448.t w448.y w448.r w448.cap) (P33.root 6) :=
  Night6836Tree.sound w448 pick448 6 t567 _ (by decide +kernel)
theorem cov448_7 : PA.Covered 7 (OZ.Valid 7 w448.low w448.t w448.y w448.r w448.cap) (P33.root 7) :=
  Night6836Tree.sound w448 pick448 7 t2134 _ (by decide +kernel)
theorem window448 : P33.WindowCount w448 := by
  apply P33.window_count w448 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov448_1
  · exact cov448_2
  · exact cov448_3
  · exact cov448_4
  · exact cov448_5
  · exact cov448_6
  · exact cov448_7
def w449 : P33.Window := ⟨7,57,6077,5720,245923584776681727,50682,24000,5000000,81920000000⟩
def h449_0 : Height w449 := ⟨50682,24000,by decide +kernel⟩
def h449_1 : Height w449 := ⟨55370,21000,by decide +kernel⟩
def h449_2 : Height w449 := ⟨61655,18000,by decide +kernel⟩
def h449_3 : Height w449 := ⟨71138,15000,by decide +kernel⟩
def pick449 (cl : ℕ) : Height w449 := if cl<47 then (if cl<10 then (h449_0) else (h449_1)) else (if cl<312 then (h449_2) else (h449_3))
private theorem k449_1_0 : check w449 pick449 1 t5078 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k449_1_1 : check w449 pick449 1 t9785 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k449_1_2 : check w449 pick449 1 t9786 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w449 pick449 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5078 t9785 k449_1_0 k449_1_1
private theorem k449_1_3 : check w449 pick449 1 t3192 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k449_1_4 : check w449 pick449 1 t9606 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k449_1_5 : check w449 pick449 1 t9787 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w449 pick449 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t3192 t9606 k449_1_3 k449_1_4
private theorem k449_1_6 : check w449 pick449 1 t9788 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w449 pick449 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9786 t9787 k449_1_2 k449_1_5
private theorem k449_1_7 : check w449 pick449 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k449_1_8 : check w449 pick449 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k449_1_9 : check w449 pick449 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w449 pick449 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k449_1_7 k449_1_8
private theorem k449_1_10 : check w449 pick449 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k449_1_11 : check w449 pick449 1 t9790 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k449_1_12 : check w449 pick449 1 t9791 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w449 pick449 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t9790 k449_1_10 k449_1_11
private theorem k449_1_13 : check w449 pick449 1 t9792 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w449 pick449 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t9791 k449_1_9 k449_1_12
private theorem k449_1_14 : check w449 pick449 1 t9793 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w449 pick449 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9788 t9792 k449_1_6 k449_1_13
theorem cov449_1 : PA.Covered 1 (OZ.Valid 1 w449.low w449.t w449.y w449.r w449.cap) (P33.root 1) :=
  Night6836Tree.sound w449 pick449 1 t9793 _ k449_1_14
private theorem k449_2_0 : check w449 pick449 2 t9626 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k449_2_1 : check w449 pick449 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k449_2_2 : check w449 pick449 2 t9682 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w449 pick449 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9626 t9321 k449_2_0 k449_2_1
private theorem k449_2_3 : check w449 pick449 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k449_2_4 : check w449 pick449 2 t9794 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k449_2_5 : check w449 pick449 2 t9795 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w449 pick449 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t9794 k449_2_3 k449_2_4
private theorem k449_2_6 : check w449 pick449 2 t9796 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w449 pick449 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9682 t9795 k449_2_2 k449_2_5
theorem cov449_2 : PA.Covered 2 (OZ.Valid 2 w449.low w449.t w449.y w449.r w449.cap) (P33.root 2) :=
  Night6836Tree.sound w449 pick449 2 t9796 _ k449_2_6
theorem cov449_3 : PA.Covered 3 (OZ.Valid 3 w449.low w449.t w449.y w449.r w449.cap) (P33.root 3) :=
  Night6836Tree.sound w449 pick449 3 t564 _ (by decide +kernel)
theorem cov449_4 : PA.Covered 4 (OZ.Valid 4 w449.low w449.t w449.y w449.r w449.cap) (P33.root 4) :=
  Night6836Tree.sound w449 pick449 4 t565 _ (by decide +kernel)
theorem cov449_5 : PA.Covered 5 (OZ.Valid 5 w449.low w449.t w449.y w449.r w449.cap) (P33.root 5) :=
  Night6836Tree.sound w449 pick449 5 t566 _ (by decide +kernel)
theorem cov449_6 : PA.Covered 6 (OZ.Valid 6 w449.low w449.t w449.y w449.r w449.cap) (P33.root 6) :=
  Night6836Tree.sound w449 pick449 6 t567 _ (by decide +kernel)
theorem cov449_7 : PA.Covered 7 (OZ.Valid 7 w449.low w449.t w449.y w449.r w449.cap) (P33.root 7) :=
  Night6836Tree.sound w449 pick449 7 t2134 _ (by decide +kernel)
theorem window449 : P33.WindowCount w449 := by
  apply P33.window_count w449 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov449_1
  · exact cov449_2
  · exact cov449_3
  · exact cov449_4
  · exact cov449_5
  · exact cov449_6
  · exact cov449_7
end ProximityPrize.SubmissionLower.Night6836Bank
