/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT02
import ProximityPrize.SubmissionLower.Night6836SharedT04
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w600 : P33.Window := ⟨14,26,6806,6000,244805461207000328,0,50000,5000000,81920000000⟩
def h600_0 : Height w600 := ⟨0,50000,by decide +kernel⟩
def pick600 (cl : ℕ) : Height w600 := h600_0
private theorem k600_1_0 : check w600 pick600 1 t7465 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k600_1_1 : check w600 pick600 1 t12141 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k600_1_2 : check w600 pick600 1 t12142 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w600 pick600 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7465 t12141 k600_1_0 k600_1_1
private theorem k600_1_3 : check w600 pick600 1 t12154 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k600_1_4 : check w600 pick600 1 t12161 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k600_1_5 : check w600 pick600 1 t12162 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w600 pick600 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t12154 t12161 k600_1_3 k600_1_4
private theorem k600_1_6 : check w600 pick600 1 t12163 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w600 pick600 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t12142 t12162 k600_1_2 k600_1_5
private theorem k600_1_7 : check w600 pick600 1 t7179 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k600_1_8 : check w600 pick600 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k600_1_9 : check w600 pick600 1 t7180 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w600 pick600 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7179 t6872 k600_1_7 k600_1_8
private theorem k600_1_10 : check w600 pick600 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k600_1_11 : check w600 pick600 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k600_1_12 : check w600 pick600 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w600 pick600 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k600_1_10 k600_1_11
private theorem k600_1_13 : check w600 pick600 1 t7191 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w600 pick600 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7180 t7190 k600_1_9 k600_1_12
private theorem k600_1_14 : check w600 pick600 1 t12164 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w600 pick600 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t12163 t7191 k600_1_6 k600_1_13
theorem cov600_1 : PA.Covered 1 (OZ.Valid 1 w600.low w600.t w600.y w600.r w600.cap) (P33.root 1) :=
  Night6836Tree.sound w600 pick600 1 t12164 _ k600_1_14
private theorem k600_2_0 : check w600 pick600 2 t7548 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k600_2_1 : check w600 pick600 2 t8480 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k600_2_2 : check w600 pick600 2 t8481 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w600 pick600 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7548 t8480 k600_2_0 k600_2_1
theorem cov600_2 : PA.Covered 2 (OZ.Valid 2 w600.low w600.t w600.y w600.r w600.cap) (P33.root 2) :=
  Night6836Tree.sound w600 pick600 2 t8481 _ k600_2_2
theorem cov600_3 : PA.Covered 3 (OZ.Valid 3 w600.low w600.t w600.y w600.r w600.cap) (P33.root 3) :=
  Night6836Tree.sound w600 pick600 3 t564 _ (by decide +kernel)
theorem cov600_4 : PA.Covered 4 (OZ.Valid 4 w600.low w600.t w600.y w600.r w600.cap) (P33.root 4) :=
  Night6836Tree.sound w600 pick600 4 t565 _ (by decide +kernel)
theorem cov600_5 : PA.Covered 5 (OZ.Valid 5 w600.low w600.t w600.y w600.r w600.cap) (P33.root 5) :=
  Night6836Tree.sound w600 pick600 5 t566 _ (by decide +kernel)
theorem cov600_6 : PA.Covered 6 (OZ.Valid 6 w600.low w600.t w600.y w600.r w600.cap) (P33.root 6) :=
  Night6836Tree.sound w600 pick600 6 t567 _ (by decide +kernel)
theorem cov600_7 : PA.Covered 7 (OZ.Valid 7 w600.low w600.t w600.y w600.r w600.cap) (P33.root 7) :=
  Night6836Tree.sound w600 pick600 7 t568 _ (by decide +kernel)
theorem window600 : P33.WindowCount w600 := by
  apply P33.window_count w600 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov600_1
  · exact cov600_2
  · exact cov600_3
  · exact cov600_4
  · exact cov600_5
  · exact cov600_6
  · exact cov600_7
def w601 : P33.Window := ⟨8,46,7045,6400,244947040499406648,12498,50000,5000000,81920000000⟩
def h601_0 : Height w601 := ⟨12498,50000,by decide +kernel⟩
def pick601 (cl : ℕ) : Height w601 := h601_0
private theorem k601_1_0 : check w601 pick601 1 t12169 ⟨1,7,2,16,1,20,1,55⟩ = true := by decide +kernel
private theorem k601_1_1 : check w601 pick601 1 t12193 ⟨1,7,2,16,21,52,1,55⟩ = true := by decide +kernel
private theorem k601_1_2 : check w601 pick601 1 t12194 ⟨1,7,2,16,1,52,1,55⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,1,52,1,55⟩ 2 20 t12169 t12193 k601_1_0 k601_1_1
private theorem k601_1_3 : check w601 pick601 1 t12217 ⟨1,7,2,16,1,52,56,97⟩ = true := by decide +kernel
private theorem k601_1_4 : check w601 pick601 1 t12218 ⟨1,7,2,16,1,52,1,97⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,1,52,1,97⟩ 3 55 t12194 t12217 k601_1_2 k601_1_3
private theorem k601_1_5 : check w601 pick601 1 t12226 ⟨1,7,2,16,1,20,98,138⟩ = true := by decide +kernel
private theorem k601_1_6 : check w601 pick601 1 t12242 ⟨1,7,2,16,21,52,98,138⟩ = true := by decide +kernel
private theorem k601_1_7 : check w601 pick601 1 t12243 ⟨1,7,2,16,1,52,98,138⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,1,52,98,138⟩ 2 20 t12226 t12242 k601_1_5 k601_1_6
private theorem k601_1_8 : check w601 pick601 1 t10597 ⟨1,7,2,16,1,52,139,159⟩ = true := by decide +kernel
private theorem k601_1_9 : check w601 pick601 1 t12244 ⟨1,7,2,16,1,52,160,179⟩ = true := by decide +kernel
private theorem k601_1_10 : check w601 pick601 1 t12245 ⟨1,7,2,16,1,52,139,179⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,1,52,139,179⟩ 3 159 t10597 t12244 k601_1_8 k601_1_9
private theorem k601_1_11 : check w601 pick601 1 t12246 ⟨1,7,2,16,1,52,98,179⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,1,52,98,179⟩ 3 138 t12243 t12245 k601_1_7 k601_1_10
private theorem k601_1_12 : check w601 pick601 1 t12247 ⟨1,7,2,16,1,52,1,179⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,1,52,1,179⟩ 3 97 t12218 t12246 k601_1_4 k601_1_11
private theorem k601_1_13 : check w601 pick601 1 t12249 ⟨1,7,2,16,1,52,180,219⟩ = true := by decide +kernel
private theorem k601_1_14 : check w601 pick601 1 t12250 ⟨1,7,2,16,1,52,220,247⟩ = true := by decide +kernel
private theorem k601_1_15 : check w601 pick601 1 t12255 ⟨1,7,2,16,1,52,248,329⟩ = true := by decide +kernel
private theorem k601_1_16 : check w601 pick601 1 t12256 ⟨1,7,2,16,1,52,220,329⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,1,52,220,329⟩ 3 247 t12250 t12255 k601_1_14 k601_1_15
private theorem k601_1_17 : check w601 pick601 1 t12257 ⟨1,7,2,16,1,52,180,329⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,1,52,180,329⟩ 3 219 t12249 t12256 k601_1_13 k601_1_16
private theorem k601_1_18 : check w601 pick601 1 t12301 ⟨1,2,2,16,1,52,330,450⟩ = true := by decide +kernel
private theorem k601_1_19 : check w601 pick601 1 t12335 ⟨3,3,2,16,1,52,330,450⟩ = true := by decide +kernel
private theorem k601_1_20 : check w601 pick601 1 t12336 ⟨1,3,2,16,1,52,330,450⟩ = true := glue w601 pick601 1 ⟨1,3,2,16,1,52,330,450⟩ 0 2 t12301 t12335 k601_1_18 k601_1_19
private theorem k601_1_21 : check w601 pick601 1 t12412 ⟨4,7,2,16,1,52,330,450⟩ = true := by decide +kernel
private theorem k601_1_22 : check w601 pick601 1 t12413 ⟨1,7,2,16,1,52,330,450⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,1,52,330,450⟩ 0 3 t12336 t12412 k601_1_20 k601_1_21
private theorem k601_1_23 : check w601 pick601 1 t12414 ⟨1,7,2,16,1,52,180,450⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,1,52,180,450⟩ 3 329 t12257 t12413 k601_1_17 k601_1_22
private theorem k601_1_24 : check w601 pick601 1 t12415 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w601 pick601 1 ⟨1,7,2,16,0,52,0,450⟩ 3 179 t12247 t12414 k601_1_12 k601_1_23
theorem cov601_1 : PA.Covered 1 (OZ.Valid 1 w601.low w601.t w601.y w601.r w601.cap) (P33.root 1) :=
  Night6836Tree.sound w601 pick601 1 t12415 _ k601_1_24
private theorem k601_2_0 : check w601 pick601 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k601_2_1 : check w601 pick601 2 t10645 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k601_2_2 : check w601 pick601 2 t10646 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w601 pick601 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10645 k601_2_0 k601_2_1
private theorem k601_2_3 : check w601 pick601 2 t12420 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k601_2_4 : check w601 pick601 2 t1716 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k601_2_5 : check w601 pick601 2 t12421 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w601 pick601 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t12420 t1716 k601_2_3 k601_2_4
private theorem k601_2_6 : check w601 pick601 2 t12422 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w601 pick601 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10646 t12421 k601_2_2 k601_2_5
theorem cov601_2 : PA.Covered 2 (OZ.Valid 2 w601.low w601.t w601.y w601.r w601.cap) (P33.root 2) :=
  Night6836Tree.sound w601 pick601 2 t12422 _ k601_2_6
theorem cov601_3 : PA.Covered 3 (OZ.Valid 3 w601.low w601.t w601.y w601.r w601.cap) (P33.root 3) :=
  Night6836Tree.sound w601 pick601 3 t564 _ (by decide +kernel)
theorem cov601_4 : PA.Covered 4 (OZ.Valid 4 w601.low w601.t w601.y w601.r w601.cap) (P33.root 4) :=
  Night6836Tree.sound w601 pick601 4 t565 _ (by decide +kernel)
theorem cov601_5 : PA.Covered 5 (OZ.Valid 5 w601.low w601.t w601.y w601.r w601.cap) (P33.root 5) :=
  Night6836Tree.sound w601 pick601 5 t566 _ (by decide +kernel)
theorem cov601_6 : PA.Covered 6 (OZ.Valid 6 w601.low w601.t w601.y w601.r w601.cap) (P33.root 6) :=
  Night6836Tree.sound w601 pick601 6 t567 _ (by decide +kernel)
theorem cov601_7 : PA.Covered 7 (OZ.Valid 7 w601.low w601.t w601.y w601.r w601.cap) (P33.root 7) :=
  Night6836Tree.sound w601 pick601 7 t568 _ (by decide +kernel)
theorem window601 : P33.WindowCount w601 := by
  apply P33.window_count w601 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov601_1
  · exact cov601_2
  · exact cov601_3
  · exact cov601_4
  · exact cov601_5
  · exact cov601_6
  · exact cov601_7
def w602 : P33.Window := ⟨9,44,6975,6200,244970337719790677,12262,50000,5000000,81920000000⟩
def h602_0 : Height w602 := ⟨12262,50000,by decide +kernel⟩
def pick602 (cl : ℕ) : Height w602 := h602_0
private theorem k602_1_0 : check w602 pick602 1 t12425 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k602_1_1 : check w602 pick602 1 t12433 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k602_1_2 : check w602 pick602 1 t12434 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t12425 t12433 k602_1_0 k602_1_1
private theorem k602_1_3 : check w602 pick602 1 t12444 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k602_1_4 : check w602 pick602 1 t12463 ⟨1,7,2,16,1,52,98,124⟩ = true := by decide +kernel
private theorem k602_1_5 : check w602 pick602 1 t12464 ⟨1,7,2,16,1,52,70,124⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,1,52,70,124⟩ 3 97 t12444 t12463 k602_1_3 k602_1_4
private theorem k602_1_6 : check w602 pick602 1 t12465 ⟨1,7,2,16,1,52,1,124⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,1,52,1,124⟩ 3 69 t12434 t12464 k602_1_2 k602_1_5
private theorem k602_1_7 : check w602 pick602 1 t12471 ⟨1,7,2,16,1,52,125,159⟩ = true := by decide +kernel
private theorem k602_1_8 : check w602 pick602 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k602_1_9 : check w602 pick602 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k602_1_10 : check w602 pick602 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k602_1_8 k602_1_9
private theorem k602_1_11 : check w602 pick602 1 t12472 ⟨1,7,2,16,1,52,125,192⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,1,52,125,192⟩ 3 159 t12471 t4432 k602_1_7 k602_1_10
private theorem k602_1_12 : check w602 pick602 1 t12496 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k602_1_13 : check w602 pick602 1 t12508 ⟨1,7,2,16,1,52,234,329⟩ = true := by decide +kernel
private theorem k602_1_14 : check w602 pick602 1 t12509 ⟨1,7,2,16,1,52,193,329⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,1,52,193,329⟩ 3 233 t12496 t12508 k602_1_12 k602_1_13
private theorem k602_1_15 : check w602 pick602 1 t12510 ⟨1,7,2,16,1,52,125,329⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,1,52,125,329⟩ 3 192 t12472 t12509 k602_1_11 k602_1_14
private theorem k602_1_16 : check w602 pick602 1 t12511 ⟨1,7,2,16,1,52,1,329⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,1,52,1,329⟩ 3 124 t12465 t12510 k602_1_6 k602_1_15
private theorem k602_1_17 : check w602 pick602 1 t12546 ⟨1,2,2,13,1,47,330,450⟩ = true := by decide +kernel
private theorem k602_1_18 : check w602 pick602 1 t12586 ⟨3,6,2,13,1,47,330,450⟩ = true := by decide +kernel
private theorem k602_1_19 : check w602 pick602 1 t12587 ⟨1,7,2,13,1,47,330,450⟩ = true := glue w602 pick602 1 ⟨1,7,2,13,1,47,330,450⟩ 0 2 t12546 t12586 k602_1_17 k602_1_18
private theorem k602_1_20 : check w602 pick602 1 t12668 ⟨1,3,14,16,7,47,330,450⟩ = true := by decide +kernel
private theorem k602_1_21 : check w602 pick602 1 t12701 ⟨4,7,14,16,7,44,330,450⟩ = true := by decide +kernel
private theorem k602_1_22 : check w602 pick602 1 t12747 ⟨4,7,14,16,45,47,330,450⟩ = true := by decide +kernel
private theorem k602_1_23 : check w602 pick602 1 t12748 ⟨4,7,14,16,7,47,330,450⟩ = true := glue w602 pick602 1 ⟨4,7,14,16,7,47,330,450⟩ 2 44 t12701 t12747 k602_1_21 k602_1_22
private theorem k602_1_24 : check w602 pick602 1 t12749 ⟨1,7,14,16,1,47,330,450⟩ = true := glue w602 pick602 1 ⟨1,7,14,16,1,47,330,450⟩ 0 3 t12668 t12748 k602_1_20 k602_1_23
private theorem k602_1_25 : check w602 pick602 1 t12750 ⟨1,7,2,16,1,47,330,450⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,1,47,330,450⟩ 1 13 t12587 t12749 k602_1_19 k602_1_24
private theorem k602_1_26 : check w602 pick602 1 t12795 ⟨1,2,2,13,48,52,330,450⟩ = true := by decide +kernel
private theorem k602_1_27 : check w602 pick602 1 t12826 ⟨3,6,2,13,48,52,330,450⟩ = true := by decide +kernel
private theorem k602_1_28 : check w602 pick602 1 t12827 ⟨1,7,2,13,48,52,330,450⟩ = true := glue w602 pick602 1 ⟨1,7,2,13,48,52,330,450⟩ 0 2 t12795 t12826 k602_1_26 k602_1_27
private theorem k602_1_29 : check w602 pick602 1 t12870 ⟨1,7,14,16,48,49,330,450⟩ = true := by decide +kernel
private theorem k602_1_30 : check w602 pick602 1 t12932 ⟨1,7,14,16,50,52,330,450⟩ = true := by decide +kernel
private theorem k602_1_31 : check w602 pick602 1 t12933 ⟨1,7,14,16,48,52,330,450⟩ = true := glue w602 pick602 1 ⟨1,7,14,16,48,52,330,450⟩ 2 49 t12870 t12932 k602_1_29 k602_1_30
private theorem k602_1_32 : check w602 pick602 1 t12934 ⟨1,7,2,16,48,52,330,450⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,48,52,330,450⟩ 1 13 t12827 t12933 k602_1_28 k602_1_31
private theorem k602_1_33 : check w602 pick602 1 t12935 ⟨1,7,2,16,1,52,330,450⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,1,52,330,450⟩ 2 47 t12750 t12934 k602_1_25 k602_1_32
private theorem k602_1_34 : check w602 pick602 1 t12936 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w602 pick602 1 ⟨1,7,2,16,0,52,0,450⟩ 3 329 t12511 t12935 k602_1_16 k602_1_33
theorem cov602_1 : PA.Covered 1 (OZ.Valid 1 w602.low w602.t w602.y w602.r w602.cap) (P33.root 1) :=
  Night6836Tree.sound w602 pick602 1 t12936 _ k602_1_34
private theorem k602_2_0 : check w602 pick602 2 t4930 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k602_2_1 : check w602 pick602 2 t4937 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k602_2_2 : check w602 pick602 2 t4938 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w602 pick602 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4930 t4937 k602_2_0 k602_2_1
private theorem k602_2_3 : check w602 pick602 2 t12942 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k602_2_4 : check w602 pick602 2 t6346 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k602_2_5 : check w602 pick602 2 t12943 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w602 pick602 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t12942 t6346 k602_2_3 k602_2_4
private theorem k602_2_6 : check w602 pick602 2 t12944 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w602 pick602 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4938 t12943 k602_2_2 k602_2_5
theorem cov602_2 : PA.Covered 2 (OZ.Valid 2 w602.low w602.t w602.y w602.r w602.cap) (P33.root 2) :=
  Night6836Tree.sound w602 pick602 2 t12944 _ k602_2_6
theorem cov602_3 : PA.Covered 3 (OZ.Valid 3 w602.low w602.t w602.y w602.r w602.cap) (P33.root 3) :=
  Night6836Tree.sound w602 pick602 3 t4151 _ (by decide +kernel)
theorem cov602_4 : PA.Covered 4 (OZ.Valid 4 w602.low w602.t w602.y w602.r w602.cap) (P33.root 4) :=
  Night6836Tree.sound w602 pick602 4 t565 _ (by decide +kernel)
theorem cov602_5 : PA.Covered 5 (OZ.Valid 5 w602.low w602.t w602.y w602.r w602.cap) (P33.root 5) :=
  Night6836Tree.sound w602 pick602 5 t566 _ (by decide +kernel)
theorem cov602_6 : PA.Covered 6 (OZ.Valid 6 w602.low w602.t w602.y w602.r w602.cap) (P33.root 6) :=
  Night6836Tree.sound w602 pick602 6 t567 _ (by decide +kernel)
theorem cov602_7 : PA.Covered 7 (OZ.Valid 7 w602.low w602.t w602.y w602.r w602.cap) (P33.root 7) :=
  Night6836Tree.sound w602 pick602 7 t568 _ (by decide +kernel)
theorem window602 : P33.WindowCount w602 := by
  apply P33.window_count w602 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov602_1
  · exact cov602_2
  · exact cov602_3
  · exact cov602_4
  · exact cov602_5
  · exact cov602_6
  · exact cov602_7
end ProximityPrize.SubmissionLower.Night6836Bank
