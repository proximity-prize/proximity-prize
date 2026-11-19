/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT02
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w180 : P33.Window := ⟨12,33,6949,6898,246369626453325621,18677,24000,5000000,81920000000⟩
def h180_0 : Height w180 := ⟨18677,24000,by decide +kernel⟩
def h180_1 : Height w180 := ⟨22873,21000,by decide +kernel⟩
def h180_2 : Height w180 := ⟨28795,18000,by decide +kernel⟩
def h180_3 : Height w180 := ⟨38876,15000,by decide +kernel⟩
def pick180 (cl : ℕ) : Height w180 := if cl<36 then (if cl<4 then (h180_0) else (h180_1)) else (if cl<524 then (h180_2) else (h180_3))
private theorem k180_1_0 : check w180 pick180 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k180_1_1 : check w180 pick180 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k180_1_2 : check w180 pick180 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w180 pick180 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k180_1_0 k180_1_1
private theorem k180_1_3 : check w180 pick180 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k180_1_4 : check w180 pick180 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k180_1_5 : check w180 pick180 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w180 pick180 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k180_1_3 k180_1_4
private theorem k180_1_6 : check w180 pick180 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w180 pick180 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k180_1_2 k180_1_5
private theorem k180_1_7 : check w180 pick180 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k180_1_8 : check w180 pick180 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k180_1_9 : check w180 pick180 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w180 pick180 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k180_1_7 k180_1_8
private theorem k180_1_10 : check w180 pick180 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k180_1_11 : check w180 pick180 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k180_1_12 : check w180 pick180 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w180 pick180 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k180_1_10 k180_1_11
private theorem k180_1_13 : check w180 pick180 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w180 pick180 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k180_1_9 k180_1_12
private theorem k180_1_14 : check w180 pick180 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w180 pick180 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k180_1_6 k180_1_13
theorem cov180_1 : PA.Covered 1 (OZ.Valid 1 w180.low w180.t w180.y w180.r w180.cap) (P33.root 1) :=
  Night6836Tree.sound w180 pick180 1 t7674 _ k180_1_14
private theorem k180_2_0 : check w180 pick180 2 t5616 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k180_2_1 : check w180 pick180 2 t7677 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k180_2_2 : check w180 pick180 2 t7678 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w180 pick180 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t5616 t7677 k180_2_0 k180_2_1
private theorem k180_2_3 : check w180 pick180 2 t7680 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k180_2_4 : check w180 pick180 2 t7681 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w180 pick180 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t7678 t7680 k180_2_2 k180_2_3
theorem cov180_2 : PA.Covered 2 (OZ.Valid 2 w180.low w180.t w180.y w180.r w180.cap) (P33.root 2) :=
  Night6836Tree.sound w180 pick180 2 t7681 _ k180_2_4
theorem cov180_3 : PA.Covered 3 (OZ.Valid 3 w180.low w180.t w180.y w180.r w180.cap) (P33.root 3) :=
  Night6836Tree.sound w180 pick180 3 t564 _ (by decide +kernel)
theorem cov180_4 : PA.Covered 4 (OZ.Valid 4 w180.low w180.t w180.y w180.r w180.cap) (P33.root 4) :=
  Night6836Tree.sound w180 pick180 4 t565 _ (by decide +kernel)
theorem cov180_5 : PA.Covered 5 (OZ.Valid 5 w180.low w180.t w180.y w180.r w180.cap) (P33.root 5) :=
  Night6836Tree.sound w180 pick180 5 t566 _ (by decide +kernel)
theorem cov180_6 : PA.Covered 6 (OZ.Valid 6 w180.low w180.t w180.y w180.r w180.cap) (P33.root 6) :=
  Night6836Tree.sound w180 pick180 6 t567 _ (by decide +kernel)
theorem cov180_7 : PA.Covered 7 (OZ.Valid 7 w180.low w180.t w180.y w180.r w180.cap) (P33.root 7) :=
  Night6836Tree.sound w180 pick180 7 t568 _ (by decide +kernel)
theorem window180 : P33.WindowCount w180 := by
  apply P33.window_count w180 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov180_1
  · exact cov180_2
  · exact cov180_3
  · exact cov180_4
  · exact cov180_5
  · exact cov180_6
  · exact cov180_7
def w181 : P33.Window := ⟨12,34,4533,3534,203687461042432693,38435,47000,5000000,81920000000⟩
def h181_0 : Height w181 := ⟨38435,47000,by decide +kernel⟩
def h181_1 : Height w181 := ⟨43837,43000,by decide +kernel⟩
def h181_2 : Height w181 := ⟨50461,39000,by decide +kernel⟩
def h181_3 : Height w181 := ⟨59107,35000,by decide +kernel⟩
def h181_4 : Height w181 := ⟨71464,31000,by decide +kernel⟩
def pick181 (cl : ℕ) : Height w181 := if cl<13 then (if cl<2 then (h181_0) else (h181_1)) else (if cl<62 then (h181_2) else (if cl<299 then (h181_3) else (h181_4)))
private theorem k181_1_0 : check w181 pick181 1 t7686 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k181_1_1 : check w181 pick181 1 t2318 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k181_1_2 : check w181 pick181 1 t7687 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w181 pick181 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7686 t2318 k181_1_0 k181_1_1
private theorem k181_1_3 : check w181 pick181 1 t7692 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k181_1_4 : check w181 pick181 1 t7694 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k181_1_5 : check w181 pick181 1 t7695 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w181 pick181 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t7692 t7694 k181_1_3 k181_1_4
private theorem k181_1_6 : check w181 pick181 1 t7696 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w181 pick181 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t7687 t7695 k181_1_2 k181_1_5
private theorem k181_1_7 : check w181 pick181 1 t7701 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k181_1_8 : check w181 pick181 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k181_1_9 : check w181 pick181 1 t7703 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w181 pick181 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7701 t7702 k181_1_7 k181_1_8
private theorem k181_1_10 : check w181 pick181 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k181_1_11 : check w181 pick181 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k181_1_12 : check w181 pick181 1 t7319 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w181 pick181 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t7318 k181_1_10 k181_1_11
private theorem k181_1_13 : check w181 pick181 1 t7704 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w181 pick181 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7703 t7319 k181_1_9 k181_1_12
private theorem k181_1_14 : check w181 pick181 1 t7705 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w181 pick181 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7696 t7704 k181_1_6 k181_1_13
theorem cov181_1 : PA.Covered 1 (OZ.Valid 1 w181.low w181.t w181.y w181.r w181.cap) (P33.root 1) :=
  Night6836Tree.sound w181 pick181 1 t7705 _ k181_1_14
theorem cov181_2 : PA.Covered 2 (OZ.Valid 2 w181.low w181.t w181.y w181.r w181.cap) (P33.root 2) :=
  Night6836Tree.sound w181 pick181 2 t7712 _ (by decide +kernel)
theorem cov181_3 : PA.Covered 3 (OZ.Valid 3 w181.low w181.t w181.y w181.r w181.cap) (P33.root 3) :=
  Night6836Tree.sound w181 pick181 3 t564 _ (by decide +kernel)
theorem cov181_4 : PA.Covered 4 (OZ.Valid 4 w181.low w181.t w181.y w181.r w181.cap) (P33.root 4) :=
  Night6836Tree.sound w181 pick181 4 t565 _ (by decide +kernel)
theorem cov181_5 : PA.Covered 5 (OZ.Valid 5 w181.low w181.t w181.y w181.r w181.cap) (P33.root 5) :=
  Night6836Tree.sound w181 pick181 5 t566 _ (by decide +kernel)
theorem cov181_6 : PA.Covered 6 (OZ.Valid 6 w181.low w181.t w181.y w181.r w181.cap) (P33.root 6) :=
  Night6836Tree.sound w181 pick181 6 t567 _ (by decide +kernel)
theorem cov181_7 : PA.Covered 7 (OZ.Valid 7 w181.low w181.t w181.y w181.r w181.cap) (P33.root 7) :=
  Night6836Tree.sound w181 pick181 7 t2134 _ (by decide +kernel)
theorem window181 : P33.WindowCount w181 := by
  apply P33.window_count w181 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov181_1
  · exact cov181_2
  · exact cov181_3
  · exact cov181_4
  · exact cov181_5
  · exact cov181_6
  · exact cov181_7
def w182 : P33.Window := ⟨12,34,6897,6847,245485911340065417,20184,24000,5000000,81920000000⟩
def h182_0 : Height w182 := ⟨20184,24000,by decide +kernel⟩
def h182_1 : Height w182 := ⟨24547,21000,by decide +kernel⟩
def h182_2 : Height w182 := ⟨30756,18000,by decide +kernel⟩
def h182_3 : Height w182 := ⟨41434,15000,by decide +kernel⟩
def pick182 (cl : ℕ) : Height w182 := if cl<44 then (if cl<5 then (h182_0) else (h182_1)) else (if cl<853 then (h182_2) else (h182_3))
private theorem k182_1_0 : check w182 pick182 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k182_1_1 : check w182 pick182 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k182_1_2 : check w182 pick182 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w182 pick182 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k182_1_0 k182_1_1
private theorem k182_1_3 : check w182 pick182 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k182_1_4 : check w182 pick182 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k182_1_5 : check w182 pick182 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w182 pick182 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k182_1_3 k182_1_4
private theorem k182_1_6 : check w182 pick182 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w182 pick182 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k182_1_2 k182_1_5
private theorem k182_1_7 : check w182 pick182 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k182_1_8 : check w182 pick182 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k182_1_9 : check w182 pick182 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w182 pick182 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k182_1_7 k182_1_8
private theorem k182_1_10 : check w182 pick182 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k182_1_11 : check w182 pick182 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k182_1_12 : check w182 pick182 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w182 pick182 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k182_1_10 k182_1_11
private theorem k182_1_13 : check w182 pick182 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w182 pick182 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k182_1_9 k182_1_12
private theorem k182_1_14 : check w182 pick182 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w182 pick182 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k182_1_6 k182_1_13
theorem cov182_1 : PA.Covered 1 (OZ.Valid 1 w182.low w182.t w182.y w182.r w182.cap) (P33.root 1) :=
  Night6836Tree.sound w182 pick182 1 t7674 _ k182_1_14
private theorem k182_2_0 : check w182 pick182 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k182_2_1 : check w182 pick182 2 t5723 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k182_2_2 : check w182 pick182 2 t5724 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w182 pick182 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5723 k182_2_0 k182_2_1
private theorem k182_2_3 : check w182 pick182 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k182_2_4 : check w182 pick182 2 t3530 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k182_2_5 : check w182 pick182 2 t3531 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w182 pick182 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t3530 k182_2_3 k182_2_4
private theorem k182_2_6 : check w182 pick182 2 t5725 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w182 pick182 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5724 t3531 k182_2_2 k182_2_5
theorem cov182_2 : PA.Covered 2 (OZ.Valid 2 w182.low w182.t w182.y w182.r w182.cap) (P33.root 2) :=
  Night6836Tree.sound w182 pick182 2 t5725 _ k182_2_6
theorem cov182_3 : PA.Covered 3 (OZ.Valid 3 w182.low w182.t w182.y w182.r w182.cap) (P33.root 3) :=
  Night6836Tree.sound w182 pick182 3 t564 _ (by decide +kernel)
theorem cov182_4 : PA.Covered 4 (OZ.Valid 4 w182.low w182.t w182.y w182.r w182.cap) (P33.root 4) :=
  Night6836Tree.sound w182 pick182 4 t565 _ (by decide +kernel)
theorem cov182_5 : PA.Covered 5 (OZ.Valid 5 w182.low w182.t w182.y w182.r w182.cap) (P33.root 5) :=
  Night6836Tree.sound w182 pick182 5 t566 _ (by decide +kernel)
theorem cov182_6 : PA.Covered 6 (OZ.Valid 6 w182.low w182.t w182.y w182.r w182.cap) (P33.root 6) :=
  Night6836Tree.sound w182 pick182 6 t567 _ (by decide +kernel)
theorem cov182_7 : PA.Covered 7 (OZ.Valid 7 w182.low w182.t w182.y w182.r w182.cap) (P33.root 7) :=
  Night6836Tree.sound w182 pick182 7 t568 _ (by decide +kernel)
theorem window182 : P33.WindowCount w182 := by
  apply P33.window_count w182 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov182_1
  · exact cov182_2
  · exact cov182_3
  · exact cov182_4
  · exact cov182_5
  · exact cov182_6
  · exact cov182_7
def w183 : P33.Window := ⟨12,36,6172,5223,245091382767871490,27516,33000,5000000,81920000000⟩
def h183_0 : Height w183 := ⟨27516,33000,by decide +kernel⟩
def h183_1 : Height w183 := ⟨31480,30000,by decide +kernel⟩
def h183_2 : Height w183 := ⟨36390,27000,by decide +kernel⟩
def h183_3 : Height w183 := ⟨42918,24000,by decide +kernel⟩
def h183_4 : Height w183 := ⟨52569,21000,by decide +kernel⟩
def pick183 (cl : ℕ) : Height w183 := if cl<12 then (if cl<2 then (h183_0) else (h183_1)) else (if cl<62 then (h183_2) else (if cl<347 then (h183_3) else (h183_4)))
private theorem k183_1_0 : check w183 pick183 1 t7551 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k183_1_1 : check w183 pick183 1 t7555 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k183_1_2 : check w183 pick183 1 t7556 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w183 pick183 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7551 t7555 k183_1_0 k183_1_1
private theorem k183_1_3 : check w183 pick183 1 t7559 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k183_1_4 : check w183 pick183 1 t7482 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k183_1_5 : check w183 pick183 1 t7560 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w183 pick183 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7559 t7482 k183_1_3 k183_1_4
private theorem k183_1_6 : check w183 pick183 1 t7561 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w183 pick183 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7556 t7560 k183_1_2 k183_1_5
private theorem k183_1_7 : check w183 pick183 1 t7713 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k183_1_8 : check w183 pick183 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k183_1_9 : check w183 pick183 1 t7714 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w183 pick183 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7713 t7641 k183_1_7 k183_1_8
private theorem k183_1_10 : check w183 pick183 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k183_1_11 : check w183 pick183 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k183_1_12 : check w183 pick183 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w183 pick183 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k183_1_10 k183_1_11
private theorem k183_1_13 : check w183 pick183 1 t7715 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w183 pick183 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7714 t7648 k183_1_9 k183_1_12
private theorem k183_1_14 : check w183 pick183 1 t7716 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w183 pick183 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7561 t7715 k183_1_6 k183_1_13
theorem cov183_1 : PA.Covered 1 (OZ.Valid 1 w183.low w183.t w183.y w183.r w183.cap) (P33.root 1) :=
  Night6836Tree.sound w183 pick183 1 t7716 _ k183_1_14
private theorem k183_2_0 : check w183 pick183 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k183_2_1 : check w183 pick183 2 t5541 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k183_2_2 : check w183 pick183 2 t5542 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w183 pick183 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t5541 k183_2_0 k183_2_1
theorem cov183_2 : PA.Covered 2 (OZ.Valid 2 w183.low w183.t w183.y w183.r w183.cap) (P33.root 2) :=
  Night6836Tree.sound w183 pick183 2 t5542 _ k183_2_2
theorem cov183_3 : PA.Covered 3 (OZ.Valid 3 w183.low w183.t w183.y w183.r w183.cap) (P33.root 3) :=
  Night6836Tree.sound w183 pick183 3 t564 _ (by decide +kernel)
theorem cov183_4 : PA.Covered 4 (OZ.Valid 4 w183.low w183.t w183.y w183.r w183.cap) (P33.root 4) :=
  Night6836Tree.sound w183 pick183 4 t565 _ (by decide +kernel)
theorem cov183_5 : PA.Covered 5 (OZ.Valid 5 w183.low w183.t w183.y w183.r w183.cap) (P33.root 5) :=
  Night6836Tree.sound w183 pick183 5 t566 _ (by decide +kernel)
theorem cov183_6 : PA.Covered 6 (OZ.Valid 6 w183.low w183.t w183.y w183.r w183.cap) (P33.root 6) :=
  Night6836Tree.sound w183 pick183 6 t567 _ (by decide +kernel)
theorem cov183_7 : PA.Covered 7 (OZ.Valid 7 w183.low w183.t w183.y w183.r w183.cap) (P33.root 7) :=
  Night6836Tree.sound w183 pick183 7 t2134 _ (by decide +kernel)
theorem window183 : P33.WindowCount w183 := by
  apply P33.window_count w183 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov183_1
  · exact cov183_2
  · exact cov183_3
  · exact cov183_4
  · exact cov183_5
  · exact cov183_6
  · exact cov183_7
def w184 : P33.Window := ⟨12,36,6791,6207,245212060325600468,24112,27000,5000000,81920000000⟩
def h184_0 : Height w184 := ⟨24112,27000,by decide +kernel⟩
def h184_1 : Height w184 := ⟨28410,24000,by decide +kernel⟩
def h184_2 : Height w184 := ⟨34179,21000,by decide +kernel⟩
def h184_3 : Height w184 := ⟨42985,18000,by decide +kernel⟩
def h184_4 : Height w184 := ⟨59818,15000,by decide +kernel⟩
def pick184 (cl : ℕ) : Height w184 := if cl<32 then (if cl<4 then (h184_0) else (h184_1)) else (if cl<266 then (h184_2) else (if cl<1021 then (h184_3) else (h184_4)))
private theorem k184_1_0 : check w184 pick184 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k184_1_1 : check w184 pick184 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k184_1_2 : check w184 pick184 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w184 pick184 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k184_1_0 k184_1_1
private theorem k184_1_3 : check w184 pick184 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k184_1_4 : check w184 pick184 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k184_1_5 : check w184 pick184 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w184 pick184 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k184_1_3 k184_1_4
private theorem k184_1_6 : check w184 pick184 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w184 pick184 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k184_1_2 k184_1_5
private theorem k184_1_7 : check w184 pick184 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k184_1_8 : check w184 pick184 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k184_1_9 : check w184 pick184 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w184 pick184 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k184_1_7 k184_1_8
private theorem k184_1_10 : check w184 pick184 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k184_1_11 : check w184 pick184 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k184_1_12 : check w184 pick184 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w184 pick184 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k184_1_10 k184_1_11
private theorem k184_1_13 : check w184 pick184 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w184 pick184 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k184_1_9 k184_1_12
private theorem k184_1_14 : check w184 pick184 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w184 pick184 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k184_1_6 k184_1_13
theorem cov184_1 : PA.Covered 1 (OZ.Valid 1 w184.low w184.t w184.y w184.r w184.cap) (P33.root 1) :=
  Night6836Tree.sound w184 pick184 1 t7674 _ k184_1_14
private theorem k184_2_0 : check w184 pick184 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k184_2_1 : check w184 pick184 2 t5723 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k184_2_2 : check w184 pick184 2 t5724 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w184 pick184 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5723 k184_2_0 k184_2_1
private theorem k184_2_3 : check w184 pick184 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k184_2_4 : check w184 pick184 2 t7719 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k184_2_5 : check w184 pick184 2 t7720 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w184 pick184 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t7719 k184_2_3 k184_2_4
private theorem k184_2_6 : check w184 pick184 2 t7721 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w184 pick184 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5724 t7720 k184_2_2 k184_2_5
theorem cov184_2 : PA.Covered 2 (OZ.Valid 2 w184.low w184.t w184.y w184.r w184.cap) (P33.root 2) :=
  Night6836Tree.sound w184 pick184 2 t7721 _ k184_2_6
theorem cov184_3 : PA.Covered 3 (OZ.Valid 3 w184.low w184.t w184.y w184.r w184.cap) (P33.root 3) :=
  Night6836Tree.sound w184 pick184 3 t4151 _ (by decide +kernel)
theorem cov184_4 : PA.Covered 4 (OZ.Valid 4 w184.low w184.t w184.y w184.r w184.cap) (P33.root 4) :=
  Night6836Tree.sound w184 pick184 4 t565 _ (by decide +kernel)
theorem cov184_5 : PA.Covered 5 (OZ.Valid 5 w184.low w184.t w184.y w184.r w184.cap) (P33.root 5) :=
  Night6836Tree.sound w184 pick184 5 t566 _ (by decide +kernel)
theorem cov184_6 : PA.Covered 6 (OZ.Valid 6 w184.low w184.t w184.y w184.r w184.cap) (P33.root 6) :=
  Night6836Tree.sound w184 pick184 6 t567 _ (by decide +kernel)
theorem cov184_7 : PA.Covered 7 (OZ.Valid 7 w184.low w184.t w184.y w184.r w184.cap) (P33.root 7) :=
  Night6836Tree.sound w184 pick184 7 t568 _ (by decide +kernel)
theorem window184 : P33.WindowCount w184 := by
  apply P33.window_count w184 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov184_1
  · exact cov184_2
  · exact cov184_3
  · exact cov184_4
  · exact cov184_5
  · exact cov184_6
  · exact cov184_7
def w185 : P33.Window := ⟨12,37,5148,4199,242276541050233410,38673,39000,5000000,81920000000⟩
def h185_0 : Height w185 := ⟨38673,39000,by decide +kernel⟩
def h185_1 : Height w185 := ⟨43087,36000,by decide +kernel⟩
def h185_2 : Height w185 := ⟨48425,33000,by decide +kernel⟩
def h185_3 : Height w185 := ⟨55210,30000,by decide +kernel⟩
def h185_4 : Height w185 := ⟨64444,27000,by decide +kernel⟩
def pick185 (cl : ℕ) : Height w185 := if cl<32 then (if cl<5 then (h185_0) else (h185_1)) else (if cl<83 then (h185_2) else (if cl<302 then (h185_3) else (h185_4)))
private theorem k185_1_0 : check w185 pick185 1 t7724 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k185_1_1 : check w185 pick185 1 t7727 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k185_1_2 : check w185 pick185 1 t7728 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w185 pick185 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7724 t7727 k185_1_0 k185_1_1
private theorem k185_1_3 : check w185 pick185 1 t7732 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k185_1_4 : check w185 pick185 1 t7403 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k185_1_5 : check w185 pick185 1 t7733 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w185 pick185 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7732 t7403 k185_1_3 k185_1_4
private theorem k185_1_6 : check w185 pick185 1 t7734 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w185 pick185 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7728 t7733 k185_1_2 k185_1_5
private theorem k185_1_7 : check w185 pick185 1 t7701 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k185_1_8 : check w185 pick185 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k185_1_9 : check w185 pick185 1 t7703 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w185 pick185 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7701 t7702 k185_1_7 k185_1_8
private theorem k185_1_10 : check w185 pick185 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k185_1_11 : check w185 pick185 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k185_1_12 : check w185 pick185 1 t7319 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w185 pick185 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t7318 k185_1_10 k185_1_11
private theorem k185_1_13 : check w185 pick185 1 t7704 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w185 pick185 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7703 t7319 k185_1_9 k185_1_12
private theorem k185_1_14 : check w185 pick185 1 t7735 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w185 pick185 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7734 t7704 k185_1_6 k185_1_13
theorem cov185_1 : PA.Covered 1 (OZ.Valid 1 w185.low w185.t w185.y w185.r w185.cap) (P33.root 1) :=
  Night6836Tree.sound w185 pick185 1 t7735 _ k185_1_14
theorem cov185_2 : PA.Covered 2 (OZ.Valid 2 w185.low w185.t w185.y w185.r w185.cap) (P33.root 2) :=
  Night6836Tree.sound w185 pick185 2 t5320 _ (by decide +kernel)
theorem cov185_3 : PA.Covered 3 (OZ.Valid 3 w185.low w185.t w185.y w185.r w185.cap) (P33.root 3) :=
  Night6836Tree.sound w185 pick185 3 t564 _ (by decide +kernel)
theorem cov185_4 : PA.Covered 4 (OZ.Valid 4 w185.low w185.t w185.y w185.r w185.cap) (P33.root 4) :=
  Night6836Tree.sound w185 pick185 4 t565 _ (by decide +kernel)
theorem cov185_5 : PA.Covered 5 (OZ.Valid 5 w185.low w185.t w185.y w185.r w185.cap) (P33.root 5) :=
  Night6836Tree.sound w185 pick185 5 t566 _ (by decide +kernel)
theorem cov185_6 : PA.Covered 6 (OZ.Valid 6 w185.low w185.t w185.y w185.r w185.cap) (P33.root 6) :=
  Night6836Tree.sound w185 pick185 6 t567 _ (by decide +kernel)
theorem cov185_7 : PA.Covered 7 (OZ.Valid 7 w185.low w185.t w185.y w185.r w185.cap) (P33.root 7) :=
  Night6836Tree.sound w185 pick185 7 t2134 _ (by decide +kernel)
theorem window185 : P33.WindowCount w185 := by
  apply P33.window_count w185 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov185_1
  · exact cov185_2
  · exact cov185_3
  · exact cov185_4
  · exact cov185_5
  · exact cov185_6
  · exact cov185_7
def w186 : P33.Window := ⟨12,37,6732,6456,246641969103629915,23083,27000,5000000,81920000000⟩
def h186_0 : Height w186 := ⟨23083,27000,by decide +kernel⟩
def h186_1 : Height w186 := ⟨27135,24000,by decide +kernel⟩
def h186_2 : Height w186 := ⟨32486,21000,by decide +kernel⟩
def h186_3 : Height w186 := ⟨40463,18000,by decide +kernel⟩
def h186_4 : Height w186 := ⟨55117,15000,by decide +kernel⟩
def pick186 (cl : ℕ) : Height w186 := if cl<25 then (if cl<2 then (h186_0) else (h186_1)) else (if cl<180 then (h186_2) else (if cl<997 then (h186_3) else (h186_4)))
private theorem k186_1_0 : check w186 pick186 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k186_1_1 : check w186 pick186 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k186_1_2 : check w186 pick186 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w186 pick186 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k186_1_0 k186_1_1
private theorem k186_1_3 : check w186 pick186 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k186_1_4 : check w186 pick186 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k186_1_5 : check w186 pick186 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w186 pick186 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k186_1_3 k186_1_4
private theorem k186_1_6 : check w186 pick186 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w186 pick186 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k186_1_2 k186_1_5
private theorem k186_1_7 : check w186 pick186 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k186_1_8 : check w186 pick186 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k186_1_9 : check w186 pick186 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w186 pick186 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k186_1_7 k186_1_8
private theorem k186_1_10 : check w186 pick186 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k186_1_11 : check w186 pick186 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k186_1_12 : check w186 pick186 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w186 pick186 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k186_1_10 k186_1_11
private theorem k186_1_13 : check w186 pick186 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w186 pick186 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k186_1_9 k186_1_12
private theorem k186_1_14 : check w186 pick186 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w186 pick186 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k186_1_6 k186_1_13
theorem cov186_1 : PA.Covered 1 (OZ.Valid 1 w186.low w186.t w186.y w186.r w186.cap) (P33.root 1) :=
  Night6836Tree.sound w186 pick186 1 t7674 _ k186_1_14
private theorem k186_2_0 : check w186 pick186 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k186_2_1 : check w186 pick186 2 t5736 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k186_2_2 : check w186 pick186 2 t5737 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w186 pick186 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5736 k186_2_0 k186_2_1
private theorem k186_2_3 : check w186 pick186 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k186_2_4 : check w186 pick186 2 t7736 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k186_2_5 : check w186 pick186 2 t7737 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w186 pick186 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t7736 k186_2_3 k186_2_4
private theorem k186_2_6 : check w186 pick186 2 t7738 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w186 pick186 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5737 t7737 k186_2_2 k186_2_5
theorem cov186_2 : PA.Covered 2 (OZ.Valid 2 w186.low w186.t w186.y w186.r w186.cap) (P33.root 2) :=
  Night6836Tree.sound w186 pick186 2 t7738 _ k186_2_6
theorem cov186_3 : PA.Covered 3 (OZ.Valid 3 w186.low w186.t w186.y w186.r w186.cap) (P33.root 3) :=
  Night6836Tree.sound w186 pick186 3 t4151 _ (by decide +kernel)
theorem cov186_4 : PA.Covered 4 (OZ.Valid 4 w186.low w186.t w186.y w186.r w186.cap) (P33.root 4) :=
  Night6836Tree.sound w186 pick186 4 t565 _ (by decide +kernel)
theorem cov186_5 : PA.Covered 5 (OZ.Valid 5 w186.low w186.t w186.y w186.r w186.cap) (P33.root 5) :=
  Night6836Tree.sound w186 pick186 5 t566 _ (by decide +kernel)
theorem cov186_6 : PA.Covered 6 (OZ.Valid 6 w186.low w186.t w186.y w186.r w186.cap) (P33.root 6) :=
  Night6836Tree.sound w186 pick186 6 t567 _ (by decide +kernel)
theorem cov186_7 : PA.Covered 7 (OZ.Valid 7 w186.low w186.t w186.y w186.r w186.cap) (P33.root 7) :=
  Night6836Tree.sound w186 pick186 7 t568 _ (by decide +kernel)
theorem window186 : P33.WindowCount w186 := by
  apply P33.window_count w186 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov186_1
  · exact cov186_2
  · exact cov186_3
  · exact cov186_4
  · exact cov186_5
  · exact cov186_6
  · exact cov186_7
def w187 : P33.Window := ⟨12,38,6669,6606,247469531877509902,22972,27000,5000000,81920000000⟩
def h187_0 : Height w187 := ⟨22972,27000,by decide +kernel⟩
def h187_1 : Height w187 := ⟨26924,24000,by decide +kernel⟩
def h187_2 : Height w187 := ⟨32102,21000,by decide +kernel⟩
def h187_3 : Height w187 := ⟨39730,18000,by decide +kernel⟩
def h187_4 : Height w187 := ⟨53459,15000,by decide +kernel⟩
def pick187 (cl : ℕ) : Height w187 := if cl<18 then (if cl<2 then (h187_0) else (h187_1)) else (if cl<148 then (h187_2) else (if cl<972 then (h187_3) else (h187_4)))
private theorem k187_1_0 : check w187 pick187 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k187_1_1 : check w187 pick187 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k187_1_2 : check w187 pick187 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w187 pick187 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k187_1_0 k187_1_1
private theorem k187_1_3 : check w187 pick187 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k187_1_4 : check w187 pick187 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k187_1_5 : check w187 pick187 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w187 pick187 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k187_1_3 k187_1_4
private theorem k187_1_6 : check w187 pick187 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w187 pick187 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k187_1_2 k187_1_5
private theorem k187_1_7 : check w187 pick187 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k187_1_8 : check w187 pick187 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k187_1_9 : check w187 pick187 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w187 pick187 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k187_1_7 k187_1_8
private theorem k187_1_10 : check w187 pick187 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k187_1_11 : check w187 pick187 1 t7741 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k187_1_12 : check w187 pick187 1 t7742 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w187 pick187 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7741 k187_1_10 k187_1_11
private theorem k187_1_13 : check w187 pick187 1 t7743 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w187 pick187 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7742 k187_1_9 k187_1_12
private theorem k187_1_14 : check w187 pick187 1 t7744 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w187 pick187 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7743 k187_1_6 k187_1_13
theorem cov187_1 : PA.Covered 1 (OZ.Valid 1 w187.low w187.t w187.y w187.r w187.cap) (P33.root 1) :=
  Night6836Tree.sound w187 pick187 1 t7744 _ k187_1_14
private theorem k187_2_0 : check w187 pick187 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k187_2_1 : check w187 pick187 2 t5736 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k187_2_2 : check w187 pick187 2 t5737 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w187 pick187 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5736 k187_2_0 k187_2_1
private theorem k187_2_3 : check w187 pick187 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k187_2_4 : check w187 pick187 2 t5898 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k187_2_5 : check w187 pick187 2 t5899 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w187 pick187 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t5898 k187_2_3 k187_2_4
private theorem k187_2_6 : check w187 pick187 2 t7745 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w187 pick187 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5737 t5899 k187_2_2 k187_2_5
theorem cov187_2 : PA.Covered 2 (OZ.Valid 2 w187.low w187.t w187.y w187.r w187.cap) (P33.root 2) :=
  Night6836Tree.sound w187 pick187 2 t7745 _ k187_2_6
theorem cov187_3 : PA.Covered 3 (OZ.Valid 3 w187.low w187.t w187.y w187.r w187.cap) (P33.root 3) :=
  Night6836Tree.sound w187 pick187 3 t4151 _ (by decide +kernel)
theorem cov187_4 : PA.Covered 4 (OZ.Valid 4 w187.low w187.t w187.y w187.r w187.cap) (P33.root 4) :=
  Night6836Tree.sound w187 pick187 4 t565 _ (by decide +kernel)
theorem cov187_5 : PA.Covered 5 (OZ.Valid 5 w187.low w187.t w187.y w187.r w187.cap) (P33.root 5) :=
  Night6836Tree.sound w187 pick187 5 t566 _ (by decide +kernel)
theorem cov187_6 : PA.Covered 6 (OZ.Valid 6 w187.low w187.t w187.y w187.r w187.cap) (P33.root 6) :=
  Night6836Tree.sound w187 pick187 6 t567 _ (by decide +kernel)
theorem cov187_7 : PA.Covered 7 (OZ.Valid 7 w187.low w187.t w187.y w187.r w187.cap) (P33.root 7) :=
  Night6836Tree.sound w187 pick187 7 t568 _ (by decide +kernel)
theorem window187 : P33.WindowCount w187 := by
  apply P33.window_count w187 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov187_1
  · exact cov187_2
  · exact cov187_3
  · exact cov187_4
  · exact cov187_5
  · exact cov187_6
  · exact cov187_7
def w188 : P33.Window := ⟨12,39,6172,5223,245790776718299748,31907,33000,5000000,81920000000⟩
def h188_0 : Height w188 := ⟨31907,33000,by decide +kernel⟩
def h188_1 : Height w188 := ⟨36114,30000,by decide +kernel⟩
def h188_2 : Height w188 := ⟨41360,27000,by decide +kernel⟩
def h188_3 : Height w188 := ⟨48381,24000,by decide +kernel⟩
def h188_4 : Height w188 := ⟨58825,21000,by decide +kernel⟩
def h188_5 : Height w188 := ⟨77265,18000,by decide +kernel⟩
def pick188 (cl : ℕ) : Height w188 := if cl<95 then (if cl<4 then (h188_0) else (if cl<25 then (h188_1) else (h188_2))) else (if cl<673 then (h188_3) else (if cl<1026 then (h188_4) else (h188_5)))
private theorem k188_1_0 : check w188 pick188 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k188_1_1 : check w188 pick188 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k188_1_2 : check w188 pick188 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w188 pick188 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k188_1_0 k188_1_1
private theorem k188_1_3 : check w188 pick188 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k188_1_4 : check w188 pick188 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k188_1_5 : check w188 pick188 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w188 pick188 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k188_1_3 k188_1_4
private theorem k188_1_6 : check w188 pick188 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w188 pick188 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k188_1_2 k188_1_5
private theorem k188_1_7 : check w188 pick188 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k188_1_8 : check w188 pick188 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k188_1_9 : check w188 pick188 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w188 pick188 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k188_1_7 k188_1_8
private theorem k188_1_10 : check w188 pick188 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k188_1_11 : check w188 pick188 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k188_1_12 : check w188 pick188 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w188 pick188 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k188_1_10 k188_1_11
private theorem k188_1_13 : check w188 pick188 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w188 pick188 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k188_1_9 k188_1_12
private theorem k188_1_14 : check w188 pick188 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w188 pick188 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k188_1_6 k188_1_13
theorem cov188_1 : PA.Covered 1 (OZ.Valid 1 w188.low w188.t w188.y w188.r w188.cap) (P33.root 1) :=
  Night6836Tree.sound w188 pick188 1 t7674 _ k188_1_14
private theorem k188_2_0 : check w188 pick188 2 t5695 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k188_2_1 : check w188 pick188 2 t5699 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k188_2_2 : check w188 pick188 2 t5700 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w188 pick188 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5695 t5699 k188_2_0 k188_2_1
private theorem k188_2_3 : check w188 pick188 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k188_2_4 : check w188 pick188 2 t7746 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k188_2_5 : check w188 pick188 2 t7747 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w188 pick188 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t7746 k188_2_3 k188_2_4
private theorem k188_2_6 : check w188 pick188 2 t7748 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w188 pick188 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5700 t7747 k188_2_2 k188_2_5
theorem cov188_2 : PA.Covered 2 (OZ.Valid 2 w188.low w188.t w188.y w188.r w188.cap) (P33.root 2) :=
  Night6836Tree.sound w188 pick188 2 t7748 _ k188_2_6
theorem cov188_3 : PA.Covered 3 (OZ.Valid 3 w188.low w188.t w188.y w188.r w188.cap) (P33.root 3) :=
  Night6836Tree.sound w188 pick188 3 t564 _ (by decide +kernel)
theorem cov188_4 : PA.Covered 4 (OZ.Valid 4 w188.low w188.t w188.y w188.r w188.cap) (P33.root 4) :=
  Night6836Tree.sound w188 pick188 4 t565 _ (by decide +kernel)
theorem cov188_5 : PA.Covered 5 (OZ.Valid 5 w188.low w188.t w188.y w188.r w188.cap) (P33.root 5) :=
  Night6836Tree.sound w188 pick188 5 t566 _ (by decide +kernel)
theorem cov188_6 : PA.Covered 6 (OZ.Valid 6 w188.low w188.t w188.y w188.r w188.cap) (P33.root 6) :=
  Night6836Tree.sound w188 pick188 6 t567 _ (by decide +kernel)
theorem cov188_7 : PA.Covered 7 (OZ.Valid 7 w188.low w188.t w188.y w188.r w188.cap) (P33.root 7) :=
  Night6836Tree.sound w188 pick188 7 t2134 _ (by decide +kernel)
theorem window188 : P33.WindowCount w188 := by
  apply P33.window_count w188 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov188_1
  · exact cov188_2
  · exact cov188_3
  · exact cov188_4
  · exact cov188_5
  · exact cov188_6
  · exact cov188_7
def w189 : P33.Window := ⟨12,39,6605,6535,247411228554936406,24728,27000,5000000,81920000000⟩
def h189_0 : Height w189 := ⟨24728,27000,by decide +kernel⟩
def h189_1 : Height w189 := ⟨28841,24000,by decide +kernel⟩
def h189_2 : Height w189 := ⟨34273,21000,by decide +kernel⟩
def h189_3 : Height w189 := ⟨42350,18000,by decide +kernel⟩
def h189_4 : Height w189 := ⟨57076,15000,by decide +kernel⟩
def pick189 (cl : ℕ) : Height w189 := if cl<25 then (if cl<3 then (h189_0) else (h189_1)) else (if cl<195 then (h189_2) else (if cl<998 then (h189_3) else (h189_4)))
private theorem k189_1_0 : check w189 pick189 1 t7750 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k189_1_1 : check w189 pick189 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k189_1_2 : check w189 pick189 1 t7751 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w189 pick189 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7750 t7661 k189_1_0 k189_1_1
private theorem k189_1_3 : check w189 pick189 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k189_1_4 : check w189 pick189 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k189_1_5 : check w189 pick189 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w189 pick189 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k189_1_3 k189_1_4
private theorem k189_1_6 : check w189 pick189 1 t7752 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w189 pick189 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7751 t7672 k189_1_2 k189_1_5
private theorem k189_1_7 : check w189 pick189 1 t7755 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k189_1_8 : check w189 pick189 1 t7760 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k189_1_9 : check w189 pick189 1 t7761 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w189 pick189 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7755 t7760 k189_1_7 k189_1_8
private theorem k189_1_10 : check w189 pick189 1 t7767 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k189_1_11 : check w189 pick189 1 t7769 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k189_1_12 : check w189 pick189 1 t7770 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w189 pick189 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7767 t7769 k189_1_10 k189_1_11
private theorem k189_1_13 : check w189 pick189 1 t7771 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w189 pick189 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7761 t7770 k189_1_9 k189_1_12
private theorem k189_1_14 : check w189 pick189 1 t7772 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w189 pick189 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7752 t7771 k189_1_6 k189_1_13
theorem cov189_1 : PA.Covered 1 (OZ.Valid 1 w189.low w189.t w189.y w189.r w189.cap) (P33.root 1) :=
  Night6836Tree.sound w189 pick189 1 t7772 _ k189_1_14
private theorem k189_2_0 : check w189 pick189 2 t5829 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k189_2_1 : check w189 pick189 2 t7782 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k189_2_2 : check w189 pick189 2 t7783 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w189 pick189 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5829 t7782 k189_2_0 k189_2_1
private theorem k189_2_3 : check w189 pick189 2 t5938 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k189_2_4 : check w189 pick189 2 t5912 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k189_2_5 : check w189 pick189 2 t5939 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w189 pick189 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t5938 t5912 k189_2_3 k189_2_4
private theorem k189_2_6 : check w189 pick189 2 t7784 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w189 pick189 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t7783 t5939 k189_2_2 k189_2_5
theorem cov189_2 : PA.Covered 2 (OZ.Valid 2 w189.low w189.t w189.y w189.r w189.cap) (P33.root 2) :=
  Night6836Tree.sound w189 pick189 2 t7784 _ k189_2_6
theorem cov189_3 : PA.Covered 3 (OZ.Valid 3 w189.low w189.t w189.y w189.r w189.cap) (P33.root 3) :=
  Night6836Tree.sound w189 pick189 3 t4231 _ (by decide +kernel)
theorem cov189_4 : PA.Covered 4 (OZ.Valid 4 w189.low w189.t w189.y w189.r w189.cap) (P33.root 4) :=
  Night6836Tree.sound w189 pick189 4 t565 _ (by decide +kernel)
theorem cov189_5 : PA.Covered 5 (OZ.Valid 5 w189.low w189.t w189.y w189.r w189.cap) (P33.root 5) :=
  Night6836Tree.sound w189 pick189 5 t566 _ (by decide +kernel)
theorem cov189_6 : PA.Covered 6 (OZ.Valid 6 w189.low w189.t w189.y w189.r w189.cap) (P33.root 6) :=
  Night6836Tree.sound w189 pick189 6 t567 _ (by decide +kernel)
theorem cov189_7 : PA.Covered 7 (OZ.Valid 7 w189.low w189.t w189.y w189.r w189.cap) (P33.root 7) :=
  Night6836Tree.sound w189 pick189 7 t568 _ (by decide +kernel)
theorem window189 : P33.WindowCount w189 := by
  apply P33.window_count w189 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov189_1
  · exact cov189_2
  · exact cov189_3
  · exact cov189_4
  · exact cov189_5
  · exact cov189_6
  · exact cov189_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w190 : P33.Window := ⟨12,40,6534,6456,247251220951735023,26617,27000,5000000,81920000000⟩
def h190_0 : Height w190 := ⟨26617,27000,by decide +kernel⟩
def h190_1 : Height w190 := ⟨30913,24000,by decide +kernel⟩
def h190_2 : Height w190 := ⟨36632,21000,by decide +kernel⟩
def h190_3 : Height w190 := ⟨45223,18000,by decide +kernel⟩
def h190_4 : Height w190 := ⟨61111,15000,by decide +kernel⟩
def pick190 (cl : ℕ) : Height w190 := if cl<31 then (if cl<4 then (h190_0) else (h190_1)) else (if cl<253 then (h190_2) else (if cl<1021 then (h190_3) else (h190_4)))
private theorem k190_1_0 : check w190 pick190 1 t7750 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k190_1_1 : check w190 pick190 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k190_1_2 : check w190 pick190 1 t7751 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w190 pick190 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7750 t7661 k190_1_0 k190_1_1
private theorem k190_1_3 : check w190 pick190 1 t7786 ⟨1,7,2,16,1,52,77,90⟩ = true := by decide +kernel
private theorem k190_1_4 : check w190 pick190 1 t7790 ⟨1,7,2,16,1,52,91,110⟩ = true := by decide +kernel
private theorem k190_1_5 : check w190 pick190 1 t7791 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w190 pick190 1 ⟨1,7,2,16,1,52,77,110⟩ 3 90 t7786 t7790 k190_1_3 k190_1_4
private theorem k190_1_6 : check w190 pick190 1 t7796 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k190_1_7 : check w190 pick190 1 t7797 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w190 pick190 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7791 t7796 k190_1_5 k190_1_6
private theorem k190_1_8 : check w190 pick190 1 t7798 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w190 pick190 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7751 t7797 k190_1_2 k190_1_7
private theorem k190_1_9 : check w190 pick190 1 t7801 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k190_1_10 : check w190 pick190 1 t7805 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k190_1_11 : check w190 pick190 1 t7806 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w190 pick190 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t7801 t7805 k190_1_9 k190_1_10
private theorem k190_1_12 : check w190 pick190 1 t7840 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k190_1_13 : check w190 pick190 1 t7769 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k190_1_14 : check w190 pick190 1 t7841 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w190 pick190 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7840 t7769 k190_1_12 k190_1_13
private theorem k190_1_15 : check w190 pick190 1 t7842 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w190 pick190 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7806 t7841 k190_1_11 k190_1_14
private theorem k190_1_16 : check w190 pick190 1 t7843 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w190 pick190 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7798 t7842 k190_1_8 k190_1_15
theorem cov190_1 : PA.Covered 1 (OZ.Valid 1 w190.low w190.t w190.y w190.r w190.cap) (P33.root 1) :=
  Night6836Tree.sound w190 pick190 1 t7843 _ k190_1_16
private theorem k190_2_0 : check w190 pick190 2 t5829 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k190_2_1 : check w190 pick190 2 t7858 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k190_2_2 : check w190 pick190 2 t7859 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w190 pick190 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5829 t7858 k190_2_0 k190_2_1
private theorem k190_2_3 : check w190 pick190 2 t5956 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k190_2_4 : check w190 pick190 2 t5912 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k190_2_5 : check w190 pick190 2 t5957 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w190 pick190 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t5956 t5912 k190_2_3 k190_2_4
private theorem k190_2_6 : check w190 pick190 2 t7860 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w190 pick190 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t7859 t5957 k190_2_2 k190_2_5
theorem cov190_2 : PA.Covered 2 (OZ.Valid 2 w190.low w190.t w190.y w190.r w190.cap) (P33.root 2) :=
  Night6836Tree.sound w190 pick190 2 t7860 _ k190_2_6
theorem cov190_3 : PA.Covered 3 (OZ.Valid 3 w190.low w190.t w190.y w190.r w190.cap) (P33.root 3) :=
  Night6836Tree.sound w190 pick190 3 t4231 _ (by decide +kernel)
theorem cov190_4 : PA.Covered 4 (OZ.Valid 4 w190.low w190.t w190.y w190.r w190.cap) (P33.root 4) :=
  Night6836Tree.sound w190 pick190 4 t565 _ (by decide +kernel)
theorem cov190_5 : PA.Covered 5 (OZ.Valid 5 w190.low w190.t w190.y w190.r w190.cap) (P33.root 5) :=
  Night6836Tree.sound w190 pick190 5 t566 _ (by decide +kernel)
theorem cov190_6 : PA.Covered 6 (OZ.Valid 6 w190.low w190.t w190.y w190.r w190.cap) (P33.root 6) :=
  Night6836Tree.sound w190 pick190 6 t567 _ (by decide +kernel)
theorem cov190_7 : PA.Covered 7 (OZ.Valid 7 w190.low w190.t w190.y w190.r w190.cap) (P33.root 7) :=
  Night6836Tree.sound w190 pick190 7 t568 _ (by decide +kernel)
theorem window190 : P33.WindowCount w190 := by
  apply P33.window_count w190 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov190_1
  · exact cov190_2
  · exact cov190_3
  · exact cov190_4
  · exact cov190_5
  · exact cov190_6
  · exact cov190_7
def w191 : P33.Window := ⟨12,41,6455,5782,246893844683530582,31221,30000,5000000,81920000000⟩
def h191_0 : Height w191 := ⟨31221,30000,by decide +kernel⟩
def h191_1 : Height w191 := ⟨35582,27000,by decide +kernel⟩
def h191_2 : Height w191 := ⟨41193,24000,by decide +kernel⟩
def h191_3 : Height w191 := ⟨49097,21000,by decide +kernel⟩
def h191_4 : Height w191 := ⟨61946,18000,by decide +kernel⟩
def pick191 (cl : ℕ) : Height w191 := if cl<26 then (if cl<5 then (h191_0) else (h191_1)) else (if cl<168 then (h191_2) else (if cl<947 then (h191_3) else (h191_4)))
private theorem k191_1_0 : check w191 pick191 1 t7861 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k191_1_1 : check w191 pick191 1 t7864 ⟨1,7,2,16,1,52,43,62⟩ = true := by decide +kernel
private theorem k191_1_2 : check w191 pick191 1 t7867 ⟨1,7,2,16,1,52,63,76⟩ = true := by decide +kernel
private theorem k191_1_3 : check w191 pick191 1 t7868 ⟨1,7,2,16,1,52,43,76⟩ = true := glue w191 pick191 1 ⟨1,7,2,16,1,52,43,76⟩ 3 62 t7864 t7867 k191_1_1 k191_1_2
private theorem k191_1_4 : check w191 pick191 1 t7869 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w191 pick191 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7861 t7868 k191_1_0 k191_1_3
private theorem k191_1_5 : check w191 pick191 1 t7875 ⟨1,7,2,16,1,52,77,90⟩ = true := by decide +kernel
private theorem k191_1_6 : check w191 pick191 1 t7881 ⟨1,7,2,16,1,52,91,110⟩ = true := by decide +kernel
private theorem k191_1_7 : check w191 pick191 1 t7882 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w191 pick191 1 ⟨1,7,2,16,1,52,77,110⟩ 3 90 t7875 t7881 k191_1_5 k191_1_6
private theorem k191_1_8 : check w191 pick191 1 t7889 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k191_1_9 : check w191 pick191 1 t7890 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w191 pick191 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7882 t7889 k191_1_7 k191_1_8
private theorem k191_1_10 : check w191 pick191 1 t7891 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w191 pick191 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7869 t7890 k191_1_4 k191_1_9
private theorem k191_1_11 : check w191 pick191 1 t7903 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k191_1_12 : check w191 pick191 1 t7940 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k191_1_13 : check w191 pick191 1 t7941 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w191 pick191 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7903 t7940 k191_1_11 k191_1_12
private theorem k191_1_14 : check w191 pick191 1 t7952 ⟨1,7,2,16,1,52,193,206⟩ = true := by decide +kernel
private theorem k191_1_15 : check w191 pick191 1 t7954 ⟨1,7,2,16,1,52,207,226⟩ = true := by decide +kernel
private theorem k191_1_16 : check w191 pick191 1 t7955 ⟨1,7,2,16,1,52,193,226⟩ = true := glue w191 pick191 1 ⟨1,7,2,16,1,52,193,226⟩ 3 206 t7952 t7954 k191_1_14 k191_1_15
private theorem k191_1_17 : check w191 pick191 1 t7959 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k191_1_18 : check w191 pick191 1 t7960 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w191 pick191 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7955 t7959 k191_1_16 k191_1_17
private theorem k191_1_19 : check w191 pick191 1 t7961 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w191 pick191 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7941 t7960 k191_1_13 k191_1_18
private theorem k191_1_20 : check w191 pick191 1 t7962 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w191 pick191 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7891 t7961 k191_1_10 k191_1_19
theorem cov191_1 : PA.Covered 1 (OZ.Valid 1 w191.low w191.t w191.y w191.r w191.cap) (P33.root 1) :=
  Night6836Tree.sound w191 pick191 1 t7962 _ k191_1_20
private theorem k191_2_0 : check w191 pick191 2 t5936 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k191_2_1 : check w191 pick191 2 t7858 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k191_2_2 : check w191 pick191 2 t7963 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w191 pick191 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5936 t7858 k191_2_0 k191_2_1
private theorem k191_2_3 : check w191 pick191 2 t6080 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k191_2_4 : check w191 pick191 2 t7964 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k191_2_5 : check w191 pick191 2 t7965 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w191 pick191 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t6080 t7964 k191_2_3 k191_2_4
private theorem k191_2_6 : check w191 pick191 2 t7966 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w191 pick191 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t7963 t7965 k191_2_2 k191_2_5
theorem cov191_2 : PA.Covered 2 (OZ.Valid 2 w191.low w191.t w191.y w191.r w191.cap) (P33.root 2) :=
  Night6836Tree.sound w191 pick191 2 t7966 _ k191_2_6
theorem cov191_3 : PA.Covered 3 (OZ.Valid 3 w191.low w191.t w191.y w191.r w191.cap) (P33.root 3) :=
  Night6836Tree.sound w191 pick191 3 t4800 _ (by decide +kernel)
theorem cov191_4 : PA.Covered 4 (OZ.Valid 4 w191.low w191.t w191.y w191.r w191.cap) (P33.root 4) :=
  Night6836Tree.sound w191 pick191 4 t565 _ (by decide +kernel)
theorem cov191_5 : PA.Covered 5 (OZ.Valid 5 w191.low w191.t w191.y w191.r w191.cap) (P33.root 5) :=
  Night6836Tree.sound w191 pick191 5 t566 _ (by decide +kernel)
theorem cov191_6 : PA.Covered 6 (OZ.Valid 6 w191.low w191.t w191.y w191.r w191.cap) (P33.root 6) :=
  Night6836Tree.sound w191 pick191 6 t567 _ (by decide +kernel)
theorem cov191_7 : PA.Covered 7 (OZ.Valid 7 w191.low w191.t w191.y w191.r w191.cap) (P33.root 7) :=
  Night6836Tree.sound w191 pick191 7 t568 _ (by decide +kernel)
theorem window191 : P33.WindowCount w191 := by
  apply P33.window_count w191 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov191_1
  · exact cov191_2
  · exact cov191_3
  · exact cov191_4
  · exact cov191_5
  · exact cov191_6
  · exact cov191_7
def w192 : P33.Window := ⟨12,42,5222,4273,245017575595521684,42193,42000,5000000,81920000000⟩
def h192_0 : Height w192 := ⟨42193,42000,by decide +kernel⟩
def h192_1 : Height w192 := ⟨46205,39000,by decide +kernel⟩
def h192_2 : Height w192 := ⟨50898,36000,by decide +kernel⟩
def h192_3 : Height w192 := ⟨56589,33000,by decide +kernel⟩
def h192_4 : Height w192 := ⟨63833,30000,by decide +kernel⟩
def h192_5 : Height w192 := ⟨73684,27000,by decide +kernel⟩
def h192_6 : Height w192 := ⟨88421,24000,by decide +kernel⟩
def pick192 (cl : ℕ) : Height w192 := if cl<32 then (if cl<2 then (h192_0) else (if cl<10 then (h192_1) else (h192_2))) else (if cl<421 then (if cl<107 then (h192_3) else (h192_4)) else (if cl<998 then (h192_5) else (h192_6)))
private theorem k192_1_0 : check w192 pick192 1 t7465 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k192_1_1 : check w192 pick192 1 t7341 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k192_1_2 : check w192 pick192 1 t7967 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w192 pick192 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7465 t7341 k192_1_0 k192_1_1
private theorem k192_1_3 : check w192 pick192 1 t7969 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k192_1_4 : check w192 pick192 1 t7972 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k192_1_5 : check w192 pick192 1 t7973 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w192 pick192 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t7969 t7972 k192_1_3 k192_1_4
private theorem k192_1_6 : check w192 pick192 1 t7974 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w192 pick192 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t7967 t7973 k192_1_2 k192_1_5
private theorem k192_1_7 : check w192 pick192 1 t7489 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k192_1_8 : check w192 pick192 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k192_1_9 : check w192 pick192 1 t7490 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w192 pick192 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7489 t6872 k192_1_7 k192_1_8
private theorem k192_1_10 : check w192 pick192 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k192_1_11 : check w192 pick192 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k192_1_12 : check w192 pick192 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w192 pick192 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k192_1_10 k192_1_11
private theorem k192_1_13 : check w192 pick192 1 t7491 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w192 pick192 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7490 t7190 k192_1_9 k192_1_12
private theorem k192_1_14 : check w192 pick192 1 t7975 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w192 pick192 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7974 t7491 k192_1_6 k192_1_13
theorem cov192_1 : PA.Covered 1 (OZ.Valid 1 w192.low w192.t w192.y w192.r w192.cap) (P33.root 1) :=
  Night6836Tree.sound w192 pick192 1 t7975 _ k192_1_14
private theorem k192_2_0 : check w192 pick192 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k192_2_1 : check w192 pick192 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k192_2_2 : check w192 pick192 2 t5528 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w192 pick192 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t3303 k192_2_0 k192_2_1
theorem cov192_2 : PA.Covered 2 (OZ.Valid 2 w192.low w192.t w192.y w192.r w192.cap) (P33.root 2) :=
  Night6836Tree.sound w192 pick192 2 t5528 _ k192_2_2
theorem cov192_3 : PA.Covered 3 (OZ.Valid 3 w192.low w192.t w192.y w192.r w192.cap) (P33.root 3) :=
  Night6836Tree.sound w192 pick192 3 t564 _ (by decide +kernel)
theorem cov192_4 : PA.Covered 4 (OZ.Valid 4 w192.low w192.t w192.y w192.r w192.cap) (P33.root 4) :=
  Night6836Tree.sound w192 pick192 4 t565 _ (by decide +kernel)
theorem cov192_5 : PA.Covered 5 (OZ.Valid 5 w192.low w192.t w192.y w192.r w192.cap) (P33.root 5) :=
  Night6836Tree.sound w192 pick192 5 t566 _ (by decide +kernel)
theorem cov192_6 : PA.Covered 6 (OZ.Valid 6 w192.low w192.t w192.y w192.r w192.cap) (P33.root 6) :=
  Night6836Tree.sound w192 pick192 6 t567 _ (by decide +kernel)
theorem cov192_7 : PA.Covered 7 (OZ.Valid 7 w192.low w192.t w192.y w192.r w192.cap) (P33.root 7) :=
  Night6836Tree.sound w192 pick192 7 t2134 _ (by decide +kernel)
theorem window192 : P33.WindowCount w192 := by
  apply P33.window_count w192 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov192_1
  · exact cov192_2
  · exact cov192_3
  · exact cov192_4
  · exact cov192_5
  · exact cov192_6
  · exact cov192_7
def w193 : P33.Window := ⟨12,42,6304,6081,247499765030572469,29066,30000,5000000,81920000000⟩
def h193_0 : Height w193 := ⟨29066,30000,by decide +kernel⟩
def h193_1 : Height w193 := ⟨33085,27000,by decide +kernel⟩
def h193_2 : Height w193 := ⟨38164,24000,by decide +kernel⟩
def h193_3 : Height w193 := ⟨45154,21000,by decide +kernel⟩
def h193_4 : Height w193 := ⟨56129,18000,by decide +kernel⟩
def pick193 (cl : ℕ) : Height w193 := if cl<15 then (if cl<2 then (h193_0) else (h193_1)) else (if cl<90 then (h193_2) else (if cl<816 then (h193_3) else (h193_4)))
private theorem k193_1_0 : check w193 pick193 1 t7861 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k193_1_1 : check w193 pick193 1 t7864 ⟨1,7,2,16,1,52,43,62⟩ = true := by decide +kernel
private theorem k193_1_2 : check w193 pick193 1 t7867 ⟨1,7,2,16,1,52,63,76⟩ = true := by decide +kernel
private theorem k193_1_3 : check w193 pick193 1 t7868 ⟨1,7,2,16,1,52,43,76⟩ = true := glue w193 pick193 1 ⟨1,7,2,16,1,52,43,76⟩ 3 62 t7864 t7867 k193_1_1 k193_1_2
private theorem k193_1_4 : check w193 pick193 1 t7869 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w193 pick193 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7861 t7868 k193_1_0 k193_1_3
private theorem k193_1_5 : check w193 pick193 1 t7976 ⟨1,7,2,16,1,52,77,90⟩ = true := by decide +kernel
private theorem k193_1_6 : check w193 pick193 1 t7790 ⟨1,7,2,16,1,52,91,110⟩ = true := by decide +kernel
private theorem k193_1_7 : check w193 pick193 1 t7977 ⟨1,7,2,16,1,52,77,110⟩ = true := glue w193 pick193 1 ⟨1,7,2,16,1,52,77,110⟩ 3 90 t7976 t7790 k193_1_5 k193_1_6
private theorem k193_1_8 : check w193 pick193 1 t7980 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k193_1_9 : check w193 pick193 1 t7981 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w193 pick193 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7977 t7980 k193_1_7 k193_1_8
private theorem k193_1_10 : check w193 pick193 1 t7982 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w193 pick193 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7869 t7981 k193_1_4 k193_1_9
private theorem k193_1_11 : check w193 pick193 1 t7801 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k193_1_12 : check w193 pick193 1 t7805 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k193_1_13 : check w193 pick193 1 t7806 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w193 pick193 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t7801 t7805 k193_1_11 k193_1_12
private theorem k193_1_14 : check w193 pick193 1 t7840 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k193_1_15 : check w193 pick193 1 t7769 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k193_1_16 : check w193 pick193 1 t7841 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w193 pick193 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7840 t7769 k193_1_14 k193_1_15
private theorem k193_1_17 : check w193 pick193 1 t7842 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w193 pick193 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7806 t7841 k193_1_13 k193_1_16
private theorem k193_1_18 : check w193 pick193 1 t7983 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w193 pick193 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7982 t7842 k193_1_10 k193_1_17
theorem cov193_1 : PA.Covered 1 (OZ.Valid 1 w193.low w193.t w193.y w193.r w193.cap) (P33.root 1) :=
  Night6836Tree.sound w193 pick193 1 t7983 _ k193_1_18
private theorem k193_2_0 : check w193 pick193 2 t5936 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k193_2_1 : check w193 pick193 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k193_2_2 : check w193 pick193 2 t5937 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w193 pick193 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5936 t4131 k193_2_0 k193_2_1
private theorem k193_2_3 : check w193 pick193 2 t6080 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k193_2_4 : check w193 pick193 2 t7986 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k193_2_5 : check w193 pick193 2 t7987 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w193 pick193 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t6080 t7986 k193_2_3 k193_2_4
private theorem k193_2_6 : check w193 pick193 2 t7988 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w193 pick193 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5937 t7987 k193_2_2 k193_2_5
theorem cov193_2 : PA.Covered 2 (OZ.Valid 2 w193.low w193.t w193.y w193.r w193.cap) (P33.root 2) :=
  Night6836Tree.sound w193 pick193 2 t7988 _ k193_2_6
theorem cov193_3 : PA.Covered 3 (OZ.Valid 3 w193.low w193.t w193.y w193.r w193.cap) (P33.root 3) :=
  Night6836Tree.sound w193 pick193 3 t4231 _ (by decide +kernel)
theorem cov193_4 : PA.Covered 4 (OZ.Valid 4 w193.low w193.t w193.y w193.r w193.cap) (P33.root 4) :=
  Night6836Tree.sound w193 pick193 4 t565 _ (by decide +kernel)
theorem cov193_5 : PA.Covered 5 (OZ.Valid 5 w193.low w193.t w193.y w193.r w193.cap) (P33.root 5) :=
  Night6836Tree.sound w193 pick193 5 t566 _ (by decide +kernel)
theorem cov193_6 : PA.Covered 6 (OZ.Valid 6 w193.low w193.t w193.y w193.r w193.cap) (P33.root 6) :=
  Night6836Tree.sound w193 pick193 6 t567 _ (by decide +kernel)
theorem cov193_7 : PA.Covered 7 (OZ.Valid 7 w193.low w193.t w193.y w193.r w193.cap) (P33.root 7) :=
  Night6836Tree.sound w193 pick193 7 t2134 _ (by decide +kernel)
theorem window193 : P33.WindowCount w193 := by
  apply P33.window_count w193 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov193_1
  · exact cov193_2
  · exact cov193_3
  · exact cov193_4
  · exact cov193_5
  · exact cov193_6
  · exact cov193_7
def w194 : P33.Window := ⟨12,43,6080,5849,247475667184819620,33009,30000,5000000,81920000000⟩
def h194_0 : Height w194 := ⟨33009,30000,by decide +kernel⟩
def h194_1 : Height w194 := ⟨37424,27000,by decide +kernel⟩
def h194_2 : Height w194 := ⟨43103,24000,by decide +kernel⟩
def h194_3 : Height w194 := ⟨51086,21000,by decide +kernel⟩
def h194_4 : Height w194 := ⟨63997,18000,by decide +kernel⟩
def pick194 (cl : ℕ) : Height w194 := if cl<27 then (if cl<5 then (h194_0) else (h194_1)) else (if cl<180 then (h194_2) else (if cl<947 then (h194_3) else (h194_4)))
private theorem k194_1_0 : check w194 pick194 1 t7750 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k194_1_1 : check w194 pick194 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k194_1_2 : check w194 pick194 1 t7751 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w194 pick194 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7750 t7661 k194_1_0 k194_1_1
private theorem k194_1_3 : check w194 pick194 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k194_1_4 : check w194 pick194 1 t7990 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k194_1_5 : check w194 pick194 1 t7991 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w194 pick194 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7990 k194_1_3 k194_1_4
private theorem k194_1_6 : check w194 pick194 1 t7992 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w194 pick194 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7751 t7991 k194_1_2 k194_1_5
private theorem k194_1_7 : check w194 pick194 1 t7801 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k194_1_8 : check w194 pick194 1 t7760 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k194_1_9 : check w194 pick194 1 t7993 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w194 pick194 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7801 t7760 k194_1_7 k194_1_8
private theorem k194_1_10 : check w194 pick194 1 t7767 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k194_1_11 : check w194 pick194 1 t7769 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k194_1_12 : check w194 pick194 1 t7770 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w194 pick194 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7767 t7769 k194_1_10 k194_1_11
private theorem k194_1_13 : check w194 pick194 1 t7994 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w194 pick194 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7993 t7770 k194_1_9 k194_1_12
private theorem k194_1_14 : check w194 pick194 1 t7995 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w194 pick194 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7992 t7994 k194_1_6 k194_1_13
theorem cov194_1 : PA.Covered 1 (OZ.Valid 1 w194.low w194.t w194.y w194.r w194.cap) (P33.root 1) :=
  Night6836Tree.sound w194 pick194 1 t7995 _ k194_1_14
private theorem k194_2_0 : check w194 pick194 2 t5936 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k194_2_1 : check w194 pick194 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k194_2_2 : check w194 pick194 2 t5937 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w194 pick194 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5936 t4131 k194_2_0 k194_2_1
private theorem k194_2_3 : check w194 pick194 2 t5956 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k194_2_4 : check w194 pick194 2 t8000 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k194_2_5 : check w194 pick194 2 t8001 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w194 pick194 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t5956 t8000 k194_2_3 k194_2_4
private theorem k194_2_6 : check w194 pick194 2 t8002 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w194 pick194 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5937 t8001 k194_2_2 k194_2_5
theorem cov194_2 : PA.Covered 2 (OZ.Valid 2 w194.low w194.t w194.y w194.r w194.cap) (P33.root 2) :=
  Night6836Tree.sound w194 pick194 2 t8002 _ k194_2_6
theorem cov194_3 : PA.Covered 3 (OZ.Valid 3 w194.low w194.t w194.y w194.r w194.cap) (P33.root 3) :=
  Night6836Tree.sound w194 pick194 3 t4877 _ (by decide +kernel)
theorem cov194_4 : PA.Covered 4 (OZ.Valid 4 w194.low w194.t w194.y w194.r w194.cap) (P33.root 4) :=
  Night6836Tree.sound w194 pick194 4 t565 _ (by decide +kernel)
theorem cov194_5 : PA.Covered 5 (OZ.Valid 5 w194.low w194.t w194.y w194.r w194.cap) (P33.root 5) :=
  Night6836Tree.sound w194 pick194 5 t566 _ (by decide +kernel)
theorem cov194_6 : PA.Covered 6 (OZ.Valid 6 w194.low w194.t w194.y w194.r w194.cap) (P33.root 6) :=
  Night6836Tree.sound w194 pick194 6 t567 _ (by decide +kernel)
theorem cov194_7 : PA.Covered 7 (OZ.Valid 7 w194.low w194.t w194.y w194.r w194.cap) (P33.root 7) :=
  Night6836Tree.sound w194 pick194 7 t2134 _ (by decide +kernel)
theorem window194 : P33.WindowCount w194 := by
  apply P33.window_count w194 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov194_1
  · exact cov194_2
  · exact cov194_3
  · exact cov194_4
  · exact cov194_5
  · exact cov194_6
  · exact cov194_7
def w195 : P33.Window := ⟨12,44,5781,4832,246419338465521567,41933,36000,5000000,81920000000⟩
def h195_0 : Height w195 := ⟨41933,36000,by decide +kernel⟩
def h195_1 : Height w195 := ⟨46414,33000,by decide +kernel⟩
def h195_2 : Height w195 := ⟨51901,30000,by decide +kernel⟩
def h195_3 : Height w195 := ⟨59007,27000,by decide +kernel⟩
def h195_4 : Height w195 := ⟨68966,24000,by decide +kernel⟩
def h195_5 : Height w195 := ⟨84673,21000,by decide +kernel⟩
def pick195 (cl : ℕ) : Height w195 := if cl<100 then (if cl<5 then (h195_0) else (if cl<25 then (h195_1) else (h195_2))) else (if cl<467 then (h195_3) else (if cl<1020 then (h195_4) else (h195_5)))
private theorem k195_1_0 : check w195 pick195 1 t8011 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k195_1_1 : check w195 pick195 1 t8028 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k195_1_2 : check w195 pick195 1 t8029 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w195 pick195 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t8011 t8028 k195_1_0 k195_1_1
private theorem k195_1_3 : check w195 pick195 1 t8038 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k195_1_4 : check w195 pick195 1 t2136 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k195_1_5 : check w195 pick195 1 t8039 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w195 pick195 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t8038 t2136 k195_1_3 k195_1_4
private theorem k195_1_6 : check w195 pick195 1 t8040 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w195 pick195 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t8029 t8039 k195_1_2 k195_1_5
private theorem k195_1_7 : check w195 pick195 1 t8053 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k195_1_8 : check w195 pick195 1 t8063 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k195_1_9 : check w195 pick195 1 t8064 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w195 pick195 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t8053 t8063 k195_1_7 k195_1_8
private theorem k195_1_10 : check w195 pick195 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k195_1_11 : check w195 pick195 1 t8067 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k195_1_12 : check w195 pick195 1 t8068 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w195 pick195 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t8067 k195_1_10 k195_1_11
private theorem k195_1_13 : check w195 pick195 1 t8069 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w195 pick195 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t8064 t8068 k195_1_9 k195_1_12
private theorem k195_1_14 : check w195 pick195 1 t8070 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w195 pick195 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8040 t8069 k195_1_6 k195_1_13
theorem cov195_1 : PA.Covered 1 (OZ.Valid 1 w195.low w195.t w195.y w195.r w195.cap) (P33.root 1) :=
  Night6836Tree.sound w195 pick195 1 t8070 _ k195_1_14
private theorem k195_2_0 : check w195 pick195 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k195_2_1 : check w195 pick195 2 t5736 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k195_2_2 : check w195 pick195 2 t5737 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w195 pick195 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5736 k195_2_0 k195_2_1
private theorem k195_2_3 : check w195 pick195 2 t8075 ⟨2,7,4,16,2,52,140,248⟩ = true := by decide +kernel
private theorem k195_2_4 : check w195 pick195 2 t8077 ⟨2,7,4,16,2,52,249,450⟩ = true := by decide +kernel
private theorem k195_2_5 : check w195 pick195 2 t8078 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w195 pick195 2 ⟨2,7,4,16,2,52,140,450⟩ 3 248 t8075 t8077 k195_2_3 k195_2_4
private theorem k195_2_6 : check w195 pick195 2 t8079 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w195 pick195 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5737 t8078 k195_2_2 k195_2_5
theorem cov195_2 : PA.Covered 2 (OZ.Valid 2 w195.low w195.t w195.y w195.r w195.cap) (P33.root 2) :=
  Night6836Tree.sound w195 pick195 2 t8079 _ k195_2_6
theorem cov195_3 : PA.Covered 3 (OZ.Valid 3 w195.low w195.t w195.y w195.r w195.cap) (P33.root 3) :=
  Night6836Tree.sound w195 pick195 3 t4877 _ (by decide +kernel)
theorem cov195_4 : PA.Covered 4 (OZ.Valid 4 w195.low w195.t w195.y w195.r w195.cap) (P33.root 4) :=
  Night6836Tree.sound w195 pick195 4 t565 _ (by decide +kernel)
theorem cov195_5 : PA.Covered 5 (OZ.Valid 5 w195.low w195.t w195.y w195.r w195.cap) (P33.root 5) :=
  Night6836Tree.sound w195 pick195 5 t566 _ (by decide +kernel)
theorem cov195_6 : PA.Covered 6 (OZ.Valid 6 w195.low w195.t w195.y w195.r w195.cap) (P33.root 6) :=
  Night6836Tree.sound w195 pick195 6 t567 _ (by decide +kernel)
theorem cov195_7 : PA.Covered 7 (OZ.Valid 7 w195.low w195.t w195.y w195.r w195.cap) (P33.root 7) :=
  Night6836Tree.sound w195 pick195 7 t2134 _ (by decide +kernel)
theorem window195 : P33.WindowCount w195 := by
  apply P33.window_count w195 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov195_1
  · exact cov195_2
  · exact cov195_3
  · exact cov195_4
  · exact cov195_5
  · exact cov195_6
  · exact cov195_7
def w196 : P33.Window := ⟨12,44,5848,5608,247491677846228122,33581,33000,5000000,81920000000⟩
def h196_0 : Height w196 := ⟨33581,33000,by decide +kernel⟩
def h196_1 : Height w196 := ⟨37583,30000,by decide +kernel⟩
def h196_2 : Height w196 := ⟨42499,27000,by decide +kernel⟩
def h196_3 : Height w196 := ⟨48941,24000,by decide +kernel⟩
def h196_4 : Height w196 := ⟨58218,21000,by decide +kernel⟩
def h196_5 : Height w196 := ⟨73733,18000,by decide +kernel⟩
def pick196 (cl : ℕ) : Height w196 := if cl<54 then (if cl<2 then (h196_0) else (if cl<12 then (h196_1) else (h196_2))) else (if cl<302 then (h196_3) else (if cl<1014 then (h196_4) else (h196_5)))
private theorem k196_1_0 : check w196 pick196 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k196_1_1 : check w196 pick196 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k196_1_2 : check w196 pick196 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w196 pick196 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k196_1_0 k196_1_1
private theorem k196_1_3 : check w196 pick196 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k196_1_4 : check w196 pick196 1 t8081 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k196_1_5 : check w196 pick196 1 t8082 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w196 pick196 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t8081 k196_1_3 k196_1_4
private theorem k196_1_6 : check w196 pick196 1 t8083 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w196 pick196 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t8082 k196_1_2 k196_1_5
private theorem k196_1_7 : check w196 pick196 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k196_1_8 : check w196 pick196 1 t8086 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k196_1_9 : check w196 pick196 1 t8087 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w196 pick196 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t7634 t8086 k196_1_7 k196_1_8
private theorem k196_1_10 : check w196 pick196 1 t8088 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k196_1_11 : check w196 pick196 1 t8090 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k196_1_12 : check w196 pick196 1 t8091 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w196 pick196 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t8088 t8090 k196_1_10 k196_1_11
private theorem k196_1_13 : check w196 pick196 1 t8092 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w196 pick196 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t8087 t8091 k196_1_9 k196_1_12
private theorem k196_1_14 : check w196 pick196 1 t8093 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w196 pick196 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8083 t8092 k196_1_6 k196_1_13
theorem cov196_1 : PA.Covered 1 (OZ.Valid 1 w196.low w196.t w196.y w196.r w196.cap) (P33.root 1) :=
  Night6836Tree.sound w196 pick196 1 t8093 _ k196_1_14
private theorem k196_2_0 : check w196 pick196 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k196_2_1 : check w196 pick196 2 t5736 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k196_2_2 : check w196 pick196 2 t5737 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w196 pick196 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5736 k196_2_0 k196_2_1
private theorem k196_2_3 : check w196 pick196 2 t4029 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k196_2_4 : check w196 pick196 2 t6161 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k196_2_5 : check w196 pick196 2 t8094 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w196 pick196 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4029 t6161 k196_2_3 k196_2_4
private theorem k196_2_6 : check w196 pick196 2 t8095 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w196 pick196 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5737 t8094 k196_2_2 k196_2_5
theorem cov196_2 : PA.Covered 2 (OZ.Valid 2 w196.low w196.t w196.y w196.r w196.cap) (P33.root 2) :=
  Night6836Tree.sound w196 pick196 2 t8095 _ k196_2_6
theorem cov196_3 : PA.Covered 3 (OZ.Valid 3 w196.low w196.t w196.y w196.r w196.cap) (P33.root 3) :=
  Night6836Tree.sound w196 pick196 3 t4877 _ (by decide +kernel)
theorem cov196_4 : PA.Covered 4 (OZ.Valid 4 w196.low w196.t w196.y w196.r w196.cap) (P33.root 4) :=
  Night6836Tree.sound w196 pick196 4 t565 _ (by decide +kernel)
theorem cov196_5 : PA.Covered 5 (OZ.Valid 5 w196.low w196.t w196.y w196.r w196.cap) (P33.root 5) :=
  Night6836Tree.sound w196 pick196 5 t566 _ (by decide +kernel)
theorem cov196_6 : PA.Covered 6 (OZ.Valid 6 w196.low w196.t w196.y w196.r w196.cap) (P33.root 6) :=
  Night6836Tree.sound w196 pick196 6 t567 _ (by decide +kernel)
theorem cov196_7 : PA.Covered 7 (OZ.Valid 7 w196.low w196.t w196.y w196.r w196.cap) (P33.root 7) :=
  Night6836Tree.sound w196 pick196 7 t2134 _ (by decide +kernel)
theorem window196 : P33.WindowCount w196 := by
  apply P33.window_count w196 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov196_1
  · exact cov196_2
  · exact cov196_3
  · exact cov196_4
  · exact cov196_5
  · exact cov196_6
  · exact cov196_7
def w197 : P33.Window := ⟨12,45,5607,5359,247468772095728753,38497,33000,5000000,81920000000⟩
def h197_0 : Height w197 := ⟨38497,33000,by decide +kernel⟩
def h197_1 : Height w197 := ⟨42944,30000,by decide +kernel⟩
def h197_2 : Height w197 := ⟨48500,27000,by decide +kernel⟩
def h197_3 : Height w197 := ⟨55933,24000,by decide +kernel⟩
def h197_4 : Height w197 := ⟨66931,21000,by decide +kernel⟩
def h197_5 : Height w197 := ⟨86047,18000,by decide +kernel⟩
def pick197 (cl : ℕ) : Height w197 := if cl<124 then (if cl<5 then (h197_0) else (if cl<27 then (h197_1) else (h197_2))) else (if cl<853 then (h197_3) else (if cl<1026 then (h197_4) else (h197_5)))
private theorem k197_1_0 : check w197 pick197 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k197_1_1 : check w197 pick197 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k197_1_2 : check w197 pick197 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w197 pick197 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k197_1_0 k197_1_1
private theorem k197_1_3 : check w197 pick197 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k197_1_4 : check w197 pick197 1 t8081 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k197_1_5 : check w197 pick197 1 t8082 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w197 pick197 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t8081 k197_1_3 k197_1_4
private theorem k197_1_6 : check w197 pick197 1 t8083 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w197 pick197 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t8082 k197_1_2 k197_1_5
private theorem k197_1_7 : check w197 pick197 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k197_1_8 : check w197 pick197 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k197_1_9 : check w197 pick197 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w197 pick197 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k197_1_7 k197_1_8
private theorem k197_1_10 : check w197 pick197 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k197_1_11 : check w197 pick197 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k197_1_12 : check w197 pick197 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w197 pick197 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k197_1_10 k197_1_11
private theorem k197_1_13 : check w197 pick197 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w197 pick197 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k197_1_9 k197_1_12
private theorem k197_1_14 : check w197 pick197 1 t8096 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w197 pick197 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8083 t7649 k197_1_6 k197_1_13
theorem cov197_1 : PA.Covered 1 (OZ.Valid 1 w197.low w197.t w197.y w197.r w197.cap) (P33.root 1) :=
  Night6836Tree.sound w197 pick197 1 t8096 _ k197_1_14
private theorem k197_2_0 : check w197 pick197 2 t5695 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k197_2_1 : check w197 pick197 2 t5699 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k197_2_2 : check w197 pick197 2 t5700 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w197 pick197 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t5695 t5699 k197_2_0 k197_2_1
private theorem k197_2_3 : check w197 pick197 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k197_2_4 : check w197 pick197 2 t8097 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k197_2_5 : check w197 pick197 2 t8098 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w197 pick197 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t8097 k197_2_3 k197_2_4
private theorem k197_2_6 : check w197 pick197 2 t8099 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w197 pick197 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5700 t8098 k197_2_2 k197_2_5
theorem cov197_2 : PA.Covered 2 (OZ.Valid 2 w197.low w197.t w197.y w197.r w197.cap) (P33.root 2) :=
  Night6836Tree.sound w197 pick197 2 t8099 _ k197_2_6
theorem cov197_3 : PA.Covered 3 (OZ.Valid 3 w197.low w197.t w197.y w197.r w197.cap) (P33.root 3) :=
  Night6836Tree.sound w197 pick197 3 t564 _ (by decide +kernel)
theorem cov197_4 : PA.Covered 4 (OZ.Valid 4 w197.low w197.t w197.y w197.r w197.cap) (P33.root 4) :=
  Night6836Tree.sound w197 pick197 4 t565 _ (by decide +kernel)
theorem cov197_5 : PA.Covered 5 (OZ.Valid 5 w197.low w197.t w197.y w197.r w197.cap) (P33.root 5) :=
  Night6836Tree.sound w197 pick197 5 t566 _ (by decide +kernel)
theorem cov197_6 : PA.Covered 6 (OZ.Valid 6 w197.low w197.t w197.y w197.r w197.cap) (P33.root 6) :=
  Night6836Tree.sound w197 pick197 6 t567 _ (by decide +kernel)
theorem cov197_7 : PA.Covered 7 (OZ.Valid 7 w197.low w197.t w197.y w197.r w197.cap) (P33.root 7) :=
  Night6836Tree.sound w197 pick197 7 t2134 _ (by decide +kernel)
theorem window197 : P33.WindowCount w197 := by
  apply P33.window_count w197 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov197_1
  · exact cov197_2
  · exact cov197_3
  · exact cov197_4
  · exact cov197_5
  · exact cov197_6
  · exact cov197_7
def w198 : P33.Window := ⟨12,46,4272,3323,244916381307319507,63220,54000,5000000,81920000000⟩
def h198_0 : Height w198 := ⟨63220,54000,by decide +kernel⟩
def h198_1 : Height w198 := ⟨67425,51000,by decide +kernel⟩
def h198_2 : Height w198 := ⟨72165,48000,by decide +kernel⟩
def h198_3 : Height w198 := ⟨77616,45000,by decide +kernel⟩
def h198_4 : Height w198 := ⟨84041,42000,by decide +kernel⟩
def h198_5 : Height w198 := ⟨91847,39000,by decide +kernel⟩
def h198_6 : Height w198 := ⟨101708,36000,by decide +kernel⟩
def h198_7 : Height w198 := ⟨114814,33000,by decide +kernel⟩
def pick198 (cl : ℕ) : Height w198 := if cl<55 then (if cl<10 then (if cl<4 then (h198_0) else (h198_1)) else (if cl<32 then (h198_2) else (h198_3))) else (if cl<431 then (if cl<200 then (h198_4) else (h198_5)) else (if cl<1006 then (h198_6) else (h198_7)))
private theorem k198_1_0 : check w198 pick198 1 t8105 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k198_1_1 : check w198 pick198 1 t8114 ⟨1,7,2,16,1,52,56,97⟩ = true := by decide +kernel
private theorem k198_1_2 : check w198 pick198 1 t8115 ⟨1,7,2,16,1,52,1,97⟩ = true := glue w198 pick198 1 ⟨1,7,2,16,1,52,1,97⟩ 3 55 t8105 t8114 k198_1_0 k198_1_1
private theorem k198_1_3 : check w198 pick198 1 t8118 ⟨1,7,2,16,1,20,98,145⟩ = true := by decide +kernel
private theorem k198_1_4 : check w198 pick198 1 t8131 ⟨1,7,2,16,21,52,98,145⟩ = true := by decide +kernel
private theorem k198_1_5 : check w198 pick198 1 t8132 ⟨1,7,2,16,1,52,98,145⟩ = true := glue w198 pick198 1 ⟨1,7,2,16,1,52,98,145⟩ 2 20 t8118 t8131 k198_1_3 k198_1_4
private theorem k198_1_6 : check w198 pick198 1 t8133 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w198 pick198 1 ⟨1,7,2,16,1,52,1,145⟩ 3 97 t8115 t8132 k198_1_2 k198_1_5
private theorem k198_1_7 : check w198 pick198 1 t8136 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k198_1_8 : check w198 pick198 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k198_1_9 : check w198 pick198 1 t8137 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w198 pick198 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t8136 t7702 k198_1_7 k198_1_8
private theorem k198_1_10 : check w198 pick198 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k198_1_11 : check w198 pick198 1 t8139 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k198_1_12 : check w198 pick198 1 t8140 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w198 pick198 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t8139 k198_1_10 k198_1_11
private theorem k198_1_13 : check w198 pick198 1 t8141 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w198 pick198 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t8137 t8140 k198_1_9 k198_1_12
private theorem k198_1_14 : check w198 pick198 1 t8142 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w198 pick198 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t8133 t8141 k198_1_6 k198_1_13
theorem cov198_1 : PA.Covered 1 (OZ.Valid 1 w198.low w198.t w198.y w198.r w198.cap) (P33.root 1) :=
  Night6836Tree.sound w198 pick198 1 t8142 _ k198_1_14
theorem cov198_2 : PA.Covered 2 (OZ.Valid 2 w198.low w198.t w198.y w198.r w198.cap) (P33.root 2) :=
  Night6836Tree.sound w198 pick198 2 t8148 _ (by decide +kernel)
theorem cov198_3 : PA.Covered 3 (OZ.Valid 3 w198.low w198.t w198.y w198.r w198.cap) (P33.root 3) :=
  Night6836Tree.sound w198 pick198 3 t564 _ (by decide +kernel)
theorem cov198_4 : PA.Covered 4 (OZ.Valid 4 w198.low w198.t w198.y w198.r w198.cap) (P33.root 4) :=
  Night6836Tree.sound w198 pick198 4 t565 _ (by decide +kernel)
theorem cov198_5 : PA.Covered 5 (OZ.Valid 5 w198.low w198.t w198.y w198.r w198.cap) (P33.root 5) :=
  Night6836Tree.sound w198 pick198 5 t566 _ (by decide +kernel)
theorem cov198_6 : PA.Covered 6 (OZ.Valid 6 w198.low w198.t w198.y w198.r w198.cap) (P33.root 6) :=
  Night6836Tree.sound w198 pick198 6 t567 _ (by decide +kernel)
theorem cov198_7 : PA.Covered 7 (OZ.Valid 7 w198.low w198.t w198.y w198.r w198.cap) (P33.root 7) :=
  Night6836Tree.sound w198 pick198 7 t2134 _ (by decide +kernel)
theorem window198 : P33.WindowCount w198 := by
  apply P33.window_count w198 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov198_1
  · exact cov198_2
  · exact cov198_3
  · exact cov198_4
  · exact cov198_5
  · exact cov198_6
  · exact cov198_7
def w199 : P33.Window := ⟨12,46,5358,5101,247072607994591505,40158,36000,5000000,81920000000⟩
def h199_0 : Height w199 := ⟨40158,36000,by decide +kernel⟩
def h199_1 : Height w199 := ⟨44315,33000,by decide +kernel⟩
def h199_2 : Height w199 := ⟨49339,30000,by decide +kernel⟩
def h199_3 : Height w199 := ⟨55735,27000,by decide +kernel⟩
def h199_4 : Height w199 := ⟨64495,24000,by decide +kernel⟩
def h199_5 : Height w199 := ⟨77861,21000,by decide +kernel⟩
def pick199 (cl : ℕ) : Height w199 := if cl<52 then (if cl<4 then (h199_0) else (if cl<14 then (h199_1) else (h199_2))) else (if cl<264 then (h199_3) else (if cl<961 then (h199_4) else (h199_5)))
private theorem k199_1_0 : check w199 pick199 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k199_1_1 : check w199 pick199 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k199_1_2 : check w199 pick199 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w199 pick199 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k199_1_0 k199_1_1
private theorem k199_1_3 : check w199 pick199 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k199_1_4 : check w199 pick199 1 t8151 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k199_1_5 : check w199 pick199 1 t8152 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w199 pick199 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t8151 k199_1_3 k199_1_4
private theorem k199_1_6 : check w199 pick199 1 t8153 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w199 pick199 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t8152 k199_1_2 k199_1_5
private theorem k199_1_7 : check w199 pick199 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k199_1_8 : check w199 pick199 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k199_1_9 : check w199 pick199 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w199 pick199 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k199_1_7 k199_1_8
private theorem k199_1_10 : check w199 pick199 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k199_1_11 : check w199 pick199 1 t8155 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k199_1_12 : check w199 pick199 1 t8156 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w199 pick199 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t8155 k199_1_10 k199_1_11
private theorem k199_1_13 : check w199 pick199 1 t8157 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w199 pick199 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t8156 k199_1_9 k199_1_12
private theorem k199_1_14 : check w199 pick199 1 t8158 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w199 pick199 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8153 t8157 k199_1_6 k199_1_13
theorem cov199_1 : PA.Covered 1 (OZ.Valid 1 w199.low w199.t w199.y w199.r w199.cap) (P33.root 1) :=
  Night6836Tree.sound w199 pick199 1 t8158 _ k199_1_14
private theorem k199_2_0 : check w199 pick199 2 t6453 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k199_2_1 : check w199 pick199 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k199_2_2 : check w199 pick199 2 t6454 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w199 pick199 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t6453 t3777 k199_2_0 k199_2_1
private theorem k199_2_3 : check w199 pick199 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k199_2_4 : check w199 pick199 2 t8097 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k199_2_5 : check w199 pick199 2 t8098 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w199 pick199 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t8097 k199_2_3 k199_2_4
private theorem k199_2_6 : check w199 pick199 2 t8159 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w199 pick199 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t6454 t8098 k199_2_2 k199_2_5
theorem cov199_2 : PA.Covered 2 (OZ.Valid 2 w199.low w199.t w199.y w199.r w199.cap) (P33.root 2) :=
  Night6836Tree.sound w199 pick199 2 t8159 _ k199_2_6
theorem cov199_3 : PA.Covered 3 (OZ.Valid 3 w199.low w199.t w199.y w199.r w199.cap) (P33.root 3) :=
  Night6836Tree.sound w199 pick199 3 t564 _ (by decide +kernel)
theorem cov199_4 : PA.Covered 4 (OZ.Valid 4 w199.low w199.t w199.y w199.r w199.cap) (P33.root 4) :=
  Night6836Tree.sound w199 pick199 4 t565 _ (by decide +kernel)
theorem cov199_5 : PA.Covered 5 (OZ.Valid 5 w199.low w199.t w199.y w199.r w199.cap) (P33.root 5) :=
  Night6836Tree.sound w199 pick199 5 t566 _ (by decide +kernel)
theorem cov199_6 : PA.Covered 6 (OZ.Valid 6 w199.low w199.t w199.y w199.r w199.cap) (P33.root 6) :=
  Night6836Tree.sound w199 pick199 6 t567 _ (by decide +kernel)
theorem cov199_7 : PA.Covered 7 (OZ.Valid 7 w199.low w199.t w199.y w199.r w199.cap) (P33.root 7) :=
  Night6836Tree.sound w199 pick199 7 t2134 _ (by decide +kernel)
theorem window199 : P33.WindowCount w199 := by
  apply P33.window_count w199 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov199_1
  · exact cov199_2
  · exact cov199_3
  · exact cov199_4
  · exact cov199_5
  · exact cov199_6
  · exact cov199_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w200 : P33.Window := ⟨12,47,5100,4832,246849586657644505,42659,39000,5000000,81920000000⟩
def h200_0 : Height w200 := ⟨42659,39000,by decide +kernel⟩
def h200_1 : Height w200 := ⟨46650,36000,by decide +kernel⟩
def h200_2 : Height w200 := ⟨51362,33000,by decide +kernel⟩
def h200_3 : Height w200 := ⟨57157,30000,by decide +kernel⟩
def h200_4 : Height w200 := ⟨64695,27000,by decide +kernel⟩
def h200_5 : Height w200 := ⟨75300,24000,by decide +kernel⟩
def h200_6 : Height w200 := ⟨92079,21000,by decide +kernel⟩
def pick200 (cl : ℕ) : Height w200 := if cl<32 then (if cl<2 then (h200_0) else (if cl<10 then (h200_1) else (h200_2))) else (if cl<853 then (if cl<136 then (h200_3) else (h200_4)) else (if cl<1021 then (h200_5) else (h200_6)))
private theorem k200_1_0 : check w200 pick200 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k200_1_1 : check w200 pick200 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k200_1_2 : check w200 pick200 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w200 pick200 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k200_1_0 k200_1_1
private theorem k200_1_3 : check w200 pick200 1 t8168 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k200_1_4 : check w200 pick200 1 t8180 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k200_1_5 : check w200 pick200 1 t8181 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w200 pick200 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t8168 t8180 k200_1_3 k200_1_4
private theorem k200_1_6 : check w200 pick200 1 t8182 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w200 pick200 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t7662 t8181 k200_1_2 k200_1_5
private theorem k200_1_7 : check w200 pick200 1 t8186 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k200_1_8 : check w200 pick200 1 t8063 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k200_1_9 : check w200 pick200 1 t8187 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w200 pick200 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t8186 t8063 k200_1_7 k200_1_8
private theorem k200_1_10 : check w200 pick200 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k200_1_11 : check w200 pick200 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k200_1_12 : check w200 pick200 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w200 pick200 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k200_1_10 k200_1_11
private theorem k200_1_13 : check w200 pick200 1 t8188 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w200 pick200 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t8187 t7648 k200_1_9 k200_1_12
private theorem k200_1_14 : check w200 pick200 1 t8189 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w200 pick200 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8182 t8188 k200_1_6 k200_1_13
theorem cov200_1 : PA.Covered 1 (OZ.Valid 1 w200.low w200.t w200.y w200.r w200.cap) (P33.root 1) :=
  Night6836Tree.sound w200 pick200 1 t8189 _ k200_1_14
private theorem k200_2_0 : check w200 pick200 2 t8196 ⟨2,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k200_2_1 : check w200 pick200 2 t8204 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k200_2_2 : check w200 pick200 2 t8205 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w200 pick200 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t8196 t8204 k200_2_0 k200_2_1
theorem cov200_2 : PA.Covered 2 (OZ.Valid 2 w200.low w200.t w200.y w200.r w200.cap) (P33.root 2) :=
  Night6836Tree.sound w200 pick200 2 t8205 _ k200_2_2
theorem cov200_3 : PA.Covered 3 (OZ.Valid 3 w200.low w200.t w200.y w200.r w200.cap) (P33.root 3) :=
  Night6836Tree.sound w200 pick200 3 t564 _ (by decide +kernel)
theorem cov200_4 : PA.Covered 4 (OZ.Valid 4 w200.low w200.t w200.y w200.r w200.cap) (P33.root 4) :=
  Night6836Tree.sound w200 pick200 4 t565 _ (by decide +kernel)
theorem cov200_5 : PA.Covered 5 (OZ.Valid 5 w200.low w200.t w200.y w200.r w200.cap) (P33.root 5) :=
  Night6836Tree.sound w200 pick200 5 t566 _ (by decide +kernel)
theorem cov200_6 : PA.Covered 6 (OZ.Valid 6 w200.low w200.t w200.y w200.r w200.cap) (P33.root 6) :=
  Night6836Tree.sound w200 pick200 6 t567 _ (by decide +kernel)
theorem cov200_7 : PA.Covered 7 (OZ.Valid 7 w200.low w200.t w200.y w200.r w200.cap) (P33.root 7) :=
  Night6836Tree.sound w200 pick200 7 t2134 _ (by decide +kernel)
theorem window200 : P33.WindowCount w200 := by
  apply P33.window_count w200 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov200_1
  · exact cov200_2
  · exact cov200_3
  · exact cov200_4
  · exact cov200_5
  · exact cov200_6
  · exact cov200_7
def w201 : P33.Window := ⟨12,48,4831,4554,246372789798196341,46094,42000,5000000,81920000000⟩
def h201_0 : Height w201 := ⟨46094,42000,by decide +kernel⟩
def h201_1 : Height w201 := ⟨50012,39000,by decide +kernel⟩
def h201_2 : Height w201 := ⟨54560,36000,by decide +kernel⟩
def h201_3 : Height w201 := ⟨60021,33000,by decide +kernel⟩
def h201_4 : Height w201 := ⟨66875,30000,by decide +kernel⟩
def h201_5 : Height w201 := ⟨76010,27000,by decide +kernel⟩
def h201_6 : Height w201 := ⟨89270,24000,by decide +kernel⟩
def pick201 (cl : ℕ) : Height w201 := if cl<32 then (if cl<2 then (h201_0) else (if cl<6 then (h201_1) else (h201_2))) else (if cl<302 then (if cl<83 then (h201_3) else (h201_4)) else (if cl<961 then (h201_5) else (h201_6)))
private theorem k201_1_0 : check w201 pick201 1 t8206 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k201_1_1 : check w201 pick201 1 t8208 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k201_1_2 : check w201 pick201 1 t8209 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w201 pick201 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t8206 t8208 k201_1_0 k201_1_1
private theorem k201_1_3 : check w201 pick201 1 t8212 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k201_1_4 : check w201 pick201 1 t8151 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k201_1_5 : check w201 pick201 1 t8213 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w201 pick201 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t8212 t8151 k201_1_3 k201_1_4
private theorem k201_1_6 : check w201 pick201 1 t8214 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w201 pick201 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8209 t8213 k201_1_2 k201_1_5
private theorem k201_1_7 : check w201 pick201 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k201_1_8 : check w201 pick201 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k201_1_9 : check w201 pick201 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w201 pick201 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k201_1_7 k201_1_8
private theorem k201_1_10 : check w201 pick201 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k201_1_11 : check w201 pick201 1 t8155 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k201_1_12 : check w201 pick201 1 t8156 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w201 pick201 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t8155 k201_1_10 k201_1_11
private theorem k201_1_13 : check w201 pick201 1 t8157 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w201 pick201 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t8156 k201_1_9 k201_1_12
private theorem k201_1_14 : check w201 pick201 1 t8215 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w201 pick201 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8214 t8157 k201_1_6 k201_1_13
theorem cov201_1 : PA.Covered 1 (OZ.Valid 1 w201.low w201.t w201.y w201.r w201.cap) (P33.root 1) :=
  Night6836Tree.sound w201 pick201 1 t8215 _ k201_1_14
private theorem k201_2_0 : check w201 pick201 2 t5566 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k201_2_1 : check w201 pick201 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k201_2_2 : check w201 pick201 2 t8216 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w201 pick201 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5566 t3303 k201_2_0 k201_2_1
theorem cov201_2 : PA.Covered 2 (OZ.Valid 2 w201.low w201.t w201.y w201.r w201.cap) (P33.root 2) :=
  Night6836Tree.sound w201 pick201 2 t8216 _ k201_2_2
theorem cov201_3 : PA.Covered 3 (OZ.Valid 3 w201.low w201.t w201.y w201.r w201.cap) (P33.root 3) :=
  Night6836Tree.sound w201 pick201 3 t564 _ (by decide +kernel)
theorem cov201_4 : PA.Covered 4 (OZ.Valid 4 w201.low w201.t w201.y w201.r w201.cap) (P33.root 4) :=
  Night6836Tree.sound w201 pick201 4 t565 _ (by decide +kernel)
theorem cov201_5 : PA.Covered 5 (OZ.Valid 5 w201.low w201.t w201.y w201.r w201.cap) (P33.root 5) :=
  Night6836Tree.sound w201 pick201 5 t566 _ (by decide +kernel)
theorem cov201_6 : PA.Covered 6 (OZ.Valid 6 w201.low w201.t w201.y w201.r w201.cap) (P33.root 6) :=
  Night6836Tree.sound w201 pick201 6 t567 _ (by decide +kernel)
theorem cov201_7 : PA.Covered 7 (OZ.Valid 7 w201.low w201.t w201.y w201.r w201.cap) (P33.root 7) :=
  Night6836Tree.sound w201 pick201 7 t2134 _ (by decide +kernel)
theorem window201 : P33.WindowCount w201 := by
  apply P33.window_count w201 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov201_1
  · exact cov201_2
  · exact cov201_3
  · exact cov201_4
  · exact cov201_5
  · exact cov201_6
  · exact cov201_7
def w202 : P33.Window := ⟨12,49,4553,3650,245909714802462961,61243,51000,5000000,81920000000⟩
def h202_0 : Height w202 := ⟨61243,51000,by decide +kernel⟩
def h202_1 : Height w202 := ⟨65362,48000,by decide +kernel⟩
def h202_2 : Height w202 := ⟨70024,45000,by decide +kernel⟩
def h202_3 : Height w202 := ⟨75419,42000,by decide +kernel⟩
def h202_4 : Height w202 := ⟨81834,39000,by decide +kernel⟩
def h202_5 : Height w202 := ⟨89728,36000,by decide +kernel⟩
def h202_6 : Height w202 := ⟨99880,33000,by decide +kernel⟩
def h202_7 : Height w202 := ⟨113736,30000,by decide +kernel⟩
def pick202 (cl : ℕ) : Height w202 := if cl<55 then (if cl<6 then (if cl<3 then (h202_0) else (h202_1)) else (if cl<32 then (h202_2) else (h202_3))) else (if cl<561 then (if cl<167 then (h202_4) else (h202_5)) else (if cl<981 then (h202_6) else (h202_7)))
private theorem k202_1_0 : check w202 pick202 1 t8224 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k202_1_1 : check w202 pick202 1 t8230 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k202_1_2 : check w202 pick202 1 t8231 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w202 pick202 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t8224 t8230 k202_1_0 k202_1_1
private theorem k202_1_3 : check w202 pick202 1 t8232 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k202_1_4 : check w202 pick202 1 t7694 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k202_1_5 : check w202 pick202 1 t8233 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w202 pick202 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t8232 t7694 k202_1_3 k202_1_4
private theorem k202_1_6 : check w202 pick202 1 t8234 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w202 pick202 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8231 t8233 k202_1_2 k202_1_5
private theorem k202_1_7 : check w202 pick202 1 t8240 ⟨1,7,2,16,1,52,139,179⟩ = true := by decide +kernel
private theorem k202_1_8 : check w202 pick202 1 t8241 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k202_1_9 : check w202 pick202 1 t8242 ⟨1,7,2,16,1,52,139,206⟩ = true := glue w202 pick202 1 ⟨1,7,2,16,1,52,139,206⟩ 3 179 t8240 t8241 k202_1_7 k202_1_8
private theorem k202_1_10 : check w202 pick202 1 t8243 ⟨1,7,2,16,1,52,207,247⟩ = true := by decide +kernel
private theorem k202_1_11 : check w202 pick202 1 t8248 ⟨1,7,2,16,1,52,248,450⟩ = true := by decide +kernel
private theorem k202_1_12 : check w202 pick202 1 t8249 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w202 pick202 1 ⟨1,7,2,16,1,52,207,450⟩ 3 247 t8243 t8248 k202_1_10 k202_1_11
private theorem k202_1_13 : check w202 pick202 1 t8250 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w202 pick202 1 ⟨1,7,2,16,1,52,139,450⟩ 3 206 t8242 t8249 k202_1_9 k202_1_12
private theorem k202_1_14 : check w202 pick202 1 t8251 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w202 pick202 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8234 t8250 k202_1_6 k202_1_13
theorem cov202_1 : PA.Covered 1 (OZ.Valid 1 w202.low w202.t w202.y w202.r w202.cap) (P33.root 1) :=
  Night6836Tree.sound w202 pick202 1 t8251 _ k202_1_14
private theorem k202_2_0 : check w202 pick202 2 t6505 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k202_2_1 : check w202 pick202 2 t8252 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k202_2_2 : check w202 pick202 2 t8253 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w202 pick202 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t6505 t8252 k202_2_0 k202_2_1
theorem cov202_2 : PA.Covered 2 (OZ.Valid 2 w202.low w202.t w202.y w202.r w202.cap) (P33.root 2) :=
  Night6836Tree.sound w202 pick202 2 t8253 _ k202_2_2
theorem cov202_3 : PA.Covered 3 (OZ.Valid 3 w202.low w202.t w202.y w202.r w202.cap) (P33.root 3) :=
  Night6836Tree.sound w202 pick202 3 t564 _ (by decide +kernel)
theorem cov202_4 : PA.Covered 4 (OZ.Valid 4 w202.low w202.t w202.y w202.r w202.cap) (P33.root 4) :=
  Night6836Tree.sound w202 pick202 4 t565 _ (by decide +kernel)
theorem cov202_5 : PA.Covered 5 (OZ.Valid 5 w202.low w202.t w202.y w202.r w202.cap) (P33.root 5) :=
  Night6836Tree.sound w202 pick202 5 t566 _ (by decide +kernel)
theorem cov202_6 : PA.Covered 6 (OZ.Valid 6 w202.low w202.t w202.y w202.r w202.cap) (P33.root 6) :=
  Night6836Tree.sound w202 pick202 6 t567 _ (by decide +kernel)
theorem cov202_7 : PA.Covered 7 (OZ.Valid 7 w202.low w202.t w202.y w202.r w202.cap) (P33.root 7) :=
  Night6836Tree.sound w202 pick202 7 t2134 _ (by decide +kernel)
theorem window202 : P33.WindowCount w202 := by
  apply P33.window_count w202 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov202_1
  · exact cov202_2
  · exact cov202_3
  · exact cov202_4
  · exact cov202_5
  · exact cov202_6
  · exact cov202_7
def w203 : P33.Window := ⟨12,50,4263,3963,246330056565796716,56942,48000,5000000,81920000000⟩
def h203_0 : Height w203 := ⟨56942,48000,by decide +kernel⟩
def h203_1 : Height w203 := ⟨60973,45000,by decide +kernel⟩
def h203_2 : Height w203 := ⟨65563,42000,by decide +kernel⟩
def h203_3 : Height w203 := ⟨70920,39000,by decide +kernel⟩
def h203_4 : Height w203 := ⟨77371,36000,by decide +kernel⟩
def h203_5 : Height w203 := ⟨85454,33000,by decide +kernel⟩
def h203_6 : Height w203 := ⟨96133,30000,by decide +kernel⟩
def pick203 (cl : ℕ) : Height w203 := if cl<32 then (if cl<2 then (h203_0) else (if cl<6 then (h203_1) else (h203_2))) else (if cl<196 then (if cl<55 then (h203_3) else (h203_4)) else (if cl<989 then (h203_5) else (h203_6)))
private theorem k203_1_0 : check w203 pick203 1 t7686 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k203_1_1 : check w203 pick203 1 t2318 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k203_1_2 : check w203 pick203 1 t7687 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w203 pick203 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7686 t2318 k203_1_0 k203_1_1
private theorem k203_1_3 : check w203 pick203 1 t8254 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k203_1_4 : check w203 pick203 1 t8257 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k203_1_5 : check w203 pick203 1 t8258 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w203 pick203 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t8254 t8257 k203_1_3 k203_1_4
private theorem k203_1_6 : check w203 pick203 1 t8259 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w203 pick203 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t7687 t8258 k203_1_2 k203_1_5
private theorem k203_1_7 : check w203 pick203 1 t7701 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k203_1_8 : check w203 pick203 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k203_1_9 : check w203 pick203 1 t7703 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w203 pick203 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7701 t7702 k203_1_7 k203_1_8
private theorem k203_1_10 : check w203 pick203 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k203_1_11 : check w203 pick203 1 t8261 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k203_1_12 : check w203 pick203 1 t8262 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w203 pick203 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t8261 k203_1_10 k203_1_11
private theorem k203_1_13 : check w203 pick203 1 t8263 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w203 pick203 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7703 t8262 k203_1_9 k203_1_12
private theorem k203_1_14 : check w203 pick203 1 t8264 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w203 pick203 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8259 t8263 k203_1_6 k203_1_13
theorem cov203_1 : PA.Covered 1 (OZ.Valid 1 w203.low w203.t w203.y w203.r w203.cap) (P33.root 1) :=
  Night6836Tree.sound w203 pick203 1 t8264 _ k203_1_14
private theorem k203_2_0 : check w203 pick203 2 t6236 ⟨2,7,4,16,2,52,2,166⟩ = true := by decide +kernel
private theorem k203_2_1 : check w203 pick203 2 t5204 ⟨2,7,4,16,2,52,167,450⟩ = true := by decide +kernel
private theorem k203_2_2 : check w203 pick203 2 t6237 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w203 pick203 2 ⟨2,7,4,16,0,52,0,450⟩ 3 166 t6236 t5204 k203_2_0 k203_2_1
theorem cov203_2 : PA.Covered 2 (OZ.Valid 2 w203.low w203.t w203.y w203.r w203.cap) (P33.root 2) :=
  Night6836Tree.sound w203 pick203 2 t6237 _ k203_2_2
theorem cov203_3 : PA.Covered 3 (OZ.Valid 3 w203.low w203.t w203.y w203.r w203.cap) (P33.root 3) :=
  Night6836Tree.sound w203 pick203 3 t564 _ (by decide +kernel)
theorem cov203_4 : PA.Covered 4 (OZ.Valid 4 w203.low w203.t w203.y w203.r w203.cap) (P33.root 4) :=
  Night6836Tree.sound w203 pick203 4 t565 _ (by decide +kernel)
theorem cov203_5 : PA.Covered 5 (OZ.Valid 5 w203.low w203.t w203.y w203.r w203.cap) (P33.root 5) :=
  Night6836Tree.sound w203 pick203 5 t566 _ (by decide +kernel)
theorem cov203_6 : PA.Covered 6 (OZ.Valid 6 w203.low w203.t w203.y w203.r w203.cap) (P33.root 6) :=
  Night6836Tree.sound w203 pick203 6 t567 _ (by decide +kernel)
theorem cov203_7 : PA.Covered 7 (OZ.Valid 7 w203.low w203.t w203.y w203.r w203.cap) (P33.root 7) :=
  Night6836Tree.sound w203 pick203 7 t2134 _ (by decide +kernel)
theorem window203 : P33.WindowCount w203 := by
  apply P33.window_count w203 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov203_1
  · exact cov203_2
  · exact cov203_3
  · exact cov203_4
  · exact cov203_5
  · exact cov203_6
  · exact cov203_7
def w204 : P33.Window := ⟨12,51,3962,3650,246354869173520490,65261,51000,5000000,81920000000⟩
def h204_0 : Height w204 := ⟨65261,51000,by decide +kernel⟩
def h204_1 : Height w204 := ⟨69499,48000,by decide +kernel⟩
def h204_2 : Height w204 := ⟨74305,45000,by decide +kernel⟩
def h204_3 : Height w204 := ⟨79877,42000,by decide +kernel⟩
def h204_4 : Height w204 := ⟨86513,39000,by decide +kernel⟩
def h204_5 : Height w204 := ⟨94693,36000,by decide +kernel⟩
def h204_6 : Height w204 := ⟨119630,30000,by decide +kernel⟩
def pick204 (cl : ℕ) : Height w204 := if cl<32 then (if cl<4 then (h204_0) else (if cl<10 then (h204_1) else (h204_2))) else (if cl<204 then (if cl<70 then (h204_3) else (h204_4)) else (if cl<989 then (h204_5) else (h204_6)))
private theorem k204_1_0 : check w204 pick204 1 t8105 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k204_1_1 : check w204 pick204 1 t8277 ⟨1,7,2,16,1,52,56,90⟩ = true := by decide +kernel
private theorem k204_1_2 : check w204 pick204 1 t8278 ⟨1,7,2,16,1,52,1,90⟩ = true := glue w204 pick204 1 ⟨1,7,2,16,1,52,1,90⟩ 3 55 t8105 t8277 k204_1_0 k204_1_1
private theorem k204_1_3 : check w204 pick204 1 t8287 ⟨1,7,2,16,1,52,91,117⟩ = true := by decide +kernel
private theorem k204_1_4 : check w204 pick204 1 t8296 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k204_1_5 : check w204 pick204 1 t8297 ⟨1,7,2,16,1,52,91,145⟩ = true := glue w204 pick204 1 ⟨1,7,2,16,1,52,91,145⟩ 3 117 t8287 t8296 k204_1_3 k204_1_4
private theorem k204_1_6 : check w204 pick204 1 t8298 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w204 pick204 1 ⟨1,7,2,16,1,52,1,145⟩ 3 90 t8278 t8297 k204_1_2 k204_1_5
private theorem k204_1_7 : check w204 pick204 1 t8136 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k204_1_8 : check w204 pick204 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k204_1_9 : check w204 pick204 1 t8137 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w204 pick204 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t8136 t7702 k204_1_7 k204_1_8
private theorem k204_1_10 : check w204 pick204 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k204_1_11 : check w204 pick204 1 t8261 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k204_1_12 : check w204 pick204 1 t8262 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w204 pick204 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t8261 k204_1_10 k204_1_11
private theorem k204_1_13 : check w204 pick204 1 t8299 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w204 pick204 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t8137 t8262 k204_1_9 k204_1_12
private theorem k204_1_14 : check w204 pick204 1 t8300 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w204 pick204 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t8298 t8299 k204_1_6 k204_1_13
theorem cov204_1 : PA.Covered 1 (OZ.Valid 1 w204.low w204.t w204.y w204.r w204.cap) (P33.root 1) :=
  Night6836Tree.sound w204 pick204 1 t8300 _ k204_1_14
theorem cov204_2 : PA.Covered 2 (OZ.Valid 2 w204.low w204.t w204.y w204.r w204.cap) (P33.root 2) :=
  Night6836Tree.sound w204 pick204 2 t8301 _ (by decide +kernel)
theorem cov204_3 : PA.Covered 3 (OZ.Valid 3 w204.low w204.t w204.y w204.r w204.cap) (P33.root 3) :=
  Night6836Tree.sound w204 pick204 3 t564 _ (by decide +kernel)
theorem cov204_4 : PA.Covered 4 (OZ.Valid 4 w204.low w204.t w204.y w204.r w204.cap) (P33.root 4) :=
  Night6836Tree.sound w204 pick204 4 t565 _ (by decide +kernel)
theorem cov204_5 : PA.Covered 5 (OZ.Valid 5 w204.low w204.t w204.y w204.r w204.cap) (P33.root 5) :=
  Night6836Tree.sound w204 pick204 5 t566 _ (by decide +kernel)
theorem cov204_6 : PA.Covered 6 (OZ.Valid 6 w204.low w204.t w204.y w204.r w204.cap) (P33.root 6) :=
  Night6836Tree.sound w204 pick204 6 t567 _ (by decide +kernel)
theorem cov204_7 : PA.Covered 7 (OZ.Valid 7 w204.low w204.t w204.y w204.r w204.cap) (P33.root 7) :=
  Night6836Tree.sound w204 pick204 7 t2134 _ (by decide +kernel)
theorem window204 : P33.WindowCount w204 := by
  apply P33.window_count w204 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov204_1
  · exact cov204_2
  · exact cov204_3
  · exact cov204_4
  · exact cov204_5
  · exact cov204_6
  · exact cov204_7
def w205 : P33.Window := ⟨12,52,3649,3323,245389514769660139,72562,57000,5000000,81920000000⟩
def h205_0 : Height w205 := ⟨72562,57000,by decide +kernel⟩
def h205_1 : Height w205 := ⟨76689,54000,by decide +kernel⟩
def h205_2 : Height w205 := ⟨81288,51000,by decide +kernel⟩
def h205_3 : Height w205 := ⟨86500,48000,by decide +kernel⟩
def h205_4 : Height w205 := ⟨92524,45000,by decide +kernel⟩
def h205_5 : Height w205 := ⟨99660,42000,by decide +kernel⟩
def h205_6 : Height w205 := ⟨108373,39000,by decide +kernel⟩
def pick205 (cl : ℕ) : Height w205 := if cl<32 then (if cl<3 then (h205_0) else (if cl<6 then (h205_1) else (h205_2))) else (if cl<105 then (if cl<40 then (h205_3) else (h205_4)) else (if cl<302 then (h205_5) else (h205_6)))
private theorem k205_1_0 : check w205 pick205 1 t8304 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k205_1_1 : check w205 pick205 1 t8313 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k205_1_2 : check w205 pick205 1 t8314 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w205 pick205 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8304 t8313 k205_1_0 k205_1_1
private theorem k205_1_3 : check w205 pick205 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k205_1_4 : check w205 pick205 1 t8321 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k205_1_5 : check w205 pick205 1 t8322 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w205 pick205 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t8321 k205_1_3 k205_1_4
private theorem k205_1_6 : check w205 pick205 1 t8323 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w205 pick205 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8314 t8322 k205_1_2 k205_1_5
theorem cov205_1 : PA.Covered 1 (OZ.Valid 1 w205.low w205.t w205.y w205.r w205.cap) (P33.root 1) :=
  Night6836Tree.sound w205 pick205 1 t8323 _ k205_1_6
theorem cov205_2 : PA.Covered 2 (OZ.Valid 2 w205.low w205.t w205.y w205.r w205.cap) (P33.root 2) :=
  Night6836Tree.sound w205 pick205 2 t8328 _ (by decide +kernel)
theorem cov205_3 : PA.Covered 3 (OZ.Valid 3 w205.low w205.t w205.y w205.r w205.cap) (P33.root 3) :=
  Night6836Tree.sound w205 pick205 3 t564 _ (by decide +kernel)
theorem cov205_4 : PA.Covered 4 (OZ.Valid 4 w205.low w205.t w205.y w205.r w205.cap) (P33.root 4) :=
  Night6836Tree.sound w205 pick205 4 t565 _ (by decide +kernel)
theorem cov205_5 : PA.Covered 5 (OZ.Valid 5 w205.low w205.t w205.y w205.r w205.cap) (P33.root 5) :=
  Night6836Tree.sound w205 pick205 5 t566 _ (by decide +kernel)
theorem cov205_6 : PA.Covered 6 (OZ.Valid 6 w205.low w205.t w205.y w205.r w205.cap) (P33.root 6) :=
  Night6836Tree.sound w205 pick205 6 t567 _ (by decide +kernel)
theorem cov205_7 : PA.Covered 7 (OZ.Valid 7 w205.low w205.t w205.y w205.r w205.cap) (P33.root 7) :=
  Night6836Tree.sound w205 pick205 7 t2134 _ (by decide +kernel)
theorem window205 : P33.WindowCount w205 := by
  apply P33.window_count w205 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov205_1
  · exact cov205_2
  · exact cov205_3
  · exact cov205_4
  · exact cov205_5
  · exact cov205_6
  · exact cov205_7
def w206 : P33.Window := ⟨12,53,3322,2983,244428351087420282,83899,63000,5000000,81920000000⟩
def h206_0 : Height w206 := ⟨83899,63000,by decide +kernel⟩
def h206_1 : Height w206 := ⟨88116,60000,by decide +kernel⟩
def h206_2 : Height w206 := ⟨92770,57000,by decide +kernel⟩
def h206_3 : Height w206 := ⟨97973,54000,by decide +kernel⟩
def h206_4 : Height w206 := ⟨103882,51000,by decide +kernel⟩
def h206_5 : Height w206 := ⟨110719,48000,by decide +kernel⟩
def h206_6 : Height w206 := ⟨118813,45000,by decide +kernel⟩
def h206_7 : Height w206 := ⟨128660,42000,by decide +kernel⟩
def pick206 (cl : ℕ) : Height w206 := if cl<36 then (if cl<6 then (if cl<4 then (h206_0) else (h206_1)) else (if cl<32 then (h206_2) else (h206_3))) else (if cl<312 then (if cl<83 then (h206_4) else (h206_5)) else (if cl<431 then (h206_6) else (h206_7)))
private theorem k206_1_0 : check w206 pick206 1 t8331 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k206_1_1 : check w206 pick206 1 t8335 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k206_1_2 : check w206 pick206 1 t8336 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w206 pick206 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8331 t8335 k206_1_0 k206_1_1
private theorem k206_1_3 : check w206 pick206 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k206_1_4 : check w206 pick206 1 t8338 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k206_1_5 : check w206 pick206 1 t8339 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w206 pick206 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8338 k206_1_3 k206_1_4
private theorem k206_1_6 : check w206 pick206 1 t8340 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w206 pick206 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8336 t8339 k206_1_2 k206_1_5
theorem cov206_1 : PA.Covered 1 (OZ.Valid 1 w206.low w206.t w206.y w206.r w206.cap) (P33.root 1) :=
  Night6836Tree.sound w206 pick206 1 t8340 _ k206_1_6
theorem cov206_2 : PA.Covered 2 (OZ.Valid 2 w206.low w206.t w206.y w206.r w206.cap) (P33.root 2) :=
  Night6836Tree.sound w206 pick206 2 t6560 _ (by decide +kernel)
theorem cov206_3 : PA.Covered 3 (OZ.Valid 3 w206.low w206.t w206.y w206.r w206.cap) (P33.root 3) :=
  Night6836Tree.sound w206 pick206 3 t564 _ (by decide +kernel)
theorem cov206_4 : PA.Covered 4 (OZ.Valid 4 w206.low w206.t w206.y w206.r w206.cap) (P33.root 4) :=
  Night6836Tree.sound w206 pick206 4 t565 _ (by decide +kernel)
theorem cov206_5 : PA.Covered 5 (OZ.Valid 5 w206.low w206.t w206.y w206.r w206.cap) (P33.root 5) :=
  Night6836Tree.sound w206 pick206 5 t566 _ (by decide +kernel)
theorem cov206_6 : PA.Covered 6 (OZ.Valid 6 w206.low w206.t w206.y w206.r w206.cap) (P33.root 6) :=
  Night6836Tree.sound w206 pick206 6 t567 _ (by decide +kernel)
theorem cov206_7 : PA.Covered 7 (OZ.Valid 7 w206.low w206.t w206.y w206.r w206.cap) (P33.root 7) :=
  Night6836Tree.sound w206 pick206 7 t2134 _ (by decide +kernel)
theorem window206 : P33.WindowCount w206 := by
  apply P33.window_count w206 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov206_1
  · exact cov206_2
  · exact cov206_3
  · exact cov206_4
  · exact cov206_5
  · exact cov206_6
  · exact cov206_7
def w207 : P33.Window := ⟨12,54,2982,2628,242182602090321664,97291,72000,5000000,81920000000⟩
def h207_0 : Height w207 := ⟨97291,72000,by decide +kernel⟩
def h207_1 : Height w207 := ⟨101476,69000,by decide +kernel⟩
def h207_2 : Height w207 := ⟨106029,66000,by decide +kernel⟩
def h207_3 : Height w207 := ⟨111031,63000,by decide +kernel⟩
def h207_4 : Height w207 := ⟨116586,60000,by decide +kernel⟩
def h207_5 : Height w207 := ⟨122838,57000,by decide +kernel⟩
def h207_6 : Height w207 := ⟨129982,54000,by decide +kernel⟩
def h207_7 : Height w207 := ⟨138293,51000,by decide +kernel⟩
def h207_8 : Height w207 := ⟨148175,48000,by decide +kernel⟩
def pick207 (cl : ℕ) : Height w207 := if cl<32 then (if cl<6 then (if cl<4 then (h207_0) else (h207_1)) else (if cl<14 then (h207_2) else (h207_3))) else (if cl<105 then (if cl<46 then (h207_4) else (h207_5)) else (if cl<312 then (h207_6) else (if cl<431 then (h207_7) else (h207_8))))
private theorem k207_1_0 : check w207 pick207 1 t8351 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k207_1_1 : check w207 pick207 1 t8359 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k207_1_2 : check w207 pick207 1 t8360 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w207 pick207 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t8351 t8359 k207_1_0 k207_1_1
private theorem k207_1_3 : check w207 pick207 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k207_1_4 : check w207 pick207 1 t8338 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k207_1_5 : check w207 pick207 1 t8339 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w207 pick207 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8338 k207_1_3 k207_1_4
private theorem k207_1_6 : check w207 pick207 1 t8361 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w207 pick207 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8360 t8339 k207_1_2 k207_1_5
theorem cov207_1 : PA.Covered 1 (OZ.Valid 1 w207.low w207.t w207.y w207.r w207.cap) (P33.root 1) :=
  Night6836Tree.sound w207 pick207 1 t8361 _ k207_1_6
theorem cov207_2 : PA.Covered 2 (OZ.Valid 2 w207.low w207.t w207.y w207.r w207.cap) (P33.root 2) :=
  Night6836Tree.sound w207 pick207 2 t6560 _ (by decide +kernel)
theorem cov207_3 : PA.Covered 3 (OZ.Valid 3 w207.low w207.t w207.y w207.r w207.cap) (P33.root 3) :=
  Night6836Tree.sound w207 pick207 3 t564 _ (by decide +kernel)
theorem cov207_4 : PA.Covered 4 (OZ.Valid 4 w207.low w207.t w207.y w207.r w207.cap) (P33.root 4) :=
  Night6836Tree.sound w207 pick207 4 t565 _ (by decide +kernel)
theorem cov207_5 : PA.Covered 5 (OZ.Valid 5 w207.low w207.t w207.y w207.r w207.cap) (P33.root 5) :=
  Night6836Tree.sound w207 pick207 5 t566 _ (by decide +kernel)
theorem cov207_6 : PA.Covered 6 (OZ.Valid 6 w207.low w207.t w207.y w207.r w207.cap) (P33.root 6) :=
  Night6836Tree.sound w207 pick207 6 t567 _ (by decide +kernel)
theorem cov207_7 : PA.Covered 7 (OZ.Valid 7 w207.low w207.t w207.y w207.r w207.cap) (P33.root 7) :=
  Night6836Tree.sound w207 pick207 7 t2134 _ (by decide +kernel)
theorem window207 : P33.WindowCount w207 := by
  apply P33.window_count w207 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov207_1
  · exact cov207_2
  · exact cov207_3
  · exact cov207_4
  · exact cov207_5
  · exact cov207_6
  · exact cov207_7
def w208 : P33.Window := ⟨12,55,2627,2259,226405637576545326,112065,87000,5000000,81920000000⟩
def h208_0 : Height w208 := ⟨112065,87000,by decide +kernel⟩
def h208_1 : Height w208 := ⟨115984,84000,by decide +kernel⟩
def h208_2 : Height w208 := ⟨120165,81000,by decide +kernel⟩
def h208_3 : Height w208 := ⟨124653,78000,by decide +kernel⟩
def h208_4 : Height w208 := ⟨129504,75000,by decide +kernel⟩
def h208_5 : Height w208 := ⟨140594,69000,by decide +kernel⟩
def h208_6 : Height w208 := ⟨147038,66000,by decide +kernel⟩
def h208_7 : Height w208 := ⟨154273,63000,by decide +kernel⟩
def h208_8 : Height w208 := ⟨162502,60000,by decide +kernel⟩
def h208_9 : Height w208 := ⟨172008,57000,by decide +kernel⟩
def pick208 (cl : ℕ) : Height w208 := if cl<32 then (if cl<4 then (if cl<2 then (h208_0) else (h208_1)) else (if cl<5 then (h208_2) else (if cl<13 then (h208_3) else (h208_4)))) else (if cl<107 then (if cl<55 then (h208_5) else (h208_6)) else (if cl<312 then (h208_7) else (if cl<317 then (h208_8) else (h208_9))))
private theorem k208_1_0 : check w208 pick208 1 t8364 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k208_1_1 : check w208 pick208 1 t8359 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k208_1_2 : check w208 pick208 1 t8365 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w208 pick208 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t8364 t8359 k208_1_0 k208_1_1
private theorem k208_1_3 : check w208 pick208 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k208_1_4 : check w208 pick208 1 t8368 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k208_1_5 : check w208 pick208 1 t8369 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w208 pick208 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8368 k208_1_3 k208_1_4
private theorem k208_1_6 : check w208 pick208 1 t8370 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w208 pick208 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8365 t8369 k208_1_2 k208_1_5
theorem cov208_1 : PA.Covered 1 (OZ.Valid 1 w208.low w208.t w208.y w208.r w208.cap) (P33.root 1) :=
  Night6836Tree.sound w208 pick208 1 t8370 _ k208_1_6
theorem cov208_2 : PA.Covered 2 (OZ.Valid 2 w208.low w208.t w208.y w208.r w208.cap) (P33.root 2) :=
  Night6836Tree.sound w208 pick208 2 t6560 _ (by decide +kernel)
theorem cov208_3 : PA.Covered 3 (OZ.Valid 3 w208.low w208.t w208.y w208.r w208.cap) (P33.root 3) :=
  Night6836Tree.sound w208 pick208 3 t564 _ (by decide +kernel)
theorem cov208_4 : PA.Covered 4 (OZ.Valid 4 w208.low w208.t w208.y w208.r w208.cap) (P33.root 4) :=
  Night6836Tree.sound w208 pick208 4 t565 _ (by decide +kernel)
theorem cov208_5 : PA.Covered 5 (OZ.Valid 5 w208.low w208.t w208.y w208.r w208.cap) (P33.root 5) :=
  Night6836Tree.sound w208 pick208 5 t566 _ (by decide +kernel)
theorem cov208_6 : PA.Covered 6 (OZ.Valid 6 w208.low w208.t w208.y w208.r w208.cap) (P33.root 6) :=
  Night6836Tree.sound w208 pick208 6 t567 _ (by decide +kernel)
theorem cov208_7 : PA.Covered 7 (OZ.Valid 7 w208.low w208.t w208.y w208.r w208.cap) (P33.root 7) :=
  Night6836Tree.sound w208 pick208 7 t2134 _ (by decide +kernel)
theorem window208 : P33.WindowCount w208 := by
  apply P33.window_count w208 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov208_1
  · exact cov208_2
  · exact cov208_3
  · exact cov208_4
  · exact cov208_5
  · exact cov208_6
  · exact cov208_7
def w209 : P33.Window := ⟨12,56,2258,1875,209292498982797177,138441,105000,5000000,81920000000⟩
def h209_0 : Height w209 := ⟨138441,105000,by decide +kernel⟩
def h209_1 : Height w209 := ⟨142360,102000,by decide +kernel⟩
def h209_2 : Height w209 := ⟨146491,99000,by decide +kernel⟩
def h209_3 : Height w209 := ⟨150863,96000,by decide +kernel⟩
def h209_4 : Height w209 := ⟨155511,93000,by decide +kernel⟩
def h209_5 : Height w209 := ⟨160476,90000,by decide +kernel⟩
def h209_6 : Height w209 := ⟨171574,84000,by decide +kernel⟩
def h209_7 : Height w209 := ⟨177843,81000,by decide +kernel⟩
def h209_8 : Height w209 := ⟨184714,78000,by decide +kernel⟩
def h209_9 : Height w209 := ⟨192307,75000,by decide +kernel⟩
def h209_10 : Height w209 := ⟨200776,72000,by decide +kernel⟩
def h209_11 : Height w209 := ⟨210323,69000,by decide +kernel⟩
def pick209 (cl : ℕ) : Height w209 := if cl<32 then (if cl<5 then (if cl<2 then (h209_0) else (if cl<3 then (h209_1) else (h209_2))) else (if cl<6 then (h209_3) else (if cl<13 then (h209_4) else (h209_5)))) else (if cl<145 then (if cl<46 then (h209_6) else (if cl<83 then (h209_7) else (h209_8))) else (if cl<312 then (h209_9) else (if cl<331 then (h209_10) else (h209_11))))
private theorem k209_1_0 : check w209 pick209 1 t8364 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k209_1_1 : check w209 pick209 1 t8359 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k209_1_2 : check w209 pick209 1 t8365 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w209 pick209 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t8364 t8359 k209_1_0 k209_1_1
private theorem k209_1_3 : check w209 pick209 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k209_1_4 : check w209 pick209 1 t8368 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k209_1_5 : check w209 pick209 1 t8369 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w209 pick209 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8368 k209_1_3 k209_1_4
private theorem k209_1_6 : check w209 pick209 1 t8370 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w209 pick209 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8365 t8369 k209_1_2 k209_1_5
theorem cov209_1 : PA.Covered 1 (OZ.Valid 1 w209.low w209.t w209.y w209.r w209.cap) (P33.root 1) :=
  Night6836Tree.sound w209 pick209 1 t8370 _ k209_1_6
theorem cov209_2 : PA.Covered 2 (OZ.Valid 2 w209.low w209.t w209.y w209.r w209.cap) (P33.root 2) :=
  Night6836Tree.sound w209 pick209 2 t6618 _ (by decide +kernel)
theorem cov209_3 : PA.Covered 3 (OZ.Valid 3 w209.low w209.t w209.y w209.r w209.cap) (P33.root 3) :=
  Night6836Tree.sound w209 pick209 3 t564 _ (by decide +kernel)
theorem cov209_4 : PA.Covered 4 (OZ.Valid 4 w209.low w209.t w209.y w209.r w209.cap) (P33.root 4) :=
  Night6836Tree.sound w209 pick209 4 t565 _ (by decide +kernel)
theorem cov209_5 : PA.Covered 5 (OZ.Valid 5 w209.low w209.t w209.y w209.r w209.cap) (P33.root 5) :=
  Night6836Tree.sound w209 pick209 5 t566 _ (by decide +kernel)
theorem cov209_6 : PA.Covered 6 (OZ.Valid 6 w209.low w209.t w209.y w209.r w209.cap) (P33.root 6) :=
  Night6836Tree.sound w209 pick209 6 t567 _ (by decide +kernel)
theorem cov209_7 : PA.Covered 7 (OZ.Valid 7 w209.low w209.t w209.y w209.r w209.cap) (P33.root 7) :=
  Night6836Tree.sound w209 pick209 7 t2134 _ (by decide +kernel)
theorem window209 : P33.WindowCount w209 := by
  apply P33.window_count w209 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov209_1
  · exact cov209_2
  · exact cov209_3
  · exact cov209_4
  · exact cov209_5
  · exact cov209_6
  · exact cov209_7
end ProximityPrize.SubmissionLower.Night6836Bank
