/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT03
import ProximityPrize.SubmissionLower.Night6836SharedT04
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w570 : P33.Window := ⟨9,41,3540,2541,198258915607799510,72899,59000,5000000,81920000000⟩
def h570_0 : Height w570 := ⟨72899,59000,by decide +kernel⟩
def h570_1 : Height w570 := ⟨78142,55000,by decide +kernel⟩
def h570_2 : Height w570 := ⟨84153,51000,by decide +kernel⟩
def h570_3 : Height w570 := ⟨91244,47000,by decide +kernel⟩
def h570_4 : Height w570 := ⟨99917,43000,by decide +kernel⟩
def h570_5 : Height w570 := ⟨111039,39000,by decide +kernel⟩
def pick570 (cl : ℕ) : Height w570 := if cl<32 then (if cl<2 then (h570_0) else (if cl<6 then (h570_1) else (h570_2))) else (if cl<62 then (h570_3) else (if cl<216 then (h570_4) else (h570_5)))
private theorem k570_1_0 : check w570 pick570 1 t5236 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k570_1_1 : check w570 pick570 1 t10911 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k570_1_2 : check w570 pick570 1 t10912 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w570 pick570 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5236 t10911 k570_1_0 k570_1_1
private theorem k570_1_3 : check w570 pick570 1 t11082 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k570_1_4 : check w570 pick570 1 t10888 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k570_1_5 : check w570 pick570 1 t11083 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w570 pick570 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t11082 t10888 k570_1_3 k570_1_4
private theorem k570_1_6 : check w570 pick570 1 t11084 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w570 pick570 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10912 t11083 k570_1_2 k570_1_5
private theorem k570_1_7 : check w570 pick570 1 t10896 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k570_1_8 : check w570 pick570 1 t6586 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k570_1_9 : check w570 pick570 1 t10897 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w570 pick570 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10896 t6586 k570_1_7 k570_1_8
private theorem k570_1_10 : check w570 pick570 1 t6602 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k570_1_11 : check w570 pick570 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k570_1_12 : check w570 pick570 1 t10898 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w570 pick570 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6602 t10862 k570_1_10 k570_1_11
private theorem k570_1_13 : check w570 pick570 1 t10899 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w570 pick570 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10897 t10898 k570_1_9 k570_1_12
private theorem k570_1_14 : check w570 pick570 1 t11085 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w570 pick570 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t11084 t10899 k570_1_6 k570_1_13
theorem cov570_1 : PA.Covered 1 (OZ.Valid 1 w570.low w570.t w570.y w570.r w570.cap) (P33.root 1) :=
  Night6836Tree.sound w570 pick570 1 t11085 _ k570_1_14
theorem cov570_2 : PA.Covered 2 (OZ.Valid 2 w570.low w570.t w570.y w570.r w570.cap) (P33.root 2) :=
  Night6836Tree.sound w570 pick570 2 t5222 _ (by decide +kernel)
theorem cov570_3 : PA.Covered 3 (OZ.Valid 3 w570.low w570.t w570.y w570.r w570.cap) (P33.root 3) :=
  Night6836Tree.sound w570 pick570 3 t564 _ (by decide +kernel)
theorem cov570_4 : PA.Covered 4 (OZ.Valid 4 w570.low w570.t w570.y w570.r w570.cap) (P33.root 4) :=
  Night6836Tree.sound w570 pick570 4 t565 _ (by decide +kernel)
theorem cov570_5 : PA.Covered 5 (OZ.Valid 5 w570.low w570.t w570.y w570.r w570.cap) (P33.root 5) :=
  Night6836Tree.sound w570 pick570 5 t566 _ (by decide +kernel)
theorem cov570_6 : PA.Covered 6 (OZ.Valid 6 w570.low w570.t w570.y w570.r w570.cap) (P33.root 6) :=
  Night6836Tree.sound w570 pick570 6 t567 _ (by decide +kernel)
theorem cov570_7 : PA.Covered 7 (OZ.Valid 7 w570.low w570.t w570.y w570.r w570.cap) (P33.root 7) :=
  Night6836Tree.sound w570 pick570 7 t2134 _ (by decide +kernel)
theorem window570 : P33.WindowCount w570 := by
  apply P33.window_count w570 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov570_1
  · exact cov570_2
  · exact cov570_3
  · exact cov570_4
  · exact cov570_5
  · exact cov570_6
  · exact cov570_7
def w571 : P33.Window := ⟨9,41,6167,5218,244146440671824743,37823,27000,5000000,81920000000⟩
def h571_0 : Height w571 := ⟨37823,27000,by decide +kernel⟩
def h571_1 : Height w571 := ⟨42491,24000,by decide +kernel⟩
def h571_2 : Height w571 := ⟨48682,21000,by decide +kernel⟩
def h571_3 : Height w571 := ⟨57838,18000,by decide +kernel⟩
def pick571 (cl : ℕ) : Height w571 := if cl<43 then (if cl<6 then (h571_0) else (h571_1)) else (if cl<302 then (h571_2) else (h571_3))
private theorem k571_1_0 : check w571 pick571 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k571_1_1 : check w571 pick571 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k571_1_2 : check w571 pick571 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w571 pick571 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k571_1_0 k571_1_1
private theorem k571_1_3 : check w571 pick571 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k571_1_4 : check w571 pick571 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w571 pick571 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k571_1_2 k571_1_3
private theorem k571_1_5 : check w571 pick571 1 t10460 ⟨1,7,2,16,1,52,139,179⟩ = true := by decide +kernel
private theorem k571_1_6 : check w571 pick571 1 t10461 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k571_1_7 : check w571 pick571 1 t10462 ⟨1,7,2,16,1,52,139,206⟩ = true := glue w571 pick571 1 ⟨1,7,2,16,1,52,139,206⟩ 3 179 t10460 t10461 k571_1_5 k571_1_6
private theorem k571_1_8 : check w571 pick571 1 t2385 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k571_1_9 : check w571 pick571 1 t10463 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k571_1_10 : check w571 pick571 1 t10464 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w571 pick571 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t2385 t10463 k571_1_8 k571_1_9
private theorem k571_1_11 : check w571 pick571 1 t10465 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w571 pick571 1 ⟨1,7,2,16,1,52,139,450⟩ 3 206 t10462 t10464 k571_1_7 k571_1_10
private theorem k571_1_12 : check w571 pick571 1 t10466 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w571 pick571 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10465 k571_1_4 k571_1_11
theorem cov571_1 : PA.Covered 1 (OZ.Valid 1 w571.low w571.t w571.y w571.r w571.cap) (P33.root 1) :=
  Night6836Tree.sound w571 pick571 1 t10466 _ k571_1_12
private theorem k571_2_0 : check w571 pick571 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k571_2_1 : check w571 pick571 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k571_2_2 : check w571 pick571 2 t9557 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w571 pick571 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t9133 k571_2_0 k571_2_1
theorem cov571_2 : PA.Covered 2 (OZ.Valid 2 w571.low w571.t w571.y w571.r w571.cap) (P33.root 2) :=
  Night6836Tree.sound w571 pick571 2 t9557 _ k571_2_2
theorem cov571_3 : PA.Covered 3 (OZ.Valid 3 w571.low w571.t w571.y w571.r w571.cap) (P33.root 3) :=
  Night6836Tree.sound w571 pick571 3 t564 _ (by decide +kernel)
theorem cov571_4 : PA.Covered 4 (OZ.Valid 4 w571.low w571.t w571.y w571.r w571.cap) (P33.root 4) :=
  Night6836Tree.sound w571 pick571 4 t565 _ (by decide +kernel)
theorem cov571_5 : PA.Covered 5 (OZ.Valid 5 w571.low w571.t w571.y w571.r w571.cap) (P33.root 5) :=
  Night6836Tree.sound w571 pick571 5 t566 _ (by decide +kernel)
theorem cov571_6 : PA.Covered 6 (OZ.Valid 6 w571.low w571.t w571.y w571.r w571.cap) (P33.root 6) :=
  Night6836Tree.sound w571 pick571 6 t567 _ (by decide +kernel)
theorem cov571_7 : PA.Covered 7 (OZ.Valid 7 w571.low w571.t w571.y w571.r w571.cap) (P33.root 7) :=
  Night6836Tree.sound w571 pick571 7 t2134 _ (by decide +kernel)
theorem window571 : P33.WindowCount w571 := by
  apply P33.window_count w571 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov571_1
  · exact cov571_2
  · exact cov571_3
  · exact cov571_4
  · exact cov571_5
  · exact cov571_6
  · exact cov571_7
def w572 : P33.Window := ⟨9,41,7128,7081,246474141746211281,26428,21000,5000000,81920000000⟩
def h572_0 : Height w572 := ⟨26428,21000,by decide +kernel⟩
def h572_1 : Height w572 := ⟨30788,18000,by decide +kernel⟩
def h572_2 : Height w572 := ⟨37119,15000,by decide +kernel⟩
def h572_3 : Height w572 := ⟨48524,12000,by decide +kernel⟩
def pick572 (cl : ℕ) : Height w572 := if cl<49 then (if cl<5 then (h572_0) else (h572_1)) else (if cl<853 then (h572_2) else (h572_3))
private theorem k572_1_0 : check w572 pick572 1 t11091 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k572_1_1 : check w572 pick572 1 t10052 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k572_1_2 : check w572 pick572 1 t11092 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w572 pick572 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t11091 t10052 k572_1_0 k572_1_1
private theorem k572_1_3 : check w572 pick572 1 t11073 ⟨1,7,2,16,1,20,77,138⟩ = true := by decide +kernel
private theorem k572_1_4 : check w572 pick572 1 t10514 ⟨1,7,2,16,21,52,77,138⟩ = true := by decide +kernel
private theorem k572_1_5 : check w572 pick572 1 t11074 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w572 pick572 1 ⟨1,7,2,16,1,52,77,138⟩ 2 20 t11073 t10514 k572_1_3 k572_1_4
private theorem k572_1_6 : check w572 pick572 1 t11093 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w572 pick572 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t11092 t11074 k572_1_2 k572_1_5
private theorem k572_1_7 : check w572 pick572 1 t11098 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k572_1_8 : check w572 pick572 1 t11102 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k572_1_9 : check w572 pick572 1 t11103 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w572 pick572 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t11098 t11102 k572_1_7 k572_1_8
private theorem k572_1_10 : check w572 pick572 1 t11105 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k572_1_11 : check w572 pick572 1 t11078 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k572_1_12 : check w572 pick572 1 t11106 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w572 pick572 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t11105 t11078 k572_1_10 k572_1_11
private theorem k572_1_13 : check w572 pick572 1 t11107 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w572 pick572 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t11103 t11106 k572_1_9 k572_1_12
private theorem k572_1_14 : check w572 pick572 1 t11108 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w572 pick572 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t11093 t11107 k572_1_6 k572_1_13
theorem cov572_1 : PA.Covered 1 (OZ.Valid 1 w572.low w572.t w572.y w572.r w572.cap) (P33.root 1) :=
  Night6836Tree.sound w572 pick572 1 t11108 _ k572_1_14
private theorem k572_2_0 : check w572 pick572 2 t9710 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k572_2_1 : check w572 pick572 2 t9719 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k572_2_2 : check w572 pick572 2 t9720 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w572 pick572 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9710 t9719 k572_2_0 k572_2_1
private theorem k572_2_3 : check w572 pick572 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k572_2_4 : check w572 pick572 2 t4155 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k572_2_5 : check w572 pick572 2 t4156 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w572 pick572 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4155 k572_2_3 k572_2_4
private theorem k572_2_6 : check w572 pick572 2 t11109 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w572 pick572 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9720 t4156 k572_2_2 k572_2_5
theorem cov572_2 : PA.Covered 2 (OZ.Valid 2 w572.low w572.t w572.y w572.r w572.cap) (P33.root 2) :=
  Night6836Tree.sound w572 pick572 2 t11109 _ k572_2_6
theorem cov572_3 : PA.Covered 3 (OZ.Valid 3 w572.low w572.t w572.y w572.r w572.cap) (P33.root 3) :=
  Night6836Tree.sound w572 pick572 3 t564 _ (by decide +kernel)
theorem cov572_4 : PA.Covered 4 (OZ.Valid 4 w572.low w572.t w572.y w572.r w572.cap) (P33.root 4) :=
  Night6836Tree.sound w572 pick572 4 t565 _ (by decide +kernel)
theorem cov572_5 : PA.Covered 5 (OZ.Valid 5 w572.low w572.t w572.y w572.r w572.cap) (P33.root 5) :=
  Night6836Tree.sound w572 pick572 5 t566 _ (by decide +kernel)
theorem cov572_6 : PA.Covered 6 (OZ.Valid 6 w572.low w572.t w572.y w572.r w572.cap) (P33.root 6) :=
  Night6836Tree.sound w572 pick572 6 t567 _ (by decide +kernel)
theorem cov572_7 : PA.Covered 7 (OZ.Valid 7 w572.low w572.t w572.y w572.r w572.cap) (P33.root 7) :=
  Night6836Tree.sound w572 pick572 7 t568 _ (by decide +kernel)
theorem window572 : P33.WindowCount w572 := by
  apply P33.window_count w572 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov572_1
  · exact cov572_2
  · exact cov572_3
  · exact cov572_4
  · exact cov572_5
  · exact cov572_6
  · exact cov572_7
def w573 : P33.Window := ⟨9,42,6167,5218,244979591690061246,39226,27000,5000000,81920000000⟩
def h573_0 : Height w573 := ⟨39226,27000,by decide +kernel⟩
def h573_1 : Height w573 := ⟨43980,24000,by decide +kernel⟩
def h573_2 : Height w573 := ⟨50297,21000,by decide +kernel⟩
def h573_3 : Height w573 := ⟨59658,18000,by decide +kernel⟩
def h573_4 : Height w573 := ⟨76250,15000,by decide +kernel⟩
def pick573 (cl : ℕ) : Height w573 := if cl<49 then (if cl<10 then (h573_0) else (h573_1)) else (if cl<302 then (h573_2) else (if cl<1021 then (h573_3) else (h573_4)))
private theorem k573_1_0 : check w573 pick573 1 t10217 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k573_1_1 : check w573 pick573 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k573_1_2 : check w573 pick573 1 t10218 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w573 pick573 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10217 t10040 k573_1_0 k573_1_1
private theorem k573_1_3 : check w573 pick573 1 t11112 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k573_1_4 : check w573 pick573 1 t11113 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w573 pick573 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10218 t11112 k573_1_2 k573_1_3
private theorem k573_1_5 : check w573 pick573 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k573_1_6 : check w573 pick573 1 t9299 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k573_1_7 : check w573 pick573 1 t9300 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w573 pick573 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t9299 k573_1_5 k573_1_6
private theorem k573_1_8 : check w573 pick573 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k573_1_9 : check w573 pick573 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k573_1_10 : check w573 pick573 1 t10502 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w573 pick573 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10064 k573_1_8 k573_1_9
private theorem k573_1_11 : check w573 pick573 1 t11114 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w573 pick573 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9300 t10502 k573_1_7 k573_1_10
private theorem k573_1_12 : check w573 pick573 1 t11115 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w573 pick573 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t11113 t11114 k573_1_4 k573_1_11
theorem cov573_1 : PA.Covered 1 (OZ.Valid 1 w573.low w573.t w573.y w573.r w573.cap) (P33.root 1) :=
  Night6836Tree.sound w573 pick573 1 t11115 _ k573_1_12
private theorem k573_2_0 : check w573 pick573 2 t3058 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k573_2_1 : check w573 pick573 2 t11121 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k573_2_2 : check w573 pick573 2 t11122 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w573 pick573 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t3058 t11121 k573_2_0 k573_2_1
theorem cov573_2 : PA.Covered 2 (OZ.Valid 2 w573.low w573.t w573.y w573.r w573.cap) (P33.root 2) :=
  Night6836Tree.sound w573 pick573 2 t11122 _ k573_2_2
theorem cov573_3 : PA.Covered 3 (OZ.Valid 3 w573.low w573.t w573.y w573.r w573.cap) (P33.root 3) :=
  Night6836Tree.sound w573 pick573 3 t564 _ (by decide +kernel)
theorem cov573_4 : PA.Covered 4 (OZ.Valid 4 w573.low w573.t w573.y w573.r w573.cap) (P33.root 4) :=
  Night6836Tree.sound w573 pick573 4 t565 _ (by decide +kernel)
theorem cov573_5 : PA.Covered 5 (OZ.Valid 5 w573.low w573.t w573.y w573.r w573.cap) (P33.root 5) :=
  Night6836Tree.sound w573 pick573 5 t566 _ (by decide +kernel)
theorem cov573_6 : PA.Covered 6 (OZ.Valid 6 w573.low w573.t w573.y w573.r w573.cap) (P33.root 6) :=
  Night6836Tree.sound w573 pick573 6 t567 _ (by decide +kernel)
theorem cov573_7 : PA.Covered 7 (OZ.Valid 7 w573.low w573.t w573.y w573.r w573.cap) (P33.root 7) :=
  Night6836Tree.sound w573 pick573 7 t2134 _ (by decide +kernel)
theorem window573 : P33.WindowCount w573 := by
  apply P33.window_count w573 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov573_1
  · exact cov573_2
  · exact cov573_3
  · exact cov573_4
  · exact cov573_5
  · exact cov573_6
  · exact cov573_7
def w574 : P33.Window := ⟨9,42,7080,7031,246456683240296692,27825,21000,5000000,81920000000⟩
def h574_0 : Height w574 := ⟨27825,21000,by decide +kernel⟩
def h574_1 : Height w574 := ⟨32325,18000,by decide +kernel⟩
def h574_2 : Height w574 := ⟨38903,15000,by decide +kernel⟩
def h574_3 : Height w574 := ⟨50853,12000,by decide +kernel⟩
def pick574 (cl : ℕ) : Height w574 := if cl<60 then (if cl<5 then (h574_0) else (h574_1)) else (if cl<925 then (h574_2) else (h574_3))
private theorem k574_1_0 : check w574 pick574 1 t3716 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k574_1_1 : check w574 pick574 1 t11123 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k574_1_2 : check w574 pick574 1 t11124 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w574 pick574 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t3716 t11123 k574_1_0 k574_1_1
private theorem k574_1_3 : check w574 pick574 1 t11130 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k574_1_4 : check w574 pick574 1 t11132 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k574_1_5 : check w574 pick574 1 t11133 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w574 pick574 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t11130 t11132 k574_1_3 k574_1_4
private theorem k574_1_6 : check w574 pick574 1 t11134 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w574 pick574 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t11124 t11133 k574_1_2 k574_1_5
private theorem k574_1_7 : check w574 pick574 1 t3594 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k574_1_8 : check w574 pick574 1 t3615 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k574_1_9 : check w574 pick574 1 t3616 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w574 pick574 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3594 t3615 k574_1_7 k574_1_8
private theorem k574_1_10 : check w574 pick574 1 t3655 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k574_1_11 : check w574 pick574 1 t11135 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k574_1_12 : check w574 pick574 1 t11136 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w574 pick574 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t3655 t11135 k574_1_10 k574_1_11
private theorem k574_1_13 : check w574 pick574 1 t11137 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w574 pick574 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3616 t11136 k574_1_9 k574_1_12
private theorem k574_1_14 : check w574 pick574 1 t11138 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w574 pick574 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t11134 t11137 k574_1_6 k574_1_13
theorem cov574_1 : PA.Covered 1 (OZ.Valid 1 w574.low w574.t w574.y w574.r w574.cap) (P33.root 1) :=
  Night6836Tree.sound w574 pick574 1 t11138 _ k574_1_14
private theorem k574_2_0 : check w574 pick574 2 t4994 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k574_2_1 : check w574 pick574 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k574_2_2 : check w574 pick574 2 t11139 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w574 pick574 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4994 t3777 k574_2_0 k574_2_1
private theorem k574_2_3 : check w574 pick574 2 t4029 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k574_2_4 : check w574 pick574 2 t11142 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k574_2_5 : check w574 pick574 2 t11143 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w574 pick574 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4029 t11142 k574_2_3 k574_2_4
private theorem k574_2_6 : check w574 pick574 2 t11144 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w574 pick574 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11139 t11143 k574_2_2 k574_2_5
theorem cov574_2 : PA.Covered 2 (OZ.Valid 2 w574.low w574.t w574.y w574.r w574.cap) (P33.root 2) :=
  Night6836Tree.sound w574 pick574 2 t11144 _ k574_2_6
theorem cov574_3 : PA.Covered 3 (OZ.Valid 3 w574.low w574.t w574.y w574.r w574.cap) (P33.root 3) :=
  Night6836Tree.sound w574 pick574 3 t564 _ (by decide +kernel)
theorem cov574_4 : PA.Covered 4 (OZ.Valid 4 w574.low w574.t w574.y w574.r w574.cap) (P33.root 4) :=
  Night6836Tree.sound w574 pick574 4 t565 _ (by decide +kernel)
theorem cov574_5 : PA.Covered 5 (OZ.Valid 5 w574.low w574.t w574.y w574.r w574.cap) (P33.root 5) :=
  Night6836Tree.sound w574 pick574 5 t566 _ (by decide +kernel)
theorem cov574_6 : PA.Covered 6 (OZ.Valid 6 w574.low w574.t w574.y w574.r w574.cap) (P33.root 6) :=
  Night6836Tree.sound w574 pick574 6 t567 _ (by decide +kernel)
theorem cov574_7 : PA.Covered 7 (OZ.Valid 7 w574.low w574.t w574.y w574.r w574.cap) (P33.root 7) :=
  Night6836Tree.sound w574 pick574 7 t568 _ (by decide +kernel)
theorem window574 : P33.WindowCount w574 := by
  apply P33.window_count w574 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov574_1
  · exact cov574_2
  · exact cov574_3
  · exact cov574_4
  · exact cov574_5
  · exact cov574_6
  · exact cov574_7
def w575 : P33.Window := ⟨9,43,7030,6976,246340650489942883,29292,21000,5000000,81920000000⟩
def h575_0 : Height w575 := ⟨29292,21000,by decide +kernel⟩
def h575_1 : Height w575 := ⟨33944,18000,by decide +kernel⟩
def h575_2 : Height w575 := ⟨40791,15000,by decide +kernel⟩
def h575_3 : Height w575 := ⟨53342,12000,by decide +kernel⟩
def pick575 (cl : ℕ) : Height w575 := if cl<79 then (if cl<6 then (h575_0) else (h575_1)) else (if cl<961 then (h575_2) else (h575_3))
private theorem k575_1_0 : check w575 pick575 1 t4037 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k575_1_1 : check w575 pick575 1 t11150 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k575_1_2 : check w575 pick575 1 t11151 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w575 pick575 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t4037 t11150 k575_1_0 k575_1_1
private theorem k575_1_3 : check w575 pick575 1 t11162 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k575_1_4 : check w575 pick575 1 t11170 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k575_1_5 : check w575 pick575 1 t11171 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w575 pick575 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t11162 t11170 k575_1_3 k575_1_4
private theorem k575_1_6 : check w575 pick575 1 t11172 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w575 pick575 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t11151 t11171 k575_1_2 k575_1_5
private theorem k575_1_7 : check w575 pick575 1 t11173 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k575_1_8 : check w575 pick575 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k575_1_9 : check w575 pick575 1 t11174 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w575 pick575 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t11173 t4090 k575_1_7 k575_1_8
private theorem k575_1_10 : check w575 pick575 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k575_1_11 : check w575 pick575 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k575_1_12 : check w575 pick575 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w575 pick575 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k575_1_10 k575_1_11
private theorem k575_1_13 : check w575 pick575 1 t11175 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w575 pick575 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t11174 t10667 k575_1_9 k575_1_12
private theorem k575_1_14 : check w575 pick575 1 t11176 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w575 pick575 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t11172 t11175 k575_1_6 k575_1_13
theorem cov575_1 : PA.Covered 1 (OZ.Valid 1 w575.low w575.t w575.y w575.r w575.cap) (P33.root 1) :=
  Night6836Tree.sound w575 pick575 1 t11176 _ k575_1_14
private theorem k575_2_0 : check w575 pick575 2 t11177 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k575_2_1 : check w575 pick575 2 t4937 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k575_2_2 : check w575 pick575 2 t11178 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w575 pick575 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t11177 t4937 k575_2_0 k575_2_1
private theorem k575_2_3 : check w575 pick575 2 t4140 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k575_2_4 : check w575 pick575 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k575_2_5 : check w575 pick575 2 t4141 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w575 pick575 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4140 t4033 k575_2_3 k575_2_4
private theorem k575_2_6 : check w575 pick575 2 t11179 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w575 pick575 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11178 t4141 k575_2_2 k575_2_5
theorem cov575_2 : PA.Covered 2 (OZ.Valid 2 w575.low w575.t w575.y w575.r w575.cap) (P33.root 2) :=
  Night6836Tree.sound w575 pick575 2 t11179 _ k575_2_6
theorem cov575_3 : PA.Covered 3 (OZ.Valid 3 w575.low w575.t w575.y w575.r w575.cap) (P33.root 3) :=
  Night6836Tree.sound w575 pick575 3 t564 _ (by decide +kernel)
theorem cov575_4 : PA.Covered 4 (OZ.Valid 4 w575.low w575.t w575.y w575.r w575.cap) (P33.root 4) :=
  Night6836Tree.sound w575 pick575 4 t565 _ (by decide +kernel)
theorem cov575_5 : PA.Covered 5 (OZ.Valid 5 w575.low w575.t w575.y w575.r w575.cap) (P33.root 5) :=
  Night6836Tree.sound w575 pick575 5 t566 _ (by decide +kernel)
theorem cov575_6 : PA.Covered 6 (OZ.Valid 6 w575.low w575.t w575.y w575.r w575.cap) (P33.root 6) :=
  Night6836Tree.sound w575 pick575 6 t567 _ (by decide +kernel)
theorem cov575_7 : PA.Covered 7 (OZ.Valid 7 w575.low w575.t w575.y w575.r w575.cap) (P33.root 7) :=
  Night6836Tree.sound w575 pick575 7 t568 _ (by decide +kernel)
theorem window575 : P33.WindowCount w575 := by
  apply P33.window_count w575 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov575_1
  · exact cov575_2
  · exact cov575_3
  · exact cov575_4
  · exact cov575_5
  · exact cov575_6
  · exact cov575_7
def w576 : P33.Window := ⟨9,44,6974,6400,242728435253603023,31606,24000,5000000,81920000000⟩
def h576_0 : Height w576 := ⟨31606,24000,by decide +kernel⟩
def h576_1 : Height w576 := ⟨35829,21000,by decide +kernel⟩
def h576_2 : Height w576 := ⟨41531,18000,by decide +kernel⟩
def h576_3 : Height w576 := ⟨50365,15000,by decide +kernel⟩
def pick576 (cl : ℕ) : Height w576 := if cl<28 then (if cl<4 then (h576_0) else (h576_1)) else (if cl<269 then (h576_2) else (h576_3))
private theorem k576_1_0 : check w576 pick576 1 t10707 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k576_1_1 : check w576 pick576 1 t10720 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k576_1_2 : check w576 pick576 1 t10721 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w576 pick576 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10707 t10720 k576_1_0 k576_1_1
private theorem k576_1_3 : check w576 pick576 1 t10739 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k576_1_4 : check w576 pick576 1 t10749 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k576_1_5 : check w576 pick576 1 t10750 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w576 pick576 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10739 t10749 k576_1_3 k576_1_4
private theorem k576_1_6 : check w576 pick576 1 t10751 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w576 pick576 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10721 t10750 k576_1_2 k576_1_5
private theorem k576_1_7 : check w576 pick576 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k576_1_8 : check w576 pick576 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k576_1_9 : check w576 pick576 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w576 pick576 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k576_1_7 k576_1_8
private theorem k576_1_10 : check w576 pick576 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k576_1_11 : check w576 pick576 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w576 pick576 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k576_1_9 k576_1_10
private theorem k576_1_12 : check w576 pick576 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k576_1_13 : check w576 pick576 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k576_1_14 : check w576 pick576 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w576 pick576 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k576_1_12 k576_1_13
private theorem k576_1_15 : check w576 pick576 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w576 pick576 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k576_1_11 k576_1_14
private theorem k576_1_16 : check w576 pick576 1 t10753 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w576 pick576 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10751 t10752 k576_1_6 k576_1_15
theorem cov576_1 : PA.Covered 1 (OZ.Valid 1 w576.low w576.t w576.y w576.r w576.cap) (P33.root 1) :=
  Night6836Tree.sound w576 pick576 1 t10753 _ k576_1_16
private theorem k576_2_0 : check w576 pick576 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k576_2_1 : check w576 pick576 2 t4937 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k576_2_2 : check w576 pick576 2 t11180 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w576 pick576 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t4937 k576_2_0 k576_2_1
private theorem k576_2_3 : check w576 pick576 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k576_2_4 : check w576 pick576 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k576_2_5 : check w576 pick576 2 t4225 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w576 pick576 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t4033 k576_2_3 k576_2_4
private theorem k576_2_6 : check w576 pick576 2 t11181 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w576 pick576 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11180 t4225 k576_2_2 k576_2_5
theorem cov576_2 : PA.Covered 2 (OZ.Valid 2 w576.low w576.t w576.y w576.r w576.cap) (P33.root 2) :=
  Night6836Tree.sound w576 pick576 2 t11181 _ k576_2_6
theorem cov576_3 : PA.Covered 3 (OZ.Valid 3 w576.low w576.t w576.y w576.r w576.cap) (P33.root 3) :=
  Night6836Tree.sound w576 pick576 3 t4151 _ (by decide +kernel)
theorem cov576_4 : PA.Covered 4 (OZ.Valid 4 w576.low w576.t w576.y w576.r w576.cap) (P33.root 4) :=
  Night6836Tree.sound w576 pick576 4 t565 _ (by decide +kernel)
theorem cov576_5 : PA.Covered 5 (OZ.Valid 5 w576.low w576.t w576.y w576.r w576.cap) (P33.root 5) :=
  Night6836Tree.sound w576 pick576 5 t566 _ (by decide +kernel)
theorem cov576_6 : PA.Covered 6 (OZ.Valid 6 w576.low w576.t w576.y w576.r w576.cap) (P33.root 6) :=
  Night6836Tree.sound w576 pick576 6 t567 _ (by decide +kernel)
theorem cov576_7 : PA.Covered 7 (OZ.Valid 7 w576.low w576.t w576.y w576.r w576.cap) (P33.root 7) :=
  Night6836Tree.sound w576 pick576 7 t568 _ (by decide +kernel)
theorem window576 : P33.WindowCount w576 := by
  apply P33.window_count w576 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov576_1
  · exact cov576_2
  · exact cov576_3
  · exact cov576_4
  · exact cov576_5
  · exact cov576_6
  · exact cov576_7
def w577 : P33.Window := ⟨9,45,6916,6664,244105857121300390,30249,24000,5000000,81920000000⟩
def h577_0 : Height w577 := ⟨30249,24000,by decide +kernel⟩
def h577_1 : Height w577 := ⟨34235,21000,by decide +kernel⟩
def h577_2 : Height w577 := ⟨39538,18000,by decide +kernel⟩
def h577_3 : Height w577 := ⟨47583,15000,by decide +kernel⟩
def h577_4 : Height w577 := ⟨62983,12000,by decide +kernel⟩
def pick577 (cl : ℕ) : Height w577 := if cl<20 then (if cl<2 then (h577_0) else (h577_1)) else (if cl<189 then (h577_2) else (if cl<1010 then (h577_3) else (h577_4)))
private theorem k577_1_0 : check w577 pick577 1 t10707 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k577_1_1 : check w577 pick577 1 t10720 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k577_1_2 : check w577 pick577 1 t10721 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w577 pick577 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10707 t10720 k577_1_0 k577_1_1
private theorem k577_1_3 : check w577 pick577 1 t10739 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k577_1_4 : check w577 pick577 1 t10749 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k577_1_5 : check w577 pick577 1 t10750 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w577 pick577 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10739 t10749 k577_1_3 k577_1_4
private theorem k577_1_6 : check w577 pick577 1 t10751 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w577 pick577 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10721 t10750 k577_1_2 k577_1_5
private theorem k577_1_7 : check w577 pick577 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k577_1_8 : check w577 pick577 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k577_1_9 : check w577 pick577 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w577 pick577 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k577_1_7 k577_1_8
private theorem k577_1_10 : check w577 pick577 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k577_1_11 : check w577 pick577 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w577 pick577 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k577_1_9 k577_1_10
private theorem k577_1_12 : check w577 pick577 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k577_1_13 : check w577 pick577 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k577_1_14 : check w577 pick577 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w577 pick577 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k577_1_12 k577_1_13
private theorem k577_1_15 : check w577 pick577 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w577 pick577 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k577_1_11 k577_1_14
private theorem k577_1_16 : check w577 pick577 1 t10753 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w577 pick577 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10751 t10752 k577_1_6 k577_1_15
theorem cov577_1 : PA.Covered 1 (OZ.Valid 1 w577.low w577.t w577.y w577.r w577.cap) (P33.root 1) :=
  Night6836Tree.sound w577 pick577 1 t10753 _ k577_1_16
private theorem k577_2_0 : check w577 pick577 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k577_2_1 : check w577 pick577 2 t4937 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k577_2_2 : check w577 pick577 2 t11180 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w577 pick577 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t4937 k577_2_0 k577_2_1
private theorem k577_2_3 : check w577 pick577 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k577_2_4 : check w577 pick577 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k577_2_5 : check w577 pick577 2 t4225 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w577 pick577 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t4033 k577_2_3 k577_2_4
private theorem k577_2_6 : check w577 pick577 2 t11181 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w577 pick577 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11180 t4225 k577_2_2 k577_2_5
theorem cov577_2 : PA.Covered 2 (OZ.Valid 2 w577.low w577.t w577.y w577.r w577.cap) (P33.root 2) :=
  Night6836Tree.sound w577 pick577 2 t11181 _ k577_2_6
theorem cov577_3 : PA.Covered 3 (OZ.Valid 3 w577.low w577.t w577.y w577.r w577.cap) (P33.root 3) :=
  Night6836Tree.sound w577 pick577 3 t4151 _ (by decide +kernel)
theorem cov577_4 : PA.Covered 4 (OZ.Valid 4 w577.low w577.t w577.y w577.r w577.cap) (P33.root 4) :=
  Night6836Tree.sound w577 pick577 4 t565 _ (by decide +kernel)
theorem cov577_5 : PA.Covered 5 (OZ.Valid 5 w577.low w577.t w577.y w577.r w577.cap) (P33.root 5) :=
  Night6836Tree.sound w577 pick577 5 t566 _ (by decide +kernel)
theorem cov577_6 : PA.Covered 6 (OZ.Valid 6 w577.low w577.t w577.y w577.r w577.cap) (P33.root 6) :=
  Night6836Tree.sound w577 pick577 6 t567 _ (by decide +kernel)
theorem cov577_7 : PA.Covered 7 (OZ.Valid 7 w577.low w577.t w577.y w577.r w577.cap) (P33.root 7) :=
  Night6836Tree.sound w577 pick577 7 t568 _ (by decide +kernel)
theorem window577 : P33.WindowCount w577 := by
  apply P33.window_count w577 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov577_1
  · exact cov577_2
  · exact cov577_3
  · exact cov577_4
  · exact cov577_5
  · exact cov577_6
  · exact cov577_7
def w578 : P33.Window := ⟨9,46,6297,5348,240503953997156871,38866,30000,5000000,81920000000⟩
def h578_0 : Height w578 := ⟨38866,30000,by decide +kernel⟩
def h578_1 : Height w578 := ⟨42783,27000,by decide +kernel⟩
def h578_2 : Height w578 := ⟨47625,24000,by decide +kernel⟩
def h578_3 : Height w578 := ⟨54045,21000,by decide +kernel⟩
def h578_4 : Height w578 := ⟨63505,18000,by decide +kernel⟩
def h578_5 : Height w578 := ⟨80055,15000,by decide +kernel⟩
def pick578 (cl : ℕ) : Height w578 := if cl<54 then (if cl<2 then (h578_0) else (if cl<13 then (h578_1) else (h578_2))) else (if cl<312 then (h578_3) else (if cl<1021 then (h578_4) else (h578_5)))
private theorem k578_1_0 : check w578 pick578 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k578_1_1 : check w578 pick578 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k578_1_2 : check w578 pick578 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w578 pick578 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k578_1_0 k578_1_1
private theorem k578_1_3 : check w578 pick578 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k578_1_4 : check w578 pick578 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k578_1_5 : check w578 pick578 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w578 pick578 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k578_1_3 k578_1_4
private theorem k578_1_6 : check w578 pick578 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w578 pick578 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k578_1_2 k578_1_5
private theorem k578_1_7 : check w578 pick578 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k578_1_8 : check w578 pick578 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k578_1_9 : check w578 pick578 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w578 pick578 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k578_1_7 k578_1_8
private theorem k578_1_10 : check w578 pick578 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k578_1_11 : check w578 pick578 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k578_1_12 : check w578 pick578 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w578 pick578 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k578_1_10 k578_1_11
private theorem k578_1_13 : check w578 pick578 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w578 pick578 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k578_1_9 k578_1_12
private theorem k578_1_14 : check w578 pick578 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w578 pick578 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k578_1_6 k578_1_13
theorem cov578_1 : PA.Covered 1 (OZ.Valid 1 w578.low w578.t w578.y w578.r w578.cap) (P33.root 1) :=
  Night6836Tree.sound w578 pick578 1 t10243 _ k578_1_14
private theorem k578_2_0 : check w578 pick578 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k578_2_1 : check w578 pick578 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k578_2_2 : check w578 pick578 2 t3778 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w578 pick578 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3777 k578_2_0 k578_2_1
private theorem k578_2_3 : check w578 pick578 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k578_2_4 : check w578 pick578 2 t6001 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k578_2_5 : check w578 pick578 2 t6002 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w578 pick578 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t6001 k578_2_3 k578_2_4
private theorem k578_2_6 : check w578 pick578 2 t11072 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w578 pick578 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3778 t6002 k578_2_2 k578_2_5
theorem cov578_2 : PA.Covered 2 (OZ.Valid 2 w578.low w578.t w578.y w578.r w578.cap) (P33.root 2) :=
  Night6836Tree.sound w578 pick578 2 t11072 _ k578_2_6
theorem cov578_3 : PA.Covered 3 (OZ.Valid 3 w578.low w578.t w578.y w578.r w578.cap) (P33.root 3) :=
  Night6836Tree.sound w578 pick578 3 t564 _ (by decide +kernel)
theorem cov578_4 : PA.Covered 4 (OZ.Valid 4 w578.low w578.t w578.y w578.r w578.cap) (P33.root 4) :=
  Night6836Tree.sound w578 pick578 4 t565 _ (by decide +kernel)
theorem cov578_5 : PA.Covered 5 (OZ.Valid 5 w578.low w578.t w578.y w578.r w578.cap) (P33.root 5) :=
  Night6836Tree.sound w578 pick578 5 t566 _ (by decide +kernel)
theorem cov578_6 : PA.Covered 6 (OZ.Valid 6 w578.low w578.t w578.y w578.r w578.cap) (P33.root 6) :=
  Night6836Tree.sound w578 pick578 6 t567 _ (by decide +kernel)
theorem cov578_7 : PA.Covered 7 (OZ.Valid 7 w578.low w578.t w578.y w578.r w578.cap) (P33.root 7) :=
  Night6836Tree.sound w578 pick578 7 t2134 _ (by decide +kernel)
theorem window578 : P33.WindowCount w578 := by
  apply P33.window_count w578 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov578_1
  · exact cov578_2
  · exact cov578_3
  · exact cov578_4
  · exact cov578_5
  · exact cov578_6
  · exact cov578_7
def w579 : P33.Window := ⟨9,46,6857,6798,245390508268418782,30115,24000,5000000,81920000000⟩
def h579_0 : Height w579 := ⟨30115,24000,by decide +kernel⟩
def h579_1 : Height w579 := ⟨34022,21000,by decide +kernel⟩
def h579_2 : Height w579 := ⟨39190,18000,by decide +kernel⟩
def h579_3 : Height w579 := ⟨46961,15000,by decide +kernel⟩
def h579_4 : Height w579 := ⟨61611,12000,by decide +kernel⟩
def pick579 (cl : ℕ) : Height w579 := if cl<18 then (if cl<2 then (h579_0) else (h579_1)) else (if cl<157 then (h579_2) else (if cl<997 then (h579_3) else (h579_4)))
private theorem k579_1_0 : check w579 pick579 1 t10707 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k579_1_1 : check w579 pick579 1 t10720 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k579_1_2 : check w579 pick579 1 t10721 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w579 pick579 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10707 t10720 k579_1_0 k579_1_1
private theorem k579_1_3 : check w579 pick579 1 t10739 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k579_1_4 : check w579 pick579 1 t10749 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k579_1_5 : check w579 pick579 1 t10750 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w579 pick579 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10739 t10749 k579_1_3 k579_1_4
private theorem k579_1_6 : check w579 pick579 1 t10751 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w579 pick579 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10721 t10750 k579_1_2 k579_1_5
private theorem k579_1_7 : check w579 pick579 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k579_1_8 : check w579 pick579 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k579_1_9 : check w579 pick579 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w579 pick579 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k579_1_7 k579_1_8
private theorem k579_1_10 : check w579 pick579 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k579_1_11 : check w579 pick579 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w579 pick579 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k579_1_9 k579_1_10
private theorem k579_1_12 : check w579 pick579 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k579_1_13 : check w579 pick579 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k579_1_14 : check w579 pick579 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w579 pick579 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k579_1_12 k579_1_13
private theorem k579_1_15 : check w579 pick579 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w579 pick579 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k579_1_11 k579_1_14
private theorem k579_1_16 : check w579 pick579 1 t10753 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w579 pick579 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10751 t10752 k579_1_6 k579_1_15
theorem cov579_1 : PA.Covered 1 (OZ.Valid 1 w579.low w579.t w579.y w579.r w579.cap) (P33.root 1) :=
  Night6836Tree.sound w579 pick579 1 t10753 _ k579_1_16
private theorem k579_2_0 : check w579 pick579 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k579_2_1 : check w579 pick579 2 t4937 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k579_2_2 : check w579 pick579 2 t11180 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w579 pick579 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t4937 k579_2_0 k579_2_1
private theorem k579_2_3 : check w579 pick579 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k579_2_4 : check w579 pick579 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k579_2_5 : check w579 pick579 2 t4225 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w579 pick579 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t4033 k579_2_3 k579_2_4
private theorem k579_2_6 : check w579 pick579 2 t11181 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w579 pick579 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11180 t4225 k579_2_2 k579_2_5
theorem cov579_2 : PA.Covered 2 (OZ.Valid 2 w579.low w579.t w579.y w579.r w579.cap) (P33.root 2) :=
  Night6836Tree.sound w579 pick579 2 t11181 _ k579_2_6
theorem cov579_3 : PA.Covered 3 (OZ.Valid 3 w579.low w579.t w579.y w579.r w579.cap) (P33.root 3) :=
  Night6836Tree.sound w579 pick579 3 t4151 _ (by decide +kernel)
theorem cov579_4 : PA.Covered 4 (OZ.Valid 4 w579.low w579.t w579.y w579.r w579.cap) (P33.root 4) :=
  Night6836Tree.sound w579 pick579 4 t565 _ (by decide +kernel)
theorem cov579_5 : PA.Covered 5 (OZ.Valid 5 w579.low w579.t w579.y w579.r w579.cap) (P33.root 5) :=
  Night6836Tree.sound w579 pick579 5 t566 _ (by decide +kernel)
theorem cov579_6 : PA.Covered 6 (OZ.Valid 6 w579.low w579.t w579.y w579.r w579.cap) (P33.root 6) :=
  Night6836Tree.sound w579 pick579 6 t567 _ (by decide +kernel)
theorem cov579_7 : PA.Covered 7 (OZ.Valid 7 w579.low w579.t w579.y w579.r w579.cap) (P33.root 7) :=
  Night6836Tree.sound w579 pick579 7 t568 _ (by decide +kernel)
theorem window579 : P33.WindowCount w579 := by
  apply P33.window_count w579 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov579_1
  · exact cov579_2
  · exact cov579_3
  · exact cov579_4
  · exact cov579_5
  · exact cov579_6
  · exact cov579_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w580 : P33.Window := ⟨9,47,6797,6736,246580922666028498,31677,24000,5000000,81920000000⟩
def h580_0 : Height w580 := ⟨31677,24000,by decide +kernel⟩
def h580_1 : Height w580 := ⟨35706,21000,by decide +kernel⟩
def h580_2 : Height w580 := ⟨41067,18000,by decide +kernel⟩
def h580_3 : Height w580 := ⟨49186,15000,by decide +kernel⟩
def h580_4 : Height w580 := ⟨64642,12000,by decide +kernel⟩
def pick580 (cl : ℕ) : Height w580 := if cl<21 then (if cl<2 then (h580_0) else (h580_1)) else (if cl<197 then (h580_2) else (if cl<1013 then (h580_3) else (h580_4)))
private theorem k580_1_0 : check w580 pick580 1 t10707 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k580_1_1 : check w580 pick580 1 t10720 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k580_1_2 : check w580 pick580 1 t10721 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w580 pick580 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10707 t10720 k580_1_0 k580_1_1
private theorem k580_1_3 : check w580 pick580 1 t10739 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k580_1_4 : check w580 pick580 1 t10749 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k580_1_5 : check w580 pick580 1 t10750 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w580 pick580 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10739 t10749 k580_1_3 k580_1_4
private theorem k580_1_6 : check w580 pick580 1 t10751 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w580 pick580 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10721 t10750 k580_1_2 k580_1_5
private theorem k580_1_7 : check w580 pick580 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k580_1_8 : check w580 pick580 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k580_1_9 : check w580 pick580 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w580 pick580 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k580_1_7 k580_1_8
private theorem k580_1_10 : check w580 pick580 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k580_1_11 : check w580 pick580 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w580 pick580 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k580_1_9 k580_1_10
private theorem k580_1_12 : check w580 pick580 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k580_1_13 : check w580 pick580 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k580_1_14 : check w580 pick580 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w580 pick580 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k580_1_12 k580_1_13
private theorem k580_1_15 : check w580 pick580 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w580 pick580 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k580_1_11 k580_1_14
private theorem k580_1_16 : check w580 pick580 1 t10753 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w580 pick580 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10751 t10752 k580_1_6 k580_1_15
theorem cov580_1 : PA.Covered 1 (OZ.Valid 1 w580.low w580.t w580.y w580.r w580.cap) (P33.root 1) :=
  Night6836Tree.sound w580 pick580 1 t10753 _ k580_1_16
private theorem k580_2_0 : check w580 pick580 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k580_2_1 : check w580 pick580 2 t4937 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k580_2_2 : check w580 pick580 2 t11180 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w580 pick580 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t4937 k580_2_0 k580_2_1
private theorem k580_2_3 : check w580 pick580 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k580_2_4 : check w580 pick580 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k580_2_5 : check w580 pick580 2 t4225 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w580 pick580 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t4033 k580_2_3 k580_2_4
private theorem k580_2_6 : check w580 pick580 2 t11181 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w580 pick580 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11180 t4225 k580_2_2 k580_2_5
theorem cov580_2 : PA.Covered 2 (OZ.Valid 2 w580.low w580.t w580.y w580.r w580.cap) (P33.root 2) :=
  Night6836Tree.sound w580 pick580 2 t11181 _ k580_2_6
theorem cov580_3 : PA.Covered 3 (OZ.Valid 3 w580.low w580.t w580.y w580.r w580.cap) (P33.root 3) :=
  Night6836Tree.sound w580 pick580 3 t4151 _ (by decide +kernel)
theorem cov580_4 : PA.Covered 4 (OZ.Valid 4 w580.low w580.t w580.y w580.r w580.cap) (P33.root 4) :=
  Night6836Tree.sound w580 pick580 4 t565 _ (by decide +kernel)
theorem cov580_5 : PA.Covered 5 (OZ.Valid 5 w580.low w580.t w580.y w580.r w580.cap) (P33.root 5) :=
  Night6836Tree.sound w580 pick580 5 t566 _ (by decide +kernel)
theorem cov580_6 : PA.Covered 6 (OZ.Valid 6 w580.low w580.t w580.y w580.r w580.cap) (P33.root 6) :=
  Night6836Tree.sound w580 pick580 6 t567 _ (by decide +kernel)
theorem cov580_7 : PA.Covered 7 (OZ.Valid 7 w580.low w580.t w580.y w580.r w580.cap) (P33.root 7) :=
  Night6836Tree.sound w580 pick580 7 t568 _ (by decide +kernel)
theorem window580 : P33.WindowCount w580 := by
  apply P33.window_count w580 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov580_1
  · exact cov580_2
  · exact cov580_3
  · exact cov580_4
  · exact cov580_5
  · exact cov580_6
  · exact cov580_7
def w581 : P33.Window := ⟨9,48,6735,6664,247068215141326577,33374,24000,5000000,81920000000⟩
def h581_0 : Height w581 := ⟨33374,24000,by decide +kernel⟩
def h581_1 : Height w581 := ⟨37541,21000,by decide +kernel⟩
def h581_2 : Height w581 := ⟨43123,18000,by decide +kernel⟩
def h581_3 : Height w581 := ⟨51644,15000,by decide +kernel⟩
def h581_4 : Height w581 := ⟨68045,12000,by decide +kernel⟩
def pick581 (cl : ℕ) : Height w581 := if cl<26 then (if cl<4 then (h581_0) else (h581_1)) else (if cl<246 then (h581_2) else (if cl<1021 then (h581_3) else (h581_4)))
private theorem k581_1_0 : check w581 pick581 1 t10707 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k581_1_1 : check w581 pick581 1 t10720 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k581_1_2 : check w581 pick581 1 t10721 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w581 pick581 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10707 t10720 k581_1_0 k581_1_1
private theorem k581_1_3 : check w581 pick581 1 t10739 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k581_1_4 : check w581 pick581 1 t10749 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k581_1_5 : check w581 pick581 1 t10750 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w581 pick581 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10739 t10749 k581_1_3 k581_1_4
private theorem k581_1_6 : check w581 pick581 1 t10751 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w581 pick581 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10721 t10750 k581_1_2 k581_1_5
private theorem k581_1_7 : check w581 pick581 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k581_1_8 : check w581 pick581 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k581_1_9 : check w581 pick581 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w581 pick581 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k581_1_7 k581_1_8
private theorem k581_1_10 : check w581 pick581 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k581_1_11 : check w581 pick581 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w581 pick581 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k581_1_9 k581_1_10
private theorem k581_1_12 : check w581 pick581 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k581_1_13 : check w581 pick581 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k581_1_14 : check w581 pick581 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w581 pick581 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k581_1_12 k581_1_13
private theorem k581_1_15 : check w581 pick581 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w581 pick581 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k581_1_11 k581_1_14
private theorem k581_1_16 : check w581 pick581 1 t10753 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w581 pick581 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10751 t10752 k581_1_6 k581_1_15
theorem cov581_1 : PA.Covered 1 (OZ.Valid 1 w581.low w581.t w581.y w581.r w581.cap) (P33.root 1) :=
  Night6836Tree.sound w581 pick581 1 t10753 _ k581_1_16
private theorem k581_2_0 : check w581 pick581 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k581_2_1 : check w581 pick581 2 t11183 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k581_2_2 : check w581 pick581 2 t11184 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w581 pick581 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t11183 k581_2_0 k581_2_1
private theorem k581_2_3 : check w581 pick581 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k581_2_4 : check w581 pick581 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k581_2_5 : check w581 pick581 2 t4225 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w581 pick581 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t4033 k581_2_3 k581_2_4
private theorem k581_2_6 : check w581 pick581 2 t11185 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w581 pick581 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11184 t4225 k581_2_2 k581_2_5
theorem cov581_2 : PA.Covered 2 (OZ.Valid 2 w581.low w581.t w581.y w581.r w581.cap) (P33.root 2) :=
  Night6836Tree.sound w581 pick581 2 t11185 _ k581_2_6
theorem cov581_3 : PA.Covered 3 (OZ.Valid 3 w581.low w581.t w581.y w581.r w581.cap) (P33.root 3) :=
  Night6836Tree.sound w581 pick581 3 t4151 _ (by decide +kernel)
theorem cov581_4 : PA.Covered 4 (OZ.Valid 4 w581.low w581.t w581.y w581.r w581.cap) (P33.root 4) :=
  Night6836Tree.sound w581 pick581 4 t565 _ (by decide +kernel)
theorem cov581_5 : PA.Covered 5 (OZ.Valid 5 w581.low w581.t w581.y w581.r w581.cap) (P33.root 5) :=
  Night6836Tree.sound w581 pick581 5 t566 _ (by decide +kernel)
theorem cov581_6 : PA.Covered 6 (OZ.Valid 6 w581.low w581.t w581.y w581.r w581.cap) (P33.root 6) :=
  Night6836Tree.sound w581 pick581 6 t567 _ (by decide +kernel)
theorem cov581_7 : PA.Covered 7 (OZ.Valid 7 w581.low w581.t w581.y w581.r w581.cap) (P33.root 7) :=
  Night6836Tree.sound w581 pick581 7 t568 _ (by decide +kernel)
theorem window581 : P33.WindowCount w581 := by
  apply P33.window_count w581 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov581_1
  · exact cov581_2
  · exact cov581_3
  · exact cov581_4
  · exact cov581_5
  · exact cov581_6
  · exact cov581_7
def w582 : P33.Window := ⟨9,49,6663,6589,245485361369372699,35151,24000,5000000,81920000000⟩
def h582_0 : Height w582 := ⟨35151,24000,by decide +kernel⟩
def h582_1 : Height w582 := ⟨39469,21000,by decide +kernel⟩
def h582_2 : Height w582 := ⟨45290,18000,by decide +kernel⟩
def h582_3 : Height w582 := ⟨54250,15000,by decide +kernel⟩
def h582_4 : Height w582 := ⟨71695,12000,by decide +kernel⟩
def pick582 (cl : ℕ) : Height w582 := if cl<32 then (if cl<4 then (h582_0) else (h582_1)) else (if cl<278 then (h582_2) else (if cl<1026 then (h582_3) else (h582_4)))
private theorem k582_1_0 : check w582 pick582 1 t10707 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k582_1_1 : check w582 pick582 1 t10720 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k582_1_2 : check w582 pick582 1 t10721 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w582 pick582 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10707 t10720 k582_1_0 k582_1_1
private theorem k582_1_3 : check w582 pick582 1 t10739 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k582_1_4 : check w582 pick582 1 t10749 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k582_1_5 : check w582 pick582 1 t10750 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w582 pick582 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10739 t10749 k582_1_3 k582_1_4
private theorem k582_1_6 : check w582 pick582 1 t10751 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w582 pick582 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10721 t10750 k582_1_2 k582_1_5
private theorem k582_1_7 : check w582 pick582 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k582_1_8 : check w582 pick582 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k582_1_9 : check w582 pick582 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w582 pick582 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k582_1_7 k582_1_8
private theorem k582_1_10 : check w582 pick582 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k582_1_11 : check w582 pick582 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w582 pick582 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k582_1_9 k582_1_10
private theorem k582_1_12 : check w582 pick582 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k582_1_13 : check w582 pick582 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k582_1_14 : check w582 pick582 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w582 pick582 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k582_1_12 k582_1_13
private theorem k582_1_15 : check w582 pick582 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w582 pick582 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k582_1_11 k582_1_14
private theorem k582_1_16 : check w582 pick582 1 t10753 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w582 pick582 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10751 t10752 k582_1_6 k582_1_15
theorem cov582_1 : PA.Covered 1 (OZ.Valid 1 w582.low w582.t w582.y w582.r w582.cap) (P33.root 1) :=
  Night6836Tree.sound w582 pick582 1 t10753 _ k582_1_16
private theorem k582_2_0 : check w582 pick582 2 t4120 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k582_2_1 : check w582 pick582 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k582_2_2 : check w582 pick582 2 t4132 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w582 pick582 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4120 t4131 k582_2_0 k582_2_1
private theorem k582_2_3 : check w582 pick582 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k582_2_4 : check w582 pick582 2 t4033 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k582_2_5 : check w582 pick582 2 t4225 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w582 pick582 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t4033 k582_2_3 k582_2_4
private theorem k582_2_6 : check w582 pick582 2 t4226 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w582 pick582 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4132 t4225 k582_2_2 k582_2_5
theorem cov582_2 : PA.Covered 2 (OZ.Valid 2 w582.low w582.t w582.y w582.r w582.cap) (P33.root 2) :=
  Night6836Tree.sound w582 pick582 2 t4226 _ k582_2_6
theorem cov582_3 : PA.Covered 3 (OZ.Valid 3 w582.low w582.t w582.y w582.r w582.cap) (P33.root 3) :=
  Night6836Tree.sound w582 pick582 3 t4231 _ (by decide +kernel)
theorem cov582_4 : PA.Covered 4 (OZ.Valid 4 w582.low w582.t w582.y w582.r w582.cap) (P33.root 4) :=
  Night6836Tree.sound w582 pick582 4 t565 _ (by decide +kernel)
theorem cov582_5 : PA.Covered 5 (OZ.Valid 5 w582.low w582.t w582.y w582.r w582.cap) (P33.root 5) :=
  Night6836Tree.sound w582 pick582 5 t566 _ (by decide +kernel)
theorem cov582_6 : PA.Covered 6 (OZ.Valid 6 w582.low w582.t w582.y w582.r w582.cap) (P33.root 6) :=
  Night6836Tree.sound w582 pick582 6 t567 _ (by decide +kernel)
theorem cov582_7 : PA.Covered 7 (OZ.Valid 7 w582.low w582.t w582.y w582.r w582.cap) (P33.root 7) :=
  Night6836Tree.sound w582 pick582 7 t568 _ (by decide +kernel)
theorem window582 : P33.WindowCount w582 := by
  apply P33.window_count w582 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov582_1
  · exact cov582_2
  · exact cov582_3
  · exact cov582_4
  · exact cov582_5
  · exact cov582_6
  · exact cov582_7
def w583 : P33.Window := ⟨9,50,6588,5661,246316754640862760,43378,27000,5000000,81920000000⟩
def h583_0 : Height w583 := ⟨43378,27000,by decide +kernel⟩
def h583_1 : Height w583 := ⟨47977,24000,by decide +kernel⟩
def h583_2 : Height w583 := ⟨53988,21000,by decide +kernel⟩
def h583_3 : Height w583 := ⟨62661,18000,by decide +kernel⟩
def h583_4 : Height w583 := ⟨77321,15000,by decide +kernel⟩
def pick583 (cl : ℕ) : Height w583 := if cl<39 then (if cl<6 then (h583_0) else (h583_1)) else (if cl<260 then (h583_2) else (if cl<997 then (h583_3) else (h583_4)))
private theorem k583_1_0 : check w583 pick583 1 t4290 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k583_1_1 : check w583 pick583 1 t11186 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k583_1_2 : check w583 pick583 1 t11187 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w583 pick583 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t4290 t11186 k583_1_0 k583_1_1
private theorem k583_1_3 : check w583 pick583 1 t10778 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k583_1_4 : check w583 pick583 1 t11198 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k583_1_5 : check w583 pick583 1 t11199 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w583 pick583 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t10778 t11198 k583_1_3 k583_1_4
private theorem k583_1_6 : check w583 pick583 1 t11200 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w583 pick583 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t11187 t11199 k583_1_2 k583_1_5
private theorem k583_1_7 : check w583 pick583 1 t4754 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k583_1_8 : check w583 pick583 1 t4428 ⟨1,7,2,5,1,52,160,192⟩ = true := by decide +kernel
private theorem k583_1_9 : check w583 pick583 1 t4431 ⟨1,7,6,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k583_1_10 : check w583 pick583 1 t4432 ⟨1,7,2,16,1,52,160,192⟩ = true := glue w583 pick583 1 ⟨1,7,2,16,1,52,160,192⟩ 1 5 t4428 t4431 k583_1_8 k583_1_9
private theorem k583_1_11 : check w583 pick583 1 t4755 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w583 pick583 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t4754 t4432 k583_1_7 k583_1_10
private theorem k583_1_12 : check w583 pick583 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k583_1_13 : check w583 pick583 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k583_1_14 : check w583 pick583 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w583 pick583 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k583_1_12 k583_1_13
private theorem k583_1_15 : check w583 pick583 1 t11201 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w583 pick583 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4755 t10667 k583_1_11 k583_1_14
private theorem k583_1_16 : check w583 pick583 1 t11202 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w583 pick583 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t11200 t11201 k583_1_6 k583_1_15
theorem cov583_1 : PA.Covered 1 (OZ.Valid 1 w583.low w583.t w583.y w583.r w583.cap) (P33.root 1) :=
  Night6836Tree.sound w583 pick583 1 t11202 _ k583_1_16
private theorem k583_2_0 : check w583 pick583 2 t11204 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k583_2_1 : check w583 pick583 2 t4131 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k583_2_2 : check w583 pick583 2 t11205 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w583 pick583 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t11204 t4131 k583_2_0 k583_2_1
private theorem k583_2_3 : check w583 pick583 2 t11209 ⟨2,7,4,16,2,52,140,248⟩ = true := by decide +kernel
private theorem k583_2_4 : check w583 pick583 2 t4531 ⟨2,7,4,16,2,52,249,450⟩ = true := by decide +kernel
private theorem k583_2_5 : check w583 pick583 2 t11210 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w583 pick583 2 ⟨2,7,4,16,2,52,140,450⟩ 3 248 t11209 t4531 k583_2_3 k583_2_4
private theorem k583_2_6 : check w583 pick583 2 t11211 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w583 pick583 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11205 t11210 k583_2_2 k583_2_5
theorem cov583_2 : PA.Covered 2 (OZ.Valid 2 w583.low w583.t w583.y w583.r w583.cap) (P33.root 2) :=
  Night6836Tree.sound w583 pick583 2 t11211 _ k583_2_6
theorem cov583_3 : PA.Covered 3 (OZ.Valid 3 w583.low w583.t w583.y w583.r w583.cap) (P33.root 3) :=
  Night6836Tree.sound w583 pick583 3 t4231 _ (by decide +kernel)
theorem cov583_4 : PA.Covered 4 (OZ.Valid 4 w583.low w583.t w583.y w583.r w583.cap) (P33.root 4) :=
  Night6836Tree.sound w583 pick583 4 t565 _ (by decide +kernel)
theorem cov583_5 : PA.Covered 5 (OZ.Valid 5 w583.low w583.t w583.y w583.r w583.cap) (P33.root 5) :=
  Night6836Tree.sound w583 pick583 5 t566 _ (by decide +kernel)
theorem cov583_6 : PA.Covered 6 (OZ.Valid 6 w583.low w583.t w583.y w583.r w583.cap) (P33.root 6) :=
  Night6836Tree.sound w583 pick583 6 t567 _ (by decide +kernel)
theorem cov583_7 : PA.Covered 7 (OZ.Valid 7 w583.low w583.t w583.y w583.r w583.cap) (P33.root 7) :=
  Night6836Tree.sound w583 pick583 7 t568 _ (by decide +kernel)
theorem window583 : P33.WindowCount w583 := by
  apply P33.window_count w583 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov583_1
  · exact cov583_2
  · exact cov583_3
  · exact cov583_4
  · exact cov583_5
  · exact cov583_6
  · exact cov583_7
def w584 : P33.Window := ⟨9,51,6503,6388,247106371498189933,39454,24000,5000000,81920000000⟩
def h584_0 : Height w584 := ⟨39454,24000,by decide +kernel⟩
def h584_1 : Height w584 := ⟨44171,21000,by decide +kernel⟩
def h584_2 : Height w584 := ⟨50635,18000,by decide +kernel⟩
def h584_3 : Height w584 := ⟨60798,15000,by decide +kernel⟩
def h584_4 : Height w584 := ⟨81199,12000,by decide +kernel⟩
def pick584 (cl : ℕ) : Height w584 := if cl<54 then (if cl<10 then (h584_0) else (h584_1)) else (if cl<561 then (h584_2) else (if cl<1027 then (h584_3) else (h584_4)))
private theorem k584_1_0 : check w584 pick584 1 t11217 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k584_1_1 : check w584 pick584 1 t10776 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k584_1_2 : check w584 pick584 1 t11218 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w584 pick584 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t11217 t10776 k584_1_0 k584_1_1
private theorem k584_1_3 : check w584 pick584 1 t10778 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k584_1_4 : check w584 pick584 1 t10780 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k584_1_5 : check w584 pick584 1 t10781 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w584 pick584 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t10778 t10780 k584_1_3 k584_1_4
private theorem k584_1_6 : check w584 pick584 1 t11219 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w584 pick584 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t11218 t10781 k584_1_2 k584_1_5
private theorem k584_1_7 : check w584 pick584 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k584_1_8 : check w584 pick584 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k584_1_9 : check w584 pick584 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w584 pick584 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k584_1_7 k584_1_8
private theorem k584_1_10 : check w584 pick584 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k584_1_11 : check w584 pick584 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w584 pick584 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k584_1_9 k584_1_10
private theorem k584_1_12 : check w584 pick584 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k584_1_13 : check w584 pick584 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k584_1_14 : check w584 pick584 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w584 pick584 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k584_1_12 k584_1_13
private theorem k584_1_15 : check w584 pick584 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w584 pick584 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k584_1_11 k584_1_14
private theorem k584_1_16 : check w584 pick584 1 t11220 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w584 pick584 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t11219 t10752 k584_1_6 k584_1_15
theorem cov584_1 : PA.Covered 1 (OZ.Valid 1 w584.low w584.t w584.y w584.r w584.cap) (P33.root 1) :=
  Night6836Tree.sound w584 pick584 1 t11220 _ k584_1_16
private theorem k584_2_0 : check w584 pick584 2 t11221 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k584_2_1 : check w584 pick584 2 t4479 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k584_2_2 : check w584 pick584 2 t11222 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w584 pick584 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t11221 t4479 k584_2_0 k584_2_1
private theorem k584_2_3 : check w584 pick584 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k584_2_4 : check w584 pick584 2 t11226 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k584_2_5 : check w584 pick584 2 t11227 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w584 pick584 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t11226 k584_2_3 k584_2_4
private theorem k584_2_6 : check w584 pick584 2 t11228 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w584 pick584 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11222 t11227 k584_2_2 k584_2_5
theorem cov584_2 : PA.Covered 2 (OZ.Valid 2 w584.low w584.t w584.y w584.r w584.cap) (P33.root 2) :=
  Night6836Tree.sound w584 pick584 2 t11228 _ k584_2_6
theorem cov584_3 : PA.Covered 3 (OZ.Valid 3 w584.low w584.t w584.y w584.r w584.cap) (P33.root 3) :=
  Night6836Tree.sound w584 pick584 3 t4231 _ (by decide +kernel)
theorem cov584_4 : PA.Covered 4 (OZ.Valid 4 w584.low w584.t w584.y w584.r w584.cap) (P33.root 4) :=
  Night6836Tree.sound w584 pick584 4 t565 _ (by decide +kernel)
theorem cov584_5 : PA.Covered 5 (OZ.Valid 5 w584.low w584.t w584.y w584.r w584.cap) (P33.root 5) :=
  Night6836Tree.sound w584 pick584 5 t566 _ (by decide +kernel)
theorem cov584_6 : PA.Covered 6 (OZ.Valid 6 w584.low w584.t w584.y w584.r w584.cap) (P33.root 6) :=
  Night6836Tree.sound w584 pick584 6 t567 _ (by decide +kernel)
theorem cov584_7 : PA.Covered 7 (OZ.Valid 7 w584.low w584.t w584.y w584.r w584.cap) (P33.root 7) :=
  Night6836Tree.sound w584 pick584 7 t568 _ (by decide +kernel)
theorem window584 : P33.WindowCount w584 := by
  apply P33.window_count w584 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov584_1
  · exact cov584_2
  · exact cov584_3
  · exact cov584_4
  · exact cov584_5
  · exact cov584_6
  · exact cov584_7
def w585 : P33.Window := ⟨9,52,5217,4268,242996427677524769,56646,39000,5000000,81920000000⟩
def h585_0 : Height w585 := ⟨56646,39000,by decide +kernel⟩
def h585_1 : Height w585 := ⟨60543,36000,by decide +kernel⟩
def h585_2 : Height w585 := ⟨65075,33000,by decide +kernel⟩
def h585_3 : Height w585 := ⟨70533,30000,by decide +kernel⟩
def h585_4 : Height w585 := ⟨77416,27000,by decide +kernel⟩
def h585_5 : Height w585 := ⟨86660,24000,by decide +kernel⟩
def h585_6 : Height w585 := ⟨100245,21000,by decide +kernel⟩
def pick585 (cl : ℕ) : Height w585 := if cl<32 then (if cl<2 then (h585_0) else (if cl<6 then (h585_1) else (h585_2))) else (if cl<302 then (if cl<83 then (h585_3) else (h585_4)) else (if cl<989 then (h585_5) else (h585_6)))
private theorem k585_1_0 : check w585 pick585 1 t10535 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k585_1_1 : check w585 pick585 1 t10552 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k585_1_2 : check w585 pick585 1 t10553 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w585 pick585 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10535 t10552 k585_1_0 k585_1_1
private theorem k585_1_3 : check w585 pick585 1 t10566 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k585_1_4 : check w585 pick585 1 t10572 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k585_1_5 : check w585 pick585 1 t10573 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w585 pick585 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t10566 t10572 k585_1_3 k585_1_4
private theorem k585_1_6 : check w585 pick585 1 t10574 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w585 pick585 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t10553 t10573 k585_1_2 k585_1_5
private theorem k585_1_7 : check w585 pick585 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k585_1_8 : check w585 pick585 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k585_1_9 : check w585 pick585 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w585 pick585 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k585_1_7 k585_1_8
private theorem k585_1_10 : check w585 pick585 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k585_1_11 : check w585 pick585 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k585_1_12 : check w585 pick585 1 t10502 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w585 pick585 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10064 k585_1_10 k585_1_11
private theorem k585_1_13 : check w585 pick585 1 t10503 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w585 pick585 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t10502 k585_1_9 k585_1_12
private theorem k585_1_14 : check w585 pick585 1 t10575 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w585 pick585 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10574 t10503 k585_1_6 k585_1_13
theorem cov585_1 : PA.Covered 1 (OZ.Valid 1 w585.low w585.t w585.y w585.r w585.cap) (P33.root 1) :=
  Night6836Tree.sound w585 pick585 1 t10575 _ k585_1_14
private theorem k585_2_0 : check w585 pick585 2 t5184 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k585_2_1 : check w585 pick585 2 t5187 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k585_2_2 : check w585 pick585 2 t5188 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w585 pick585 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5184 t5187 k585_2_0 k585_2_1
theorem cov585_2 : PA.Covered 2 (OZ.Valid 2 w585.low w585.t w585.y w585.r w585.cap) (P33.root 2) :=
  Night6836Tree.sound w585 pick585 2 t5188 _ k585_2_2
theorem cov585_3 : PA.Covered 3 (OZ.Valid 3 w585.low w585.t w585.y w585.r w585.cap) (P33.root 3) :=
  Night6836Tree.sound w585 pick585 3 t564 _ (by decide +kernel)
theorem cov585_4 : PA.Covered 4 (OZ.Valid 4 w585.low w585.t w585.y w585.r w585.cap) (P33.root 4) :=
  Night6836Tree.sound w585 pick585 4 t565 _ (by decide +kernel)
theorem cov585_5 : PA.Covered 5 (OZ.Valid 5 w585.low w585.t w585.y w585.r w585.cap) (P33.root 5) :=
  Night6836Tree.sound w585 pick585 5 t566 _ (by decide +kernel)
theorem cov585_6 : PA.Covered 6 (OZ.Valid 6 w585.low w585.t w585.y w585.r w585.cap) (P33.root 6) :=
  Night6836Tree.sound w585 pick585 6 t567 _ (by decide +kernel)
theorem cov585_7 : PA.Covered 7 (OZ.Valid 7 w585.low w585.t w585.y w585.r w585.cap) (P33.root 7) :=
  Night6836Tree.sound w585 pick585 7 t2134 _ (by decide +kernel)
theorem window585 : P33.WindowCount w585 := by
  apply P33.window_count w585 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov585_1
  · exact cov585_2
  · exact cov585_3
  · exact cov585_4
  · exact cov585_5
  · exact cov585_6
  · exact cov585_7
def w586 : P33.Window := ⟨9,52,6387,6081,247454876109593465,40242,27000,5000000,81920000000⟩
def h586_0 : Height w586 := ⟨40242,27000,by decide +kernel⟩
def h586_1 : Height w586 := ⟨44380,24000,by decide +kernel⟩
def h586_2 : Height w586 := ⟨49674,21000,by decide +kernel⟩
def h586_3 : Height w586 := ⟨57095,18000,by decide +kernel⟩
def h586_4 : Height w586 := ⟨69121,15000,by decide +kernel⟩
def pick586 (cl : ℕ) : Height w586 := if cl<20 then (if cl<3 then (h586_0) else (h586_1)) else (if cl<125 then (h586_2) else (if cl<925 then (h586_3) else (h586_4)))
private theorem k586_1_0 : check w586 pick586 1 t4544 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k586_1_1 : check w586 pick586 1 t11186 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k586_1_2 : check w586 pick586 1 t11229 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w586 pick586 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t4544 t11186 k586_1_0 k586_1_1
private theorem k586_1_3 : check w586 pick586 1 t10778 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k586_1_4 : check w586 pick586 1 t10780 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k586_1_5 : check w586 pick586 1 t10781 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w586 pick586 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t10778 t10780 k586_1_3 k586_1_4
private theorem k586_1_6 : check w586 pick586 1 t11230 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w586 pick586 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t11229 t10781 k586_1_2 k586_1_5
private theorem k586_1_7 : check w586 pick586 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k586_1_8 : check w586 pick586 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k586_1_9 : check w586 pick586 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w586 pick586 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k586_1_7 k586_1_8
private theorem k586_1_10 : check w586 pick586 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k586_1_11 : check w586 pick586 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w586 pick586 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k586_1_9 k586_1_10
private theorem k586_1_12 : check w586 pick586 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k586_1_13 : check w586 pick586 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k586_1_14 : check w586 pick586 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w586 pick586 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k586_1_12 k586_1_13
private theorem k586_1_15 : check w586 pick586 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w586 pick586 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k586_1_11 k586_1_14
private theorem k586_1_16 : check w586 pick586 1 t11231 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w586 pick586 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t11230 t10752 k586_1_6 k586_1_15
theorem cov586_1 : PA.Covered 1 (OZ.Valid 1 w586.low w586.t w586.y w586.r w586.cap) (P33.root 1) :=
  Night6836Tree.sound w586 pick586 1 t11231 _ k586_1_16
private theorem k586_2_0 : check w586 pick586 2 t4112 ⟨2,7,4,16,2,52,2,56⟩ = true := by decide +kernel
private theorem k586_2_1 : check w586 pick586 2 t5946 ⟨2,7,4,16,2,52,57,84⟩ = true := by decide +kernel
private theorem k586_2_2 : check w586 pick586 2 t11232 ⟨2,7,4,16,2,52,2,84⟩ = true := glue w586 pick586 2 ⟨2,7,4,16,2,52,2,84⟩ 3 56 t4112 t5946 k586_2_0 k586_2_1
private theorem k586_2_3 : check w586 pick586 2 t11233 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k586_2_4 : check w586 pick586 2 t11234 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w586 pick586 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t11232 t11233 k586_2_2 k586_2_3
private theorem k586_2_5 : check w586 pick586 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k586_2_6 : check w586 pick586 2 t11235 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k586_2_7 : check w586 pick586 2 t11236 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w586 pick586 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t11235 k586_2_5 k586_2_6
private theorem k586_2_8 : check w586 pick586 2 t11237 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w586 pick586 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11234 t11236 k586_2_4 k586_2_7
theorem cov586_2 : PA.Covered 2 (OZ.Valid 2 w586.low w586.t w586.y w586.r w586.cap) (P33.root 2) :=
  Night6836Tree.sound w586 pick586 2 t11237 _ k586_2_8
theorem cov586_3 : PA.Covered 3 (OZ.Valid 3 w586.low w586.t w586.y w586.r w586.cap) (P33.root 3) :=
  Night6836Tree.sound w586 pick586 3 t4231 _ (by decide +kernel)
theorem cov586_4 : PA.Covered 4 (OZ.Valid 4 w586.low w586.t w586.y w586.r w586.cap) (P33.root 4) :=
  Night6836Tree.sound w586 pick586 4 t565 _ (by decide +kernel)
theorem cov586_5 : PA.Covered 5 (OZ.Valid 5 w586.low w586.t w586.y w586.r w586.cap) (P33.root 5) :=
  Night6836Tree.sound w586 pick586 5 t566 _ (by decide +kernel)
theorem cov586_6 : PA.Covered 6 (OZ.Valid 6 w586.low w586.t w586.y w586.r w586.cap) (P33.root 6) :=
  Night6836Tree.sound w586 pick586 6 t567 _ (by decide +kernel)
theorem cov586_7 : PA.Covered 7 (OZ.Valid 7 w586.low w586.t w586.y w586.r w586.cap) (P33.root 7) :=
  Night6836Tree.sound w586 pick586 7 t2134 _ (by decide +kernel)
theorem window586 : P33.WindowCount w586 := by
  apply P33.window_count w586 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov586_1
  · exact cov586_2
  · exact cov586_3
  · exact cov586_4
  · exact cov586_5
  · exact cov586_6
  · exact cov586_7
def w587 : P33.Window := ⟨9,53,6080,5760,247109937036700148,45659,27000,5000000,81920000000⟩
def h587_0 : Height w587 := ⟨45659,27000,by decide +kernel⟩
def h587_1 : Height w587 := ⟨50298,24000,by decide +kernel⟩
def h587_2 : Height w587 := ⟨56355,21000,by decide +kernel⟩
def h587_3 : Height w587 := ⟨65063,18000,by decide +kernel⟩
def h587_4 : Height w587 := ⟨79673,15000,by decide +kernel⟩
def pick587 (cl : ℕ) : Height w587 := if cl<40 then (if cl<6 then (h587_0) else (h587_1)) else (if cl<260 then (h587_2) else (if cl<997 then (h587_3) else (h587_4)))
private theorem k587_1_0 : check w587 pick587 1 t4544 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k587_1_1 : check w587 pick587 1 t11186 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k587_1_2 : check w587 pick587 1 t11229 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w587 pick587 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t4544 t11186 k587_1_0 k587_1_1
private theorem k587_1_3 : check w587 pick587 1 t10778 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k587_1_4 : check w587 pick587 1 t10780 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k587_1_5 : check w587 pick587 1 t10781 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w587 pick587 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t10778 t10780 k587_1_3 k587_1_4
private theorem k587_1_6 : check w587 pick587 1 t11230 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w587 pick587 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t11229 t10781 k587_1_2 k587_1_5
private theorem k587_1_7 : check w587 pick587 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k587_1_8 : check w587 pick587 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k587_1_9 : check w587 pick587 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w587 pick587 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k587_1_7 k587_1_8
private theorem k587_1_10 : check w587 pick587 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k587_1_11 : check w587 pick587 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w587 pick587 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k587_1_9 k587_1_10
private theorem k587_1_12 : check w587 pick587 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k587_1_13 : check w587 pick587 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k587_1_14 : check w587 pick587 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w587 pick587 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k587_1_12 k587_1_13
private theorem k587_1_15 : check w587 pick587 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w587 pick587 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k587_1_11 k587_1_14
private theorem k587_1_16 : check w587 pick587 1 t11231 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w587 pick587 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t11230 t10752 k587_1_6 k587_1_15
theorem cov587_1 : PA.Covered 1 (OZ.Valid 1 w587.low w587.t w587.y w587.r w587.cap) (P33.root 1) :=
  Night6836Tree.sound w587 pick587 1 t11231 _ k587_1_16
private theorem k587_2_0 : check w587 pick587 2 t4930 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k587_2_1 : check w587 pick587 2 t4937 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k587_2_2 : check w587 pick587 2 t4938 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w587 pick587 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4930 t4937 k587_2_0 k587_2_1
private theorem k587_2_3 : check w587 pick587 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k587_2_4 : check w587 pick587 2 t10652 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k587_2_5 : check w587 pick587 2 t11238 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w587 pick587 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t10652 k587_2_3 k587_2_4
private theorem k587_2_6 : check w587 pick587 2 t11239 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w587 pick587 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t4938 t11238 k587_2_2 k587_2_5
theorem cov587_2 : PA.Covered 2 (OZ.Valid 2 w587.low w587.t w587.y w587.r w587.cap) (P33.root 2) :=
  Night6836Tree.sound w587 pick587 2 t11239 _ k587_2_6
theorem cov587_3 : PA.Covered 3 (OZ.Valid 3 w587.low w587.t w587.y w587.r w587.cap) (P33.root 3) :=
  Night6836Tree.sound w587 pick587 3 t4877 _ (by decide +kernel)
theorem cov587_4 : PA.Covered 4 (OZ.Valid 4 w587.low w587.t w587.y w587.r w587.cap) (P33.root 4) :=
  Night6836Tree.sound w587 pick587 4 t565 _ (by decide +kernel)
theorem cov587_5 : PA.Covered 5 (OZ.Valid 5 w587.low w587.t w587.y w587.r w587.cap) (P33.root 5) :=
  Night6836Tree.sound w587 pick587 5 t566 _ (by decide +kernel)
theorem cov587_6 : PA.Covered 6 (OZ.Valid 6 w587.low w587.t w587.y w587.r w587.cap) (P33.root 6) :=
  Night6836Tree.sound w587 pick587 6 t567 _ (by decide +kernel)
theorem cov587_7 : PA.Covered 7 (OZ.Valid 7 w587.low w587.t w587.y w587.r w587.cap) (P33.root 7) :=
  Night6836Tree.sound w587 pick587 7 t2134 _ (by decide +kernel)
theorem window587 : P33.WindowCount w587 := by
  apply P33.window_count w587 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov587_1
  · exact cov587_2
  · exact cov587_3
  · exact cov587_4
  · exact cov587_5
  · exact cov587_6
  · exact cov587_7
def w588 : P33.Window := ⟨9,54,5660,4711,245830596366993773,53409,36000,5000000,81920000000⟩
def h588_0 : Height w588 := ⟨53409,36000,by decide +kernel⟩
def h588_1 : Height w588 := ⟨57306,33000,by decide +kernel⟩
def h588_2 : Height w588 := ⟨61901,30000,by decide +kernel⟩
def h588_3 : Height w588 := ⟨67550,27000,by decide +kernel⟩
def h588_4 : Height w588 := ⟨74901,24000,by decide +kernel⟩
def h588_5 : Height w588 := ⟨85267,21000,by decide +kernel⟩
def h588_6 : Height w588 := ⟨101770,18000,by decide +kernel⟩
def pick588 (cl : ℕ) : Height w588 := if cl<27 then (if cl<2 then (h588_0) else (if cl<6 then (h588_1) else (h588_2))) else (if cl<644 then (if cl<115 then (h588_3) else (h588_4)) else (if cl<1021 then (h588_5) else (h588_6)))
private theorem k588_1_0 : check w588 pick588 1 t11243 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k588_1_1 : check w588 pick588 1 t11245 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k588_1_2 : check w588 pick588 1 t11246 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w588 pick588 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t11243 t11245 k588_1_0 k588_1_1
private theorem k588_1_3 : check w588 pick588 1 t6458 ⟨1,7,2,16,1,20,70,131⟩ = true := by decide +kernel
private theorem k588_1_4 : check w588 pick588 1 t11255 ⟨1,7,2,16,21,52,70,131⟩ = true := by decide +kernel
private theorem k588_1_5 : check w588 pick588 1 t11256 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w588 pick588 1 ⟨1,7,2,16,1,52,70,131⟩ 2 20 t6458 t11255 k588_1_3 k588_1_4
private theorem k588_1_6 : check w588 pick588 1 t11257 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w588 pick588 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t11246 t11256 k588_1_2 k588_1_5
private theorem k588_1_7 : check w588 pick588 1 t11260 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k588_1_8 : check w588 pick588 1 t3840 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k588_1_9 : check w588 pick588 1 t11261 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w588 pick588 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t11260 t3840 k588_1_7 k588_1_8
private theorem k588_1_10 : check w588 pick588 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k588_1_11 : check w588 pick588 1 t10521 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k588_1_12 : check w588 pick588 1 t11262 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w588 pick588 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t10521 k588_1_10 k588_1_11
private theorem k588_1_13 : check w588 pick588 1 t11263 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w588 pick588 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t11261 t11262 k588_1_9 k588_1_12
private theorem k588_1_14 : check w588 pick588 1 t11264 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w588 pick588 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t11257 t11263 k588_1_6 k588_1_13
theorem cov588_1 : PA.Covered 1 (OZ.Valid 1 w588.low w588.t w588.y w588.r w588.cap) (P33.root 1) :=
  Night6836Tree.sound w588 pick588 1 t11264 _ k588_1_14
private theorem k588_2_0 : check w588 pick588 2 t4994 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k588_2_1 : check w588 pick588 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k588_2_2 : check w588 pick588 2 t11139 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w588 pick588 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t4994 t3777 k588_2_0 k588_2_1
private theorem k588_2_3 : check w588 pick588 2 t4029 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k588_2_4 : check w588 pick588 2 t11265 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k588_2_5 : check w588 pick588 2 t11266 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w588 pick588 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4029 t11265 k588_2_3 k588_2_4
private theorem k588_2_6 : check w588 pick588 2 t11267 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w588 pick588 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t11139 t11266 k588_2_2 k588_2_5
theorem cov588_2 : PA.Covered 2 (OZ.Valid 2 w588.low w588.t w588.y w588.r w588.cap) (P33.root 2) :=
  Night6836Tree.sound w588 pick588 2 t11267 _ k588_2_6
theorem cov588_3 : PA.Covered 3 (OZ.Valid 3 w588.low w588.t w588.y w588.r w588.cap) (P33.root 3) :=
  Night6836Tree.sound w588 pick588 3 t564 _ (by decide +kernel)
theorem cov588_4 : PA.Covered 4 (OZ.Valid 4 w588.low w588.t w588.y w588.r w588.cap) (P33.root 4) :=
  Night6836Tree.sound w588 pick588 4 t565 _ (by decide +kernel)
theorem cov588_5 : PA.Covered 5 (OZ.Valid 5 w588.low w588.t w588.y w588.r w588.cap) (P33.root 5) :=
  Night6836Tree.sound w588 pick588 5 t566 _ (by decide +kernel)
theorem cov588_6 : PA.Covered 6 (OZ.Valid 6 w588.low w588.t w588.y w588.r w588.cap) (P33.root 6) :=
  Night6836Tree.sound w588 pick588 6 t567 _ (by decide +kernel)
theorem cov588_7 : PA.Covered 7 (OZ.Valid 7 w588.low w588.t w588.y w588.r w588.cap) (P33.root 7) :=
  Night6836Tree.sound w588 pick588 7 t2134 _ (by decide +kernel)
theorem window588 : P33.WindowCount w588 := by
  apply P33.window_count w588 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov588_1
  · exact cov588_2
  · exact cov588_3
  · exact cov588_4
  · exact cov588_5
  · exact cov588_6
  · exact cov588_7
def w589 : P33.Window := ⟨9,54,5759,5425,246984701251714519,47970,30000,5000000,81920000000⟩
def h589_0 : Height w589 := ⟨47970,30000,by decide +kernel⟩
def h589_1 : Height w589 := ⟨52233,27000,by decide +kernel⟩
def h589_2 : Height w589 := ⟨57544,24000,by decide +kernel⟩
def h589_3 : Height w589 := ⟨64636,21000,by decide +kernel⟩
def h589_4 : Height w589 := ⟨75134,18000,by decide +kernel⟩
def pick589 (cl : ℕ) : Height w589 := if cl<21 then (if cl<4 then (h589_0) else (h589_1)) else (if cl<97 then (h589_2) else (if cl<685 then (h589_3) else (h589_4)))
private theorem k589_1_0 : check w589 pick589 1 t11268 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k589_1_1 : check w589 pick589 1 t11271 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k589_1_2 : check w589 pick589 1 t11272 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w589 pick589 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t11268 t11271 k589_1_0 k589_1_1
private theorem k589_1_3 : check w589 pick589 1 t11275 ⟨1,7,2,16,1,20,77,138⟩ = true := by decide +kernel
private theorem k589_1_4 : check w589 pick589 1 t10514 ⟨1,7,2,16,21,52,77,138⟩ = true := by decide +kernel
private theorem k589_1_5 : check w589 pick589 1 t11276 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w589 pick589 1 ⟨1,7,2,16,1,52,77,138⟩ 2 20 t11275 t10514 k589_1_3 k589_1_4
private theorem k589_1_6 : check w589 pick589 1 t11277 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w589 pick589 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t11272 t11276 k589_1_2 k589_1_5
private theorem k589_1_7 : check w589 pick589 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k589_1_8 : check w589 pick589 1 t10685 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k589_1_9 : check w589 pick589 1 t10686 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w589 pick589 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t9740 t10685 k589_1_7 k589_1_8
private theorem k589_1_10 : check w589 pick589 1 t11279 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k589_1_11 : check w589 pick589 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k589_1_12 : check w589 pick589 1 t11280 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w589 pick589 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t11279 t10616 k589_1_10 k589_1_11
private theorem k589_1_13 : check w589 pick589 1 t11281 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w589 pick589 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t10686 t11280 k589_1_9 k589_1_12
private theorem k589_1_14 : check w589 pick589 1 t11282 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w589 pick589 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t11277 t11281 k589_1_6 k589_1_13
theorem cov589_1 : PA.Covered 1 (OZ.Valid 1 w589.low w589.t w589.y w589.r w589.cap) (P33.root 1) :=
  Night6836Tree.sound w589 pick589 1 t11282 _ k589_1_14
private theorem k589_2_0 : check w589 pick589 2 t9748 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k589_2_1 : check w589 pick589 2 t5002 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k589_2_2 : check w589 pick589 2 t9780 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w589 pick589 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9748 t5002 k589_2_0 k589_2_1
private theorem k589_2_3 : check w589 pick589 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k589_2_4 : check w589 pick589 2 t10652 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k589_2_5 : check w589 pick589 2 t11238 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w589 pick589 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t10652 k589_2_3 k589_2_4
private theorem k589_2_6 : check w589 pick589 2 t11283 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w589 pick589 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9780 t11238 k589_2_2 k589_2_5
theorem cov589_2 : PA.Covered 2 (OZ.Valid 2 w589.low w589.t w589.y w589.r w589.cap) (P33.root 2) :=
  Night6836Tree.sound w589 pick589 2 t11283 _ k589_2_6
theorem cov589_3 : PA.Covered 3 (OZ.Valid 3 w589.low w589.t w589.y w589.r w589.cap) (P33.root 3) :=
  Night6836Tree.sound w589 pick589 3 t564 _ (by decide +kernel)
theorem cov589_4 : PA.Covered 4 (OZ.Valid 4 w589.low w589.t w589.y w589.r w589.cap) (P33.root 4) :=
  Night6836Tree.sound w589 pick589 4 t565 _ (by decide +kernel)
theorem cov589_5 : PA.Covered 5 (OZ.Valid 5 w589.low w589.t w589.y w589.r w589.cap) (P33.root 5) :=
  Night6836Tree.sound w589 pick589 5 t566 _ (by decide +kernel)
theorem cov589_6 : PA.Covered 6 (OZ.Valid 6 w589.low w589.t w589.y w589.r w589.cap) (P33.root 6) :=
  Night6836Tree.sound w589 pick589 6 t567 _ (by decide +kernel)
theorem cov589_7 : PA.Covered 7 (OZ.Valid 7 w589.low w589.t w589.y w589.r w589.cap) (P33.root 7) :=
  Night6836Tree.sound w589 pick589 7 t2134 _ (by decide +kernel)
theorem window589 : P33.WindowCount w589 := by
  apply P33.window_count w589 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov589_1
  · exact cov589_2
  · exact cov589_3
  · exact cov589_4
  · exact cov589_5
  · exact cov589_6
  · exact cov589_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w590 : P33.Window := ⟨9,55,5424,5075,245927872446524503,51438,33000,5000000,81920000000⟩
def h590_0 : Height w590 := ⟨51438,33000,by decide +kernel⟩
def h590_1 : Height w590 := ⟨55501,30000,by decide +kernel⟩
def h590_2 : Height w590 := ⟨60405,27000,by decide +kernel⟩
def h590_3 : Height w590 := ⟨66647,24000,by decide +kernel⟩
def h590_4 : Height w590 := ⟨75202,21000,by decide +kernel⟩
def h590_5 : Height w590 := ⟨88302,18000,by decide +kernel⟩
def pick590 (cl : ℕ) : Height w590 := if cl<46 then (if cl<2 then (h590_0) else (if cl<13 then (h590_1) else (h590_2))) else (if cl<260 then (h590_3) else (if cl<961 then (h590_4) else (h590_5)))
private theorem k590_1_0 : check w590 pick590 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k590_1_1 : check w590 pick590 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k590_1_2 : check w590 pick590 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w590 pick590 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k590_1_0 k590_1_1
private theorem k590_1_3 : check w590 pick590 1 t5039 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k590_1_4 : check w590 pick590 1 t10058 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k590_1_5 : check w590 pick590 1 t10241 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w590 pick590 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t5039 t10058 k590_1_3 k590_1_4
private theorem k590_1_6 : check w590 pick590 1 t10242 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w590 pick590 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10234 t10241 k590_1_2 k590_1_5
private theorem k590_1_7 : check w590 pick590 1 t10061 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k590_1_8 : check w590 pick590 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k590_1_9 : check w590 pick590 1 t10062 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w590 pick590 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10061 t3123 k590_1_7 k590_1_8
private theorem k590_1_10 : check w590 pick590 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k590_1_11 : check w590 pick590 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k590_1_12 : check w590 pick590 1 t10065 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w590 pick590 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t10064 k590_1_10 k590_1_11
private theorem k590_1_13 : check w590 pick590 1 t10066 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w590 pick590 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10062 t10065 k590_1_9 k590_1_12
private theorem k590_1_14 : check w590 pick590 1 t10243 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w590 pick590 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10242 t10066 k590_1_6 k590_1_13
theorem cov590_1 : PA.Covered 1 (OZ.Valid 1 w590.low w590.t w590.y w590.r w590.cap) (P33.root 1) :=
  Night6836Tree.sound w590 pick590 1 t10243 _ k590_1_14
private theorem k590_2_0 : check w590 pick590 2 t3466 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k590_2_1 : check w590 pick590 2 t3777 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k590_2_2 : check w590 pick590 2 t3778 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w590 pick590 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t3466 t3777 k590_2_0 k590_2_1
private theorem k590_2_3 : check w590 pick590 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k590_2_4 : check w590 pick590 2 t4902 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k590_2_5 : check w590 pick590 2 t4903 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w590 pick590 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t4902 k590_2_3 k590_2_4
private theorem k590_2_6 : check w590 pick590 2 t4904 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w590 pick590 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t3778 t4903 k590_2_2 k590_2_5
theorem cov590_2 : PA.Covered 2 (OZ.Valid 2 w590.low w590.t w590.y w590.r w590.cap) (P33.root 2) :=
  Night6836Tree.sound w590 pick590 2 t4904 _ k590_2_6
theorem cov590_3 : PA.Covered 3 (OZ.Valid 3 w590.low w590.t w590.y w590.r w590.cap) (P33.root 3) :=
  Night6836Tree.sound w590 pick590 3 t564 _ (by decide +kernel)
theorem cov590_4 : PA.Covered 4 (OZ.Valid 4 w590.low w590.t w590.y w590.r w590.cap) (P33.root 4) :=
  Night6836Tree.sound w590 pick590 4 t565 _ (by decide +kernel)
theorem cov590_5 : PA.Covered 5 (OZ.Valid 5 w590.low w590.t w590.y w590.r w590.cap) (P33.root 5) :=
  Night6836Tree.sound w590 pick590 5 t566 _ (by decide +kernel)
theorem cov590_6 : PA.Covered 6 (OZ.Valid 6 w590.low w590.t w590.y w590.r w590.cap) (P33.root 6) :=
  Night6836Tree.sound w590 pick590 6 t567 _ (by decide +kernel)
theorem cov590_7 : PA.Covered 7 (OZ.Valid 7 w590.low w590.t w590.y w590.r w590.cap) (P33.root 7) :=
  Night6836Tree.sound w590 pick590 7 t2134 _ (by decide +kernel)
theorem window590 : P33.WindowCount w590 := by
  apply P33.window_count w590 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov590_1
  · exact cov590_2
  · exact cov590_3
  · exact cov590_4
  · exact cov590_5
  · exact cov590_6
  · exact cov590_7
def w591 : P33.Window := ⟨9,56,5074,4711,246476776563363712,56287,36000,5000000,81920000000⟩
def h591_0 : Height w591 := ⟨56287,36000,by decide +kernel⟩
def h591_1 : Height w591 := ⟨60279,33000,by decide +kernel⟩
def h591_2 : Height w591 := ⟨64996,30000,by decide +kernel⟩
def h591_3 : Height w591 := ⟨70810,27000,by decide +kernel⟩
def h591_4 : Height w591 := ⟨78391,24000,by decide +kernel⟩
def h591_5 : Height w591 := ⟨89105,21000,by decide +kernel⟩
def pick591 (cl : ℕ) : Height w591 := if cl<32 then (if cl<2 then (h591_0) else (if cl<10 then (h591_1) else (h591_2))) else (if cl<140 then (h591_3) else (if cl<853 then (h591_4) else (h591_5)))
private theorem k591_1_0 : check w591 pick591 1 t10535 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k591_1_1 : check w591 pick591 1 t10552 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k591_1_2 : check w591 pick591 1 t10553 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w591 pick591 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10535 t10552 k591_1_0 k591_1_1
private theorem k591_1_3 : check w591 pick591 1 t10566 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k591_1_4 : check w591 pick591 1 t10572 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k591_1_5 : check w591 pick591 1 t10573 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w591 pick591 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t10566 t10572 k591_1_3 k591_1_4
private theorem k591_1_6 : check w591 pick591 1 t10574 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w591 pick591 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t10553 t10573 k591_1_2 k591_1_5
private theorem k591_1_7 : check w591 pick591 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k591_1_8 : check w591 pick591 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k591_1_9 : check w591 pick591 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w591 pick591 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k591_1_7 k591_1_8
private theorem k591_1_10 : check w591 pick591 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k591_1_11 : check w591 pick591 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k591_1_12 : check w591 pick591 1 t10502 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w591 pick591 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10064 k591_1_10 k591_1_11
private theorem k591_1_13 : check w591 pick591 1 t10503 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w591 pick591 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t10502 k591_1_9 k591_1_12
private theorem k591_1_14 : check w591 pick591 1 t10575 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w591 pick591 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10574 t10503 k591_1_6 k591_1_13
theorem cov591_1 : PA.Covered 1 (OZ.Valid 1 w591.low w591.t w591.y w591.r w591.cap) (P33.root 1) :=
  Night6836Tree.sound w591 pick591 1 t10575 _ k591_1_14
private theorem k591_2_0 : check w591 pick591 2 t3321 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k591_2_1 : check w591 pick591 2 t11288 ⟨2,7,4,16,2,52,85,166⟩ = true := by decide +kernel
private theorem k591_2_2 : check w591 pick591 2 t11289 ⟨2,7,4,16,2,52,2,166⟩ = true := glue w591 pick591 2 ⟨2,7,4,16,2,52,2,166⟩ 3 84 t3321 t11288 k591_2_0 k591_2_1
private theorem k591_2_3 : check w591 pick591 2 t5127 ⟨2,7,4,16,2,52,167,450⟩ = true := by decide +kernel
private theorem k591_2_4 : check w591 pick591 2 t11290 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w591 pick591 2 ⟨2,7,4,16,0,52,0,450⟩ 3 166 t11289 t5127 k591_2_2 k591_2_3
theorem cov591_2 : PA.Covered 2 (OZ.Valid 2 w591.low w591.t w591.y w591.r w591.cap) (P33.root 2) :=
  Night6836Tree.sound w591 pick591 2 t11290 _ k591_2_4
theorem cov591_3 : PA.Covered 3 (OZ.Valid 3 w591.low w591.t w591.y w591.r w591.cap) (P33.root 3) :=
  Night6836Tree.sound w591 pick591 3 t564 _ (by decide +kernel)
theorem cov591_4 : PA.Covered 4 (OZ.Valid 4 w591.low w591.t w591.y w591.r w591.cap) (P33.root 4) :=
  Night6836Tree.sound w591 pick591 4 t565 _ (by decide +kernel)
theorem cov591_5 : PA.Covered 5 (OZ.Valid 5 w591.low w591.t w591.y w591.r w591.cap) (P33.root 5) :=
  Night6836Tree.sound w591 pick591 5 t566 _ (by decide +kernel)
theorem cov591_6 : PA.Covered 6 (OZ.Valid 6 w591.low w591.t w591.y w591.r w591.cap) (P33.root 6) :=
  Night6836Tree.sound w591 pick591 6 t567 _ (by decide +kernel)
theorem cov591_7 : PA.Covered 7 (OZ.Valid 7 w591.low w591.t w591.y w591.r w591.cap) (P33.root 7) :=
  Night6836Tree.sound w591 pick591 7 t2134 _ (by decide +kernel)
theorem window591 : P33.WindowCount w591 := by
  apply P33.window_count w591 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov591_1
  · exact cov591_2
  · exact cov591_3
  · exact cov591_4
  · exact cov591_5
  · exact cov591_6
  · exact cov591_7
def w592 : P33.Window := ⟨9,57,4710,4332,245413321713389402,62952,39000,5000000,81920000000⟩
def h592_0 : Height w592 := ⟨62952,39000,by decide +kernel⟩
def h592_1 : Height w592 := ⟨66991,36000,by decide +kernel⟩
def h592_2 : Height w592 := ⟨71697,33000,by decide +kernel⟩
def h592_3 : Height w592 := ⟨77374,30000,by decide +kernel⟩
def h592_4 : Height w592 := ⟨84541,27000,by decide +kernel⟩
def h592_5 : Height w592 := ⟨94162,24000,by decide +kernel⟩
def h592_6 : Height w592 := ⟨108263,21000,by decide +kernel⟩
def pick592 (cl : ℕ) : Height w592 := if cl<32 then (if cl<2 then (h592_0) else (if cl<10 then (h592_1) else (h592_2))) else (if cl<340 then (if cl<105 then (h592_3) else (h592_4)) else (if cl<989 then (h592_5) else (h592_6)))
private theorem k592_1_0 : check w592 pick592 1 t9154 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k592_1_1 : check w592 pick592 1 t11294 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k592_1_2 : check w592 pick592 1 t11295 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w592 pick592 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t9154 t11294 k592_1_0 k592_1_1
private theorem k592_1_3 : check w592 pick592 1 t11112 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k592_1_4 : check w592 pick592 1 t11296 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w592 pick592 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t11295 t11112 k592_1_2 k592_1_3
private theorem k592_1_5 : check w592 pick592 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k592_1_6 : check w592 pick592 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k592_1_7 : check w592 pick592 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w592 pick592 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k592_1_5 k592_1_6
private theorem k592_1_8 : check w592 pick592 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k592_1_9 : check w592 pick592 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k592_1_10 : check w592 pick592 1 t10502 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w592 pick592 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10064 k592_1_8 k592_1_9
private theorem k592_1_11 : check w592 pick592 1 t10503 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w592 pick592 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t10502 k592_1_7 k592_1_10
private theorem k592_1_12 : check w592 pick592 1 t11297 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w592 pick592 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t11296 t10503 k592_1_4 k592_1_11
theorem cov592_1 : PA.Covered 1 (OZ.Valid 1 w592.low w592.t w592.y w592.r w592.cap) (P33.root 1) :=
  Night6836Tree.sound w592 pick592 1 t11297 _ k592_1_12
private theorem k592_2_0 : check w592 pick592 2 t5184 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k592_2_1 : check w592 pick592 2 t5187 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k592_2_2 : check w592 pick592 2 t5188 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w592 pick592 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5184 t5187 k592_2_0 k592_2_1
theorem cov592_2 : PA.Covered 2 (OZ.Valid 2 w592.low w592.t w592.y w592.r w592.cap) (P33.root 2) :=
  Night6836Tree.sound w592 pick592 2 t5188 _ k592_2_2
theorem cov592_3 : PA.Covered 3 (OZ.Valid 3 w592.low w592.t w592.y w592.r w592.cap) (P33.root 3) :=
  Night6836Tree.sound w592 pick592 3 t564 _ (by decide +kernel)
theorem cov592_4 : PA.Covered 4 (OZ.Valid 4 w592.low w592.t w592.y w592.r w592.cap) (P33.root 4) :=
  Night6836Tree.sound w592 pick592 4 t565 _ (by decide +kernel)
theorem cov592_5 : PA.Covered 5 (OZ.Valid 5 w592.low w592.t w592.y w592.r w592.cap) (P33.root 5) :=
  Night6836Tree.sound w592 pick592 5 t566 _ (by decide +kernel)
theorem cov592_6 : PA.Covered 6 (OZ.Valid 6 w592.low w592.t w592.y w592.r w592.cap) (P33.root 6) :=
  Night6836Tree.sound w592 pick592 6 t567 _ (by decide +kernel)
theorem cov592_7 : PA.Covered 7 (OZ.Valid 7 w592.low w592.t w592.y w592.r w592.cap) (P33.root 7) :=
  Night6836Tree.sound w592 pick592 7 t2134 _ (by decide +kernel)
theorem window592 : P33.WindowCount w592 := by
  apply P33.window_count w592 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov592_1
  · exact cov592_2
  · exact cov592_3
  · exact cov592_4
  · exact cov592_5
  · exact cov592_6
  · exact cov592_7
def w593 : P33.Window := ⟨9,58,4331,3939,245750122777085277,72091,42000,5000000,81920000000⟩
def h593_0 : Height w593 := ⟨72091,42000,by decide +kernel⟩
def h593_1 : Height w593 := ⟨76304,39000,by decide +kernel⟩
def h593_2 : Height w593 := ⟨81174,36000,by decide +kernel⟩
def h593_3 : Height w593 := ⟨86969,33000,by decide +kernel⟩
def h593_4 : Height w593 := ⟨94132,30000,by decide +kernel⟩
def h593_5 : Height w593 := ⟨103436,27000,by decide +kernel⟩
def h593_6 : Height w593 := ⟨116373,24000,by decide +kernel⟩
def pick593 (cl : ℕ) : Height w593 := if cl<32 then (if cl<4 then (h593_0) else (if cl<13 then (h593_1) else (h593_2))) else (if cl<302 then (if cl<105 then (h593_3) else (h593_4)) else (if cl<989 then (h593_5) else (h593_6)))
private theorem k593_1_0 : check w593 pick593 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k593_1_1 : check w593 pick593 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k593_1_2 : check w593 pick593 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w593 pick593 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k593_1_0 k593_1_1
private theorem k593_1_3 : check w593 pick593 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k593_1_4 : check w593 pick593 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w593 pick593 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k593_1_2 k593_1_3
private theorem k593_1_5 : check w593 pick593 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k593_1_6 : check w593 pick593 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k593_1_7 : check w593 pick593 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w593 pick593 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k593_1_5 k593_1_6
private theorem k593_1_8 : check w593 pick593 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k593_1_9 : check w593 pick593 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k593_1_10 : check w593 pick593 1 t10863 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w593 pick593 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10862 k593_1_8 k593_1_9
private theorem k593_1_11 : check w593 pick593 1 t10864 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w593 pick593 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10863 k593_1_7 k593_1_10
private theorem k593_1_12 : check w593 pick593 1 t10865 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w593 pick593 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10864 k593_1_4 k593_1_11
theorem cov593_1 : PA.Covered 1 (OZ.Valid 1 w593.low w593.t w593.y w593.r w593.cap) (P33.root 1) :=
  Night6836Tree.sound w593 pick593 1 t10865 _ k593_1_12
theorem cov593_2 : PA.Covered 2 (OZ.Valid 2 w593.low w593.t w593.y w593.r w593.cap) (P33.root 2) :=
  Night6836Tree.sound w593 pick593 2 t11301 _ (by decide +kernel)
theorem cov593_3 : PA.Covered 3 (OZ.Valid 3 w593.low w593.t w593.y w593.r w593.cap) (P33.root 3) :=
  Night6836Tree.sound w593 pick593 3 t564 _ (by decide +kernel)
theorem cov593_4 : PA.Covered 4 (OZ.Valid 4 w593.low w593.t w593.y w593.r w593.cap) (P33.root 4) :=
  Night6836Tree.sound w593 pick593 4 t565 _ (by decide +kernel)
theorem cov593_5 : PA.Covered 5 (OZ.Valid 5 w593.low w593.t w593.y w593.r w593.cap) (P33.root 5) :=
  Night6836Tree.sound w593 pick593 5 t566 _ (by decide +kernel)
theorem cov593_6 : PA.Covered 6 (OZ.Valid 6 w593.low w593.t w593.y w593.r w593.cap) (P33.root 6) :=
  Night6836Tree.sound w593 pick593 6 t567 _ (by decide +kernel)
theorem cov593_7 : PA.Covered 7 (OZ.Valid 7 w593.low w593.t w593.y w593.r w593.cap) (P33.root 7) :=
  Night6836Tree.sound w593 pick593 7 t2134 _ (by decide +kernel)
theorem window593 : P33.WindowCount w593 := by
  apply P33.window_count w593 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov593_1
  · exact cov593_2
  · exact cov593_3
  · exact cov593_4
  · exact cov593_5
  · exact cov593_6
  · exact cov593_7
def w594 : P33.Window := ⟨9,59,3938,3530,244272966217031753,80875,48000,5000000,81920000000⟩
def h594_0 : Height w594 := ⟨80875,48000,by decide +kernel⟩
def h594_1 : Height w594 := ⟨84923,45000,by decide +kernel⟩
def h594_2 : Height w594 := ⟨89488,42000,by decide +kernel⟩
def h594_3 : Height w594 := ⟨94746,39000,by decide +kernel⟩
def h594_4 : Height w594 := ⟨100959,36000,by decide +kernel⟩
def h594_5 : Height w594 := ⟨108546,33000,by decide +kernel⟩
def h594_6 : Height w594 := ⟨118205,30000,by decide +kernel⟩
def pick594 (cl : ℕ) : Height w594 := if cl<32 then (if cl<2 then (h594_0) else (if cl<6 then (h594_1) else (h594_2))) else (if cl<145 then (if cl<44 then (h594_3) else (h594_4)) else (if cl<347 then (h594_5) else (h594_6)))
private theorem k594_1_0 : check w594 pick594 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k594_1_1 : check w594 pick594 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k594_1_2 : check w594 pick594 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w594 pick594 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k594_1_0 k594_1_1
private theorem k594_1_3 : check w594 pick594 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k594_1_4 : check w594 pick594 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w594 pick594 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k594_1_2 k594_1_3
private theorem k594_1_5 : check w594 pick594 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k594_1_6 : check w594 pick594 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k594_1_7 : check w594 pick594 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w594 pick594 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k594_1_5 k594_1_6
private theorem k594_1_8 : check w594 pick594 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k594_1_9 : check w594 pick594 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k594_1_10 : check w594 pick594 1 t10863 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w594 pick594 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10862 k594_1_8 k594_1_9
private theorem k594_1_11 : check w594 pick594 1 t10864 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w594 pick594 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10863 k594_1_7 k594_1_10
private theorem k594_1_12 : check w594 pick594 1 t10865 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w594 pick594 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10864 k594_1_4 k594_1_11
theorem cov594_1 : PA.Covered 1 (OZ.Valid 1 w594.low w594.t w594.y w594.r w594.cap) (P33.root 1) :=
  Night6836Tree.sound w594 pick594 1 t10865 _ k594_1_12
theorem cov594_2 : PA.Covered 2 (OZ.Valid 2 w594.low w594.t w594.y w594.r w594.cap) (P33.root 2) :=
  Night6836Tree.sound w594 pick594 2 t9593 _ (by decide +kernel)
theorem cov594_3 : PA.Covered 3 (OZ.Valid 3 w594.low w594.t w594.y w594.r w594.cap) (P33.root 3) :=
  Night6836Tree.sound w594 pick594 3 t564 _ (by decide +kernel)
theorem cov594_4 : PA.Covered 4 (OZ.Valid 4 w594.low w594.t w594.y w594.r w594.cap) (P33.root 4) :=
  Night6836Tree.sound w594 pick594 4 t565 _ (by decide +kernel)
theorem cov594_5 : PA.Covered 5 (OZ.Valid 5 w594.low w594.t w594.y w594.r w594.cap) (P33.root 5) :=
  Night6836Tree.sound w594 pick594 5 t566 _ (by decide +kernel)
theorem cov594_6 : PA.Covered 6 (OZ.Valid 6 w594.low w594.t w594.y w594.r w594.cap) (P33.root 6) :=
  Night6836Tree.sound w594 pick594 6 t567 _ (by decide +kernel)
theorem cov594_7 : PA.Covered 7 (OZ.Valid 7 w594.low w594.t w594.y w594.r w594.cap) (P33.root 7) :=
  Night6836Tree.sound w594 pick594 7 t2134 _ (by decide +kernel)
theorem window594 : P33.WindowCount w594 := by
  apply P33.window_count w594 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov594_1
  · exact cov594_2
  · exact cov594_3
  · exact cov594_4
  · exact cov594_5
  · exact cov594_6
  · exact cov594_7
def w595 : P33.Window := ⟨9,60,3529,3107,236985347481914530,94721,54000,5000000,81920000000⟩
def h595_0 : Height w595 := ⟨94721,54000,by decide +kernel⟩
def h595_1 : Height w595 := ⟨98852,51000,by decide +kernel⟩
def h595_2 : Height w595 := ⟨103448,48000,by decide +kernel⟩
def h595_3 : Height w595 := ⟨108644,45000,by decide +kernel⟩
def h595_4 : Height w595 := ⟨114634,42000,by decide +kernel⟩
def h595_5 : Height w595 := ⟨121704,39000,by decide +kernel⟩
def h595_6 : Height w595 := ⟨130293,36000,by decide +kernel⟩
def pick595 (cl : ℕ) : Height w595 := if cl<32 then (if cl<3 then (h595_0) else (if cl<6 then (h595_1) else (h595_2))) else (if cl<100 then (if cl<37 then (h595_3) else (h595_4)) else (if cl<260 then (h595_5) else (h595_6)))
private theorem k595_1_0 : check w595 pick595 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k595_1_1 : check w595 pick595 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k595_1_2 : check w595 pick595 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w595 pick595 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k595_1_0 k595_1_1
private theorem k595_1_3 : check w595 pick595 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k595_1_4 : check w595 pick595 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w595 pick595 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k595_1_2 k595_1_3
private theorem k595_1_5 : check w595 pick595 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k595_1_6 : check w595 pick595 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k595_1_7 : check w595 pick595 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w595 pick595 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k595_1_5 k595_1_6
private theorem k595_1_8 : check w595 pick595 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k595_1_9 : check w595 pick595 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k595_1_10 : check w595 pick595 1 t10863 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w595 pick595 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10862 k595_1_8 k595_1_9
private theorem k595_1_11 : check w595 pick595 1 t10864 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w595 pick595 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10863 k595_1_7 k595_1_10
private theorem k595_1_12 : check w595 pick595 1 t10865 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w595 pick595 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10864 k595_1_4 k595_1_11
theorem cov595_1 : PA.Covered 1 (OZ.Valid 1 w595.low w595.t w595.y w595.r w595.cap) (P33.root 1) :=
  Night6836Tree.sound w595 pick595 1 t10865 _ k595_1_12
theorem cov595_2 : PA.Covered 2 (OZ.Valid 2 w595.low w595.t w595.y w595.r w595.cap) (P33.root 2) :=
  Night6836Tree.sound w595 pick595 2 t5222 _ (by decide +kernel)
theorem cov595_3 : PA.Covered 3 (OZ.Valid 3 w595.low w595.t w595.y w595.r w595.cap) (P33.root 3) :=
  Night6836Tree.sound w595 pick595 3 t564 _ (by decide +kernel)
theorem cov595_4 : PA.Covered 4 (OZ.Valid 4 w595.low w595.t w595.y w595.r w595.cap) (P33.root 4) :=
  Night6836Tree.sound w595 pick595 4 t565 _ (by decide +kernel)
theorem cov595_5 : PA.Covered 5 (OZ.Valid 5 w595.low w595.t w595.y w595.r w595.cap) (P33.root 5) :=
  Night6836Tree.sound w595 pick595 5 t566 _ (by decide +kernel)
theorem cov595_6 : PA.Covered 6 (OZ.Valid 6 w595.low w595.t w595.y w595.r w595.cap) (P33.root 6) :=
  Night6836Tree.sound w595 pick595 6 t567 _ (by decide +kernel)
theorem cov595_7 : PA.Covered 7 (OZ.Valid 7 w595.low w595.t w595.y w595.r w595.cap) (P33.root 7) :=
  Night6836Tree.sound w595 pick595 7 t2134 _ (by decide +kernel)
theorem window595 : P33.WindowCount w595 := by
  apply P33.window_count w595 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov595_1
  · exact cov595_2
  · exact cov595_3
  · exact cov595_4
  · exact cov595_5
  · exact cov595_6
  · exact cov595_7
def w596 : P33.Window := ⟨9,61,3106,2669,235894925122319635,112560,63000,5000000,81920000000⟩
def h596_0 : Height w596 := ⟨112560,63000,by decide +kernel⟩
def h596_1 : Height w596 := ⟨116681,60000,by decide +kernel⟩
def h596_2 : Height w596 := ⟨121188,57000,by decide +kernel⟩
def h596_3 : Height w596 := ⟨126173,54000,by decide +kernel⟩
def h596_4 : Height w596 := ⟨131761,51000,by decide +kernel⟩
def h596_5 : Height w596 := ⟨138121,48000,by decide +kernel⟩
def h596_6 : Height w596 := ⟨145495,45000,by decide +kernel⟩
def h596_7 : Height w596 := ⟨154236,42000,by decide +kernel⟩
def pick596 (cl : ℕ) : Height w596 := if cl<32 then (if cl<6 then (if cl<3 then (h596_0) else (h596_1)) else (if cl<14 then (h596_2) else (h596_3))) else (if cl<117 then (if cl<51 then (h596_4) else (h596_5)) else (if cl<262 then (h596_6) else (h596_7)))
private theorem k596_1_0 : check w596 pick596 1 t5236 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k596_1_1 : check w596 pick596 1 t10911 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k596_1_2 : check w596 pick596 1 t10912 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w596 pick596 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5236 t10911 k596_1_0 k596_1_1
private theorem k596_1_3 : check w596 pick596 1 t10879 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k596_1_4 : check w596 pick596 1 t10888 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k596_1_5 : check w596 pick596 1 t10889 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w596 pick596 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10879 t10888 k596_1_3 k596_1_4
private theorem k596_1_6 : check w596 pick596 1 t10913 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w596 pick596 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10912 t10889 k596_1_2 k596_1_5
private theorem k596_1_7 : check w596 pick596 1 t10896 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k596_1_8 : check w596 pick596 1 t6586 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k596_1_9 : check w596 pick596 1 t10897 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w596 pick596 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10896 t6586 k596_1_7 k596_1_8
private theorem k596_1_10 : check w596 pick596 1 t6602 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k596_1_11 : check w596 pick596 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k596_1_12 : check w596 pick596 1 t10898 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w596 pick596 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6602 t10862 k596_1_10 k596_1_11
private theorem k596_1_13 : check w596 pick596 1 t10899 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w596 pick596 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10897 t10898 k596_1_9 k596_1_12
private theorem k596_1_14 : check w596 pick596 1 t10914 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w596 pick596 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10913 t10899 k596_1_6 k596_1_13
theorem cov596_1 : PA.Covered 1 (OZ.Valid 1 w596.low w596.t w596.y w596.r w596.cap) (P33.root 1) :=
  Night6836Tree.sound w596 pick596 1 t10914 _ k596_1_14
theorem cov596_2 : PA.Covered 2 (OZ.Valid 2 w596.low w596.t w596.y w596.r w596.cap) (P33.root 2) :=
  Night6836Tree.sound w596 pick596 2 t5222 _ (by decide +kernel)
theorem cov596_3 : PA.Covered 3 (OZ.Valid 3 w596.low w596.t w596.y w596.r w596.cap) (P33.root 3) :=
  Night6836Tree.sound w596 pick596 3 t564 _ (by decide +kernel)
theorem cov596_4 : PA.Covered 4 (OZ.Valid 4 w596.low w596.t w596.y w596.r w596.cap) (P33.root 4) :=
  Night6836Tree.sound w596 pick596 4 t565 _ (by decide +kernel)
theorem cov596_5 : PA.Covered 5 (OZ.Valid 5 w596.low w596.t w596.y w596.r w596.cap) (P33.root 5) :=
  Night6836Tree.sound w596 pick596 5 t566 _ (by decide +kernel)
theorem cov596_6 : PA.Covered 6 (OZ.Valid 6 w596.low w596.t w596.y w596.r w596.cap) (P33.root 6) :=
  Night6836Tree.sound w596 pick596 6 t567 _ (by decide +kernel)
theorem cov596_7 : PA.Covered 7 (OZ.Valid 7 w596.low w596.t w596.y w596.r w596.cap) (P33.root 7) :=
  Night6836Tree.sound w596 pick596 7 t2134 _ (by decide +kernel)
theorem window596 : P33.WindowCount w596 := by
  apply P33.window_count w596 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov596_1
  · exact cov596_2
  · exact cov596_3
  · exact cov596_4
  · exact cov596_5
  · exact cov596_6
  · exact cov596_7
def w597 : P33.Window := ⟨9,62,2668,2216,217202074418239748,135756,78000,5000000,81920000000⟩
def h597_0 : Height w597 := ⟨135756,78000,by decide +kernel⟩
def h597_1 : Height w597 := ⟨139685,75000,by decide +kernel⟩
def h597_2 : Height w597 := ⟨143891,72000,by decide +kernel⟩
def h597_3 : Height w597 := ⟨148426,69000,by decide +kernel⟩
def h597_4 : Height w597 := ⟨153352,66000,by decide +kernel⟩
def h597_5 : Height w597 := ⟨158750,63000,by decide +kernel⟩
def h597_6 : Height w597 := ⟨164724,60000,by decide +kernel⟩
def h597_7 : Height w597 := ⟨171413,57000,by decide +kernel⟩
def h597_8 : Height w597 := ⟨179001,54000,by decide +kernel⟩
def h597_9 : Height w597 := ⟨187743,51000,by decide +kernel⟩
def h597_10 : Height w597 := ⟨197999,48000,by decide +kernel⟩
def pick597 (cl : ℕ) : Height w597 := if cl<32 then (if cl<4 then (if cl<2 then (h597_0) else (h597_1)) else (if cl<6 then (h597_2) else (if cl<13 then (h597_3) else (h597_4)))) else (if cl<145 then (if cl<37 then (h597_5) else (if cl<83 then (h597_6) else (h597_7))) else (if cl<262 then (h597_8) else (if cl<615 then (h597_9) else (h597_10))))
private theorem k597_1_0 : check w597 pick597 1 t5236 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k597_1_1 : check w597 pick597 1 t10920 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k597_1_2 : check w597 pick597 1 t10921 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w597 pick597 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5236 t10920 k597_1_0 k597_1_1
private theorem k597_1_3 : check w597 pick597 1 t10879 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k597_1_4 : check w597 pick597 1 t11306 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k597_1_5 : check w597 pick597 1 t11307 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w597 pick597 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10879 t11306 k597_1_3 k597_1_4
private theorem k597_1_6 : check w597 pick597 1 t11308 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w597 pick597 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10921 t11307 k597_1_2 k597_1_5
private theorem k597_1_7 : check w597 pick597 1 t10896 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k597_1_8 : check w597 pick597 1 t6586 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k597_1_9 : check w597 pick597 1 t10897 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w597 pick597 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10896 t6586 k597_1_7 k597_1_8
private theorem k597_1_10 : check w597 pick597 1 t6602 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k597_1_11 : check w597 pick597 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k597_1_12 : check w597 pick597 1 t10898 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w597 pick597 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6602 t10862 k597_1_10 k597_1_11
private theorem k597_1_13 : check w597 pick597 1 t10899 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w597 pick597 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10897 t10898 k597_1_9 k597_1_12
private theorem k597_1_14 : check w597 pick597 1 t11309 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w597 pick597 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t11308 t10899 k597_1_6 k597_1_13
theorem cov597_1 : PA.Covered 1 (OZ.Valid 1 w597.low w597.t w597.y w597.r w597.cap) (P33.root 1) :=
  Night6836Tree.sound w597 pick597 1 t11309 _ k597_1_14
theorem cov597_2 : PA.Covered 2 (OZ.Valid 2 w597.low w597.t w597.y w597.r w597.cap) (P33.root 2) :=
  Night6836Tree.sound w597 pick597 2 t5222 _ (by decide +kernel)
theorem cov597_3 : PA.Covered 3 (OZ.Valid 3 w597.low w597.t w597.y w597.r w597.cap) (P33.root 3) :=
  Night6836Tree.sound w597 pick597 3 t564 _ (by decide +kernel)
theorem cov597_4 : PA.Covered 4 (OZ.Valid 4 w597.low w597.t w597.y w597.r w597.cap) (P33.root 4) :=
  Night6836Tree.sound w597 pick597 4 t565 _ (by decide +kernel)
theorem cov597_5 : PA.Covered 5 (OZ.Valid 5 w597.low w597.t w597.y w597.r w597.cap) (P33.root 5) :=
  Night6836Tree.sound w597 pick597 5 t566 _ (by decide +kernel)
theorem cov597_6 : PA.Covered 6 (OZ.Valid 6 w597.low w597.t w597.y w597.r w597.cap) (P33.root 6) :=
  Night6836Tree.sound w597 pick597 6 t567 _ (by decide +kernel)
theorem cov597_7 : PA.Covered 7 (OZ.Valid 7 w597.low w597.t w597.y w597.r w597.cap) (P33.root 7) :=
  Night6836Tree.sound w597 pick597 7 t2134 _ (by decide +kernel)
theorem window597 : P33.WindowCount w597 := by
  apply P33.window_count w597 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov597_1
  · exact cov597_2
  · exact cov597_3
  · exact cov597_4
  · exact cov597_5
  · exact cov597_6
  · exact cov597_7
def w598 : P33.Window := ⟨9,63,2215,1930,237397839371624257,158666,90000,5000000,81920000000⟩
def h598_0 : Height w598 := ⟨158666,90000,by decide +kernel⟩
def h598_1 : Height w598 := ⟨162575,87000,by decide +kernel⟩
def h598_2 : Height w598 := ⟨166717,84000,by decide +kernel⟩
def h598_3 : Height w598 := ⟨171130,81000,by decide +kernel⟩
def h598_4 : Height w598 := ⟨175856,78000,by decide +kernel⟩
def h598_5 : Height w598 := ⟨180948,75000,by decide +kernel⟩
def h598_6 : Height w598 := ⟨186473,72000,by decide +kernel⟩
def h598_7 : Height w598 := ⟨192513,69000,by decide +kernel⟩
def h598_8 : Height w598 := ⟨199174,66000,by decide +kernel⟩
def h598_9 : Height w598 := ⟨206592,63000,by decide +kernel⟩
def h598_10 : Height w598 := ⟨214945,60000,by decide +kernel⟩
def h598_11 : Height w598 := ⟨224473,57000,by decide +kernel⟩
def pick598 (cl : ℕ) : Height w598 := if cl<32 then (if cl<5 then (if cl<2 then (h598_0) else (if cl<3 then (h598_1) else (h598_2))) else (if cl<10 then (h598_3) else (if cl<16 then (h598_4) else (h598_5)))) else (if cl<132 then (if cl<40 then (h598_6) else (if cl<70 then (h598_7) else (h598_8))) else (if cl<216 then (h598_9) else (if cl<331 then (h598_10) else (h598_11))))
private theorem k598_1_0 : check w598 pick598 1 t5236 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k598_1_1 : check w598 pick598 1 t11315 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k598_1_2 : check w598 pick598 1 t11316 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w598 pick598 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5236 t11315 k598_1_0 k598_1_1
private theorem k598_1_3 : check w598 pick598 1 t10879 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k598_1_4 : check w598 pick598 1 t11332 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k598_1_5 : check w598 pick598 1 t11333 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w598 pick598 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10879 t11332 k598_1_3 k598_1_4
private theorem k598_1_6 : check w598 pick598 1 t11334 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w598 pick598 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t11316 t11333 k598_1_2 k598_1_5
private theorem k598_1_7 : check w598 pick598 1 t10896 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k598_1_8 : check w598 pick598 1 t6586 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k598_1_9 : check w598 pick598 1 t10897 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w598 pick598 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10896 t6586 k598_1_7 k598_1_8
private theorem k598_1_10 : check w598 pick598 1 t6602 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k598_1_11 : check w598 pick598 1 t11341 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k598_1_12 : check w598 pick598 1 t11342 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w598 pick598 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6602 t11341 k598_1_10 k598_1_11
private theorem k598_1_13 : check w598 pick598 1 t11343 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w598 pick598 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10897 t11342 k598_1_9 k598_1_12
private theorem k598_1_14 : check w598 pick598 1 t11344 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w598 pick598 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t11334 t11343 k598_1_6 k598_1_13
theorem cov598_1 : PA.Covered 1 (OZ.Valid 1 w598.low w598.t w598.y w598.r w598.cap) (P33.root 1) :=
  Night6836Tree.sound w598 pick598 1 t11344 _ k598_1_14
theorem cov598_2 : PA.Covered 2 (OZ.Valid 2 w598.low w598.t w598.y w598.r w598.cap) (P33.root 2) :=
  Night6836Tree.sound w598 pick598 2 t5283 _ (by decide +kernel)
theorem cov598_3 : PA.Covered 3 (OZ.Valid 3 w598.low w598.t w598.y w598.r w598.cap) (P33.root 3) :=
  Night6836Tree.sound w598 pick598 3 t564 _ (by decide +kernel)
theorem cov598_4 : PA.Covered 4 (OZ.Valid 4 w598.low w598.t w598.y w598.r w598.cap) (P33.root 4) :=
  Night6836Tree.sound w598 pick598 4 t565 _ (by decide +kernel)
theorem cov598_5 : PA.Covered 5 (OZ.Valid 5 w598.low w598.t w598.y w598.r w598.cap) (P33.root 5) :=
  Night6836Tree.sound w598 pick598 5 t566 _ (by decide +kernel)
theorem cov598_6 : PA.Covered 6 (OZ.Valid 6 w598.low w598.t w598.y w598.r w598.cap) (P33.root 6) :=
  Night6836Tree.sound w598 pick598 6 t567 _ (by decide +kernel)
theorem cov598_7 : PA.Covered 7 (OZ.Valid 7 w598.low w598.t w598.y w598.r w598.cap) (P33.root 7) :=
  Night6836Tree.sound w598 pick598 7 t2134 _ (by decide +kernel)
theorem window598 : P33.WindowCount w598 := by
  apply P33.window_count w598 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov598_1
  · exact cov598_2
  · exact cov598_3
  · exact cov598_4
  · exact cov598_5
  · exact cov598_6
  · exact cov598_7
def w599 : P33.Window := ⟨12,35,6846,6000,244983515187839630,5208,50000,5000000,81920000000⟩
def h599_0 : Height w599 := ⟨5208,50000,by decide +kernel⟩
def pick599 (cl : ℕ) : Height w599 := h599_0
private theorem k599_1_0 : check w599 pick599 1 t11359 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k599_1_1 : check w599 pick599 1 t11372 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k599_1_2 : check w599 pick599 1 t11373 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w599 pick599 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t11359 t11372 k599_1_0 k599_1_1
private theorem k599_1_3 : check w599 pick599 1 t11378 ⟨1,7,2,16,1,20,70,124⟩ = true := by decide +kernel
private theorem k599_1_4 : check w599 pick599 1 t11396 ⟨1,7,2,16,21,52,70,124⟩ = true := by decide +kernel
private theorem k599_1_5 : check w599 pick599 1 t11397 ⟨1,7,2,16,1,52,70,124⟩ = true := glue w599 pick599 1 ⟨1,7,2,16,1,52,70,124⟩ 2 20 t11378 t11396 k599_1_3 k599_1_4
private theorem k599_1_6 : check w599 pick599 1 t11398 ⟨1,7,2,16,1,52,1,124⟩ = true := glue w599 pick599 1 ⟨1,7,2,16,1,52,1,124⟩ 3 69 t11373 t11397 k599_1_2 k599_1_5
private theorem k599_1_7 : check w599 pick599 1 t11403 ⟨1,7,2,16,1,52,125,152⟩ = true := by decide +kernel
private theorem k599_1_8 : check w599 pick599 1 t11408 ⟨1,7,2,16,1,52,153,186⟩ = true := by decide +kernel
private theorem k599_1_9 : check w599 pick599 1 t11409 ⟨1,7,2,16,1,52,125,186⟩ = true := glue w599 pick599 1 ⟨1,7,2,16,1,52,125,186⟩ 3 152 t11403 t11408 k599_1_7 k599_1_8
private theorem k599_1_10 : check w599 pick599 1 t11413 ⟨1,7,2,16,1,52,187,219⟩ = true := by decide +kernel
private theorem k599_1_11 : check w599 pick599 1 t11416 ⟨1,7,2,16,1,52,220,329⟩ = true := by decide +kernel
private theorem k599_1_12 : check w599 pick599 1 t11417 ⟨1,7,2,16,1,52,187,329⟩ = true := glue w599 pick599 1 ⟨1,7,2,16,1,52,187,329⟩ 3 219 t11413 t11416 k599_1_10 k599_1_11
private theorem k599_1_13 : check w599 pick599 1 t11418 ⟨1,7,2,16,1,52,125,329⟩ = true := glue w599 pick599 1 ⟨1,7,2,16,1,52,125,329⟩ 3 186 t11409 t11417 k599_1_9 k599_1_12
private theorem k599_1_14 : check w599 pick599 1 t11419 ⟨1,7,2,16,1,52,1,329⟩ = true := glue w599 pick599 1 ⟨1,7,2,16,1,52,1,329⟩ 3 124 t11398 t11418 k599_1_6 k599_1_13
private theorem k599_1_15 : check w599 pick599 1 t11490 ⟨1,1,2,13,1,52,330,450⟩ = true := by decide +kernel
private theorem k599_1_16 : check w599 pick599 1 t11561 ⟨2,2,2,13,1,52,330,450⟩ = true := by decide +kernel
private theorem k599_1_17 : check w599 pick599 1 t11562 ⟨1,2,2,13,1,52,330,450⟩ = true := glue w599 pick599 1 ⟨1,2,2,13,1,52,330,450⟩ 0 1 t11490 t11561 k599_1_15 k599_1_16
private theorem k599_1_18 : check w599 pick599 1 t11651 ⟨3,6,6,13,3,47,330,450⟩ = true := by decide +kernel
private theorem k599_1_19 : check w599 pick599 1 t11738 ⟨3,6,6,13,48,52,330,450⟩ = true := by decide +kernel
private theorem k599_1_20 : check w599 pick599 1 t11739 ⟨3,6,2,13,1,52,330,450⟩ = true := glue w599 pick599 1 ⟨3,6,2,13,1,52,330,450⟩ 2 47 t11651 t11738 k599_1_18 k599_1_19
private theorem k599_1_21 : check w599 pick599 1 t11740 ⟨1,7,2,13,1,52,330,450⟩ = true := glue w599 pick599 1 ⟨1,7,2,13,1,52,330,450⟩ 0 2 t11562 t11739 k599_1_17 k599_1_20
private theorem k599_1_22 : check w599 pick599 1 t11818 ⟨1,3,14,16,7,47,330,450⟩ = true := by decide +kernel
private theorem k599_1_23 : check w599 pick599 1 t11919 ⟨4,7,14,16,7,47,330,450⟩ = true := by decide +kernel
private theorem k599_1_24 : check w599 pick599 1 t11920 ⟨1,7,14,16,7,47,330,450⟩ = true := glue w599 pick599 1 ⟨1,7,14,16,7,47,330,450⟩ 0 3 t11818 t11919 k599_1_22 k599_1_23
private theorem k599_1_25 : check w599 pick599 1 t11973 ⟨1,2,14,16,48,52,330,450⟩ = true := by decide +kernel
private theorem k599_1_26 : check w599 pick599 1 t12040 ⟨3,4,14,16,48,52,330,450⟩ = true := by decide +kernel
private theorem k599_1_27 : check w599 pick599 1 t12041 ⟨1,4,14,16,48,52,330,450⟩ = true := glue w599 pick599 1 ⟨1,4,14,16,48,52,330,450⟩ 0 2 t11973 t12040 k599_1_25 k599_1_26
private theorem k599_1_28 : check w599 pick599 1 t12129 ⟨5,7,14,16,48,52,330,450⟩ = true := by decide +kernel
private theorem k599_1_29 : check w599 pick599 1 t12130 ⟨1,7,14,16,48,52,330,450⟩ = true := glue w599 pick599 1 ⟨1,7,14,16,48,52,330,450⟩ 0 4 t12041 t12129 k599_1_27 k599_1_28
private theorem k599_1_30 : check w599 pick599 1 t12131 ⟨1,7,14,16,1,52,330,450⟩ = true := glue w599 pick599 1 ⟨1,7,14,16,1,52,330,450⟩ 2 47 t11920 t12130 k599_1_24 k599_1_29
private theorem k599_1_31 : check w599 pick599 1 t12132 ⟨1,7,2,16,1,52,330,450⟩ = true := glue w599 pick599 1 ⟨1,7,2,16,1,52,330,450⟩ 1 13 t11740 t12131 k599_1_21 k599_1_30
private theorem k599_1_32 : check w599 pick599 1 t12133 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w599 pick599 1 ⟨1,7,2,16,0,52,0,450⟩ 3 329 t11419 t12132 k599_1_14 k599_1_31
theorem cov599_1 : PA.Covered 1 (OZ.Valid 1 w599.low w599.t w599.y w599.r w599.cap) (P33.root 1) :=
  Night6836Tree.sound w599 pick599 1 t12133 _ k599_1_32
private theorem k599_2_0 : check w599 pick599 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k599_2_1 : check w599 pick599 2 t5723 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k599_2_2 : check w599 pick599 2 t5724 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w599 pick599 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5723 k599_2_0 k599_2_1
private theorem k599_2_3 : check w599 pick599 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k599_2_4 : check w599 pick599 2 t8612 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k599_2_5 : check w599 pick599 2 t8613 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w599 pick599 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t8612 k599_2_3 k599_2_4
private theorem k599_2_6 : check w599 pick599 2 t12134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w599 pick599 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5724 t8613 k599_2_2 k599_2_5
theorem cov599_2 : PA.Covered 2 (OZ.Valid 2 w599.low w599.t w599.y w599.r w599.cap) (P33.root 2) :=
  Night6836Tree.sound w599 pick599 2 t12134 _ k599_2_6
theorem cov599_3 : PA.Covered 3 (OZ.Valid 3 w599.low w599.t w599.y w599.r w599.cap) (P33.root 3) :=
  Night6836Tree.sound w599 pick599 3 t4151 _ (by decide +kernel)
theorem cov599_4 : PA.Covered 4 (OZ.Valid 4 w599.low w599.t w599.y w599.r w599.cap) (P33.root 4) :=
  Night6836Tree.sound w599 pick599 4 t565 _ (by decide +kernel)
theorem cov599_5 : PA.Covered 5 (OZ.Valid 5 w599.low w599.t w599.y w599.r w599.cap) (P33.root 5) :=
  Night6836Tree.sound w599 pick599 5 t566 _ (by decide +kernel)
theorem cov599_6 : PA.Covered 6 (OZ.Valid 6 w599.low w599.t w599.y w599.r w599.cap) (P33.root 6) :=
  Night6836Tree.sound w599 pick599 6 t567 _ (by decide +kernel)
theorem cov599_7 : PA.Covered 7 (OZ.Valid 7 w599.low w599.t w599.y w599.r w599.cap) (P33.root 7) :=
  Night6836Tree.sound w599 pick599 7 t568 _ (by decide +kernel)
theorem window599 : P33.WindowCount w599 := by
  apply P33.window_count w599 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov599_1
  · exact cov599_2
  · exact cov599_3
  · exact cov599_4
  · exact cov599_5
  · exact cov599_6
  · exact cov599_7
end ProximityPrize.SubmissionLower.Night6836Bank
