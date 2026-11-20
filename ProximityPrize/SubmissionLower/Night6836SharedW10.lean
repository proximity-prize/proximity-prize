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
def w300 : P33.Window := ⟨15,26,5608,5423,241100007567223603,16623,30000,5000000,81920000000⟩
def h300_0 : Height w300 := ⟨16623,30000,by decide +kernel⟩
def h300_1 : Height w300 := ⟨21421,27000,by decide +kernel⟩
def h300_2 : Height w300 := ⟨28146,24000,by decide +kernel⟩
def h300_3 : Height w300 := ⟨39163,21000,by decide +kernel⟩
def pick300 (cl : ℕ) : Height w300 := if cl<83 then (if cl<8 then (h300_0) else (h300_1)) else (if cl<922 then (h300_2) else (h300_3))
private theorem k300_1_0 : check w300 pick300 1 t7116 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k300_1_1 : check w300 pick300 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k300_1_2 : check w300 pick300 1 t7117 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w300 pick300 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7116 t7032 k300_1_0 k300_1_1
private theorem k300_1_3 : check w300 pick300 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k300_1_4 : check w300 pick300 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k300_1_5 : check w300 pick300 1 t7219 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w300 pick300 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t7097 k300_1_3 k300_1_4
private theorem k300_1_6 : check w300 pick300 1 t9060 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w300 pick300 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7117 t7219 k300_1_2 k300_1_5
theorem cov300_1 : PA.Covered 1 (OZ.Valid 1 w300.low w300.t w300.y w300.r w300.cap) (P33.root 1) :=
  Night6836Tree.sound w300 pick300 1 t9060 _ k300_1_6
theorem cov300_2 : PA.Covered 2 (OZ.Valid 2 w300.low w300.t w300.y w300.r w300.cap) (P33.root 2) :=
  Night6836Tree.sound w300 pick300 2 t7224 _ (by decide +kernel)
theorem cov300_3 : PA.Covered 3 (OZ.Valid 3 w300.low w300.t w300.y w300.r w300.cap) (P33.root 3) :=
  Night6836Tree.sound w300 pick300 3 t564 _ (by decide +kernel)
theorem cov300_4 : PA.Covered 4 (OZ.Valid 4 w300.low w300.t w300.y w300.r w300.cap) (P33.root 4) :=
  Night6836Tree.sound w300 pick300 4 t565 _ (by decide +kernel)
theorem cov300_5 : PA.Covered 5 (OZ.Valid 5 w300.low w300.t w300.y w300.r w300.cap) (P33.root 5) :=
  Night6836Tree.sound w300 pick300 5 t566 _ (by decide +kernel)
theorem cov300_6 : PA.Covered 6 (OZ.Valid 6 w300.low w300.t w300.y w300.r w300.cap) (P33.root 6) :=
  Night6836Tree.sound w300 pick300 6 t567 _ (by decide +kernel)
theorem cov300_7 : PA.Covered 7 (OZ.Valid 7 w300.low w300.t w300.y w300.r w300.cap) (P33.root 7) :=
  Night6836Tree.sound w300 pick300 7 t2134 _ (by decide +kernel)
theorem window300 : P33.WindowCount w300 := by
  apply P33.window_count w300 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov300_1
  · exact cov300_2
  · exact cov300_3
  · exact cov300_4
  · exact cov300_5
  · exact cov300_6
  · exact cov300_7
def w301 : P33.Window := ⟨15,27,5422,5233,241427124289532804,16416,33000,5000000,81920000000⟩
def h301_0 : Height w301 := ⟨16416,33000,by decide +kernel⟩
def h301_1 : Height w301 := ⟨20637,30000,by decide +kernel⟩
def h301_2 : Height w301 := ⟨26135,27000,by decide +kernel⟩
def h301_3 : Height w301 := ⟨34081,24000,by decide +kernel⟩
def pick301 (cl : ℕ) : Height w301 := if cl<32 then (if cl<4 then (h301_0) else (h301_1)) else (if cl<302 then (h301_2) else (h301_3))
private theorem k301_1_0 : check w301 pick301 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k301_1_1 : check w301 pick301 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k301_1_2 : check w301 pick301 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w301 pick301 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k301_1_0 k301_1_1
private theorem k301_1_3 : check w301 pick301 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k301_1_4 : check w301 pick301 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k301_1_5 : check w301 pick301 1 t7219 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w301 pick301 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t7097 k301_1_3 k301_1_4
private theorem k301_1_6 : check w301 pick301 1 t8460 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w301 pick301 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t7219 k301_1_2 k301_1_5
theorem cov301_1 : PA.Covered 1 (OZ.Valid 1 w301.low w301.t w301.y w301.r w301.cap) (P33.root 1) :=
  Night6836Tree.sound w301 pick301 1 t8460 _ k301_1_6
theorem cov301_2 : PA.Covered 2 (OZ.Valid 2 w301.low w301.t w301.y w301.r w301.cap) (P33.root 2) :=
  Night6836Tree.sound w301 pick301 2 t5320 _ (by decide +kernel)
theorem cov301_3 : PA.Covered 3 (OZ.Valid 3 w301.low w301.t w301.y w301.r w301.cap) (P33.root 3) :=
  Night6836Tree.sound w301 pick301 3 t564 _ (by decide +kernel)
theorem cov301_4 : PA.Covered 4 (OZ.Valid 4 w301.low w301.t w301.y w301.r w301.cap) (P33.root 4) :=
  Night6836Tree.sound w301 pick301 4 t565 _ (by decide +kernel)
theorem cov301_5 : PA.Covered 5 (OZ.Valid 5 w301.low w301.t w301.y w301.r w301.cap) (P33.root 5) :=
  Night6836Tree.sound w301 pick301 5 t566 _ (by decide +kernel)
theorem cov301_6 : PA.Covered 6 (OZ.Valid 6 w301.low w301.t w301.y w301.r w301.cap) (P33.root 6) :=
  Night6836Tree.sound w301 pick301 6 t567 _ (by decide +kernel)
theorem cov301_7 : PA.Covered 7 (OZ.Valid 7 w301.low w301.t w301.y w301.r w301.cap) (P33.root 7) :=
  Night6836Tree.sound w301 pick301 7 t2134 _ (by decide +kernel)
theorem window301 : P33.WindowCount w301 := by
  apply P33.window_count w301 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov301_1
  · exact cov301_2
  · exact cov301_3
  · exact cov301_4
  · exact cov301_5
  · exact cov301_6
  · exact cov301_7
def w302 : P33.Window := ⟨15,28,5232,5038,237411770927764968,20533,33000,5000000,81920000000⟩
def h302_0 : Height w302 := ⟨20533,33000,by decide +kernel⟩
def h302_1 : Height w302 := ⟨25324,30000,by decide +kernel⟩
def h302_2 : Height w302 := ⟨31727,27000,by decide +kernel⟩
def h302_3 : Height w302 := ⟨41303,24000,by decide +kernel⟩
def pick302 (cl : ℕ) : Height w302 := if cl<55 then (if cl<8 then (h302_0) else (h302_1)) else (if cl<331 then (h302_2) else (h302_3))
private theorem k302_1_0 : check w302 pick302 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k302_1_1 : check w302 pick302 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k302_1_2 : check w302 pick302 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w302 pick302 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k302_1_0 k302_1_1
private theorem k302_1_3 : check w302 pick302 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k302_1_4 : check w302 pick302 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k302_1_5 : check w302 pick302 1 t7219 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w302 pick302 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t7097 k302_1_3 k302_1_4
private theorem k302_1_6 : check w302 pick302 1 t8460 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w302 pick302 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t7219 k302_1_2 k302_1_5
theorem cov302_1 : PA.Covered 1 (OZ.Valid 1 w302.low w302.t w302.y w302.r w302.cap) (P33.root 1) :=
  Night6836Tree.sound w302 pick302 1 t8460 _ k302_1_6
theorem cov302_2 : PA.Covered 2 (OZ.Valid 2 w302.low w302.t w302.y w302.r w302.cap) (P33.root 2) :=
  Night6836Tree.sound w302 pick302 2 t5320 _ (by decide +kernel)
theorem cov302_3 : PA.Covered 3 (OZ.Valid 3 w302.low w302.t w302.y w302.r w302.cap) (P33.root 3) :=
  Night6836Tree.sound w302 pick302 3 t564 _ (by decide +kernel)
theorem cov302_4 : PA.Covered 4 (OZ.Valid 4 w302.low w302.t w302.y w302.r w302.cap) (P33.root 4) :=
  Night6836Tree.sound w302 pick302 4 t565 _ (by decide +kernel)
theorem cov302_5 : PA.Covered 5 (OZ.Valid 5 w302.low w302.t w302.y w302.r w302.cap) (P33.root 5) :=
  Night6836Tree.sound w302 pick302 5 t566 _ (by decide +kernel)
theorem cov302_6 : PA.Covered 6 (OZ.Valid 6 w302.low w302.t w302.y w302.r w302.cap) (P33.root 6) :=
  Night6836Tree.sound w302 pick302 6 t567 _ (by decide +kernel)
theorem cov302_7 : PA.Covered 7 (OZ.Valid 7 w302.low w302.t w302.y w302.r w302.cap) (P33.root 7) :=
  Night6836Tree.sound w302 pick302 7 t2134 _ (by decide +kernel)
theorem window302 : P33.WindowCount w302 := by
  apply P33.window_count w302 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov302_1
  · exact cov302_2
  · exact cov302_3
  · exact cov302_4
  · exact cov302_5
  · exact cov302_6
  · exact cov302_7
def w303 : P33.Window := ⟨15,29,5037,4840,234088366506190360,20964,36000,5000000,81920000000⟩
def h303_0 : Height w303 := ⟨20964,36000,by decide +kernel⟩
def h303_1 : Height w303 := ⟨25317,33000,by decide +kernel⟩
def h303_2 : Height w303 := ⟨30839,30000,by decide +kernel⟩
def h303_3 : Height w303 := ⟨38430,27000,by decide +kernel⟩
def h303_4 : Height w303 := ⟨50224,24000,by decide +kernel⟩
def pick303 (cl : ℕ) : Height w303 := if cl<32 then (if cl<5 then (h303_0) else (h303_1)) else (if cl<145 then (h303_2) else (if cl<922 then (h303_3) else (h303_4)))
private theorem k303_1_0 : check w303 pick303 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k303_1_1 : check w303 pick303 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k303_1_2 : check w303 pick303 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w303 pick303 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k303_1_0 k303_1_1
private theorem k303_1_3 : check w303 pick303 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k303_1_4 : check w303 pick303 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k303_1_5 : check w303 pick303 1 t7219 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w303 pick303 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t7097 k303_1_3 k303_1_4
private theorem k303_1_6 : check w303 pick303 1 t8460 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w303 pick303 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t7219 k303_1_2 k303_1_5
theorem cov303_1 : PA.Covered 1 (OZ.Valid 1 w303.low w303.t w303.y w303.r w303.cap) (P33.root 1) :=
  Night6836Tree.sound w303 pick303 1 t8460 _ k303_1_6
theorem cov303_2 : PA.Covered 2 (OZ.Valid 2 w303.low w303.t w303.y w303.r w303.cap) (P33.root 2) :=
  Night6836Tree.sound w303 pick303 2 t5320 _ (by decide +kernel)
theorem cov303_3 : PA.Covered 3 (OZ.Valid 3 w303.low w303.t w303.y w303.r w303.cap) (P33.root 3) :=
  Night6836Tree.sound w303 pick303 3 t564 _ (by decide +kernel)
theorem cov303_4 : PA.Covered 4 (OZ.Valid 4 w303.low w303.t w303.y w303.r w303.cap) (P33.root 4) :=
  Night6836Tree.sound w303 pick303 4 t565 _ (by decide +kernel)
theorem cov303_5 : PA.Covered 5 (OZ.Valid 5 w303.low w303.t w303.y w303.r w303.cap) (P33.root 5) :=
  Night6836Tree.sound w303 pick303 5 t566 _ (by decide +kernel)
theorem cov303_6 : PA.Covered 6 (OZ.Valid 6 w303.low w303.t w303.y w303.r w303.cap) (P33.root 6) :=
  Night6836Tree.sound w303 pick303 6 t567 _ (by decide +kernel)
theorem cov303_7 : PA.Covered 7 (OZ.Valid 7 w303.low w303.t w303.y w303.r w303.cap) (P33.root 7) :=
  Night6836Tree.sound w303 pick303 7 t2134 _ (by decide +kernel)
theorem window303 : P33.WindowCount w303 := by
  apply P33.window_count w303 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov303_1
  · exact cov303_2
  · exact cov303_3
  · exact cov303_4
  · exact cov303_5
  · exact cov303_6
  · exact cov303_7
def w304 : P33.Window := ⟨15,30,4839,4432,230864791841717235,25292,39000,5000000,81920000000⟩
def h304_0 : Height w304 := ⟨25292,39000,by decide +kernel⟩
def h304_1 : Height w304 := ⟨29821,36000,by decide +kernel⟩
def h304_2 : Height w304 := ⟨35469,33000,by decide +kernel⟩
def h304_3 : Height w304 := ⟨42991,30000,by decide +kernel⟩
def h304_4 : Height w304 := ⟨54019,27000,by decide +kernel⟩
def pick304 (cl : ℕ) : Height w304 := if cl<32 then (if cl<6 then (h304_0) else (h304_1)) else (if cl<136 then (h304_2) else (if cl<922 then (h304_3) else (h304_4)))
private theorem k304_1_0 : check w304 pick304 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k304_1_1 : check w304 pick304 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k304_1_2 : check w304 pick304 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w304 pick304 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k304_1_0 k304_1_1
private theorem k304_1_3 : check w304 pick304 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k304_1_4 : check w304 pick304 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k304_1_5 : check w304 pick304 1 t7219 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w304 pick304 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t7097 k304_1_3 k304_1_4
private theorem k304_1_6 : check w304 pick304 1 t8460 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w304 pick304 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t7219 k304_1_2 k304_1_5
theorem cov304_1 : PA.Covered 1 (OZ.Valid 1 w304.low w304.t w304.y w304.r w304.cap) (P33.root 1) :=
  Night6836Tree.sound w304 pick304 1 t8460 _ k304_1_6
theorem cov304_2 : PA.Covered 2 (OZ.Valid 2 w304.low w304.t w304.y w304.r w304.cap) (P33.root 2) :=
  Night6836Tree.sound w304 pick304 2 t5320 _ (by decide +kernel)
theorem cov304_3 : PA.Covered 3 (OZ.Valid 3 w304.low w304.t w304.y w304.r w304.cap) (P33.root 3) :=
  Night6836Tree.sound w304 pick304 3 t564 _ (by decide +kernel)
theorem cov304_4 : PA.Covered 4 (OZ.Valid 4 w304.low w304.t w304.y w304.r w304.cap) (P33.root 4) :=
  Night6836Tree.sound w304 pick304 4 t565 _ (by decide +kernel)
theorem cov304_5 : PA.Covered 5 (OZ.Valid 5 w304.low w304.t w304.y w304.r w304.cap) (P33.root 5) :=
  Night6836Tree.sound w304 pick304 5 t566 _ (by decide +kernel)
theorem cov304_6 : PA.Covered 6 (OZ.Valid 6 w304.low w304.t w304.y w304.r w304.cap) (P33.root 6) :=
  Night6836Tree.sound w304 pick304 6 t567 _ (by decide +kernel)
theorem cov304_7 : PA.Covered 7 (OZ.Valid 7 w304.low w304.t w304.y w304.r w304.cap) (P33.root 7) :=
  Night6836Tree.sound w304 pick304 7 t2134 _ (by decide +kernel)
theorem window304 : P33.WindowCount w304 := by
  apply P33.window_count w304 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov304_1
  · exact cov304_2
  · exact cov304_3
  · exact cov304_4
  · exact cov304_5
  · exact cov304_6
  · exact cov304_7
def w305 : P33.Window := ⟨15,31,4637,4432,244929354610137911,23366,42000,5000000,81920000000⟩
def h305_0 : Height w305 := ⟨23366,42000,by decide +kernel⟩
def h305_1 : Height w305 := ⟨27277,39000,by decide +kernel⟩
def h305_2 : Height w305 := ⟨31939,36000,by decide +kernel⟩
def h305_3 : Height w305 := ⟨37767,33000,by decide +kernel⟩
def h305_4 : Height w305 := ⟨45550,30000,by decide +kernel⟩
def h305_5 : Height w305 := ⟨56986,27000,by decide +kernel⟩
def pick305 (cl : ℕ) : Height w305 := if cl<36 then (if cl<2 then (h305_0) else (if cl<6 then (h305_1) else (h305_2))) else (if cl<302 then (h305_3) else (if cl<922 then (h305_4) else (h305_5)))
private theorem k305_1_0 : check w305 pick305 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k305_1_1 : check w305 pick305 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k305_1_2 : check w305 pick305 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w305 pick305 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k305_1_0 k305_1_1
private theorem k305_1_3 : check w305 pick305 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k305_1_4 : check w305 pick305 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k305_1_5 : check w305 pick305 1 t7219 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w305 pick305 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t7097 k305_1_3 k305_1_4
private theorem k305_1_6 : check w305 pick305 1 t8460 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w305 pick305 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t7219 k305_1_2 k305_1_5
theorem cov305_1 : PA.Covered 1 (OZ.Valid 1 w305.low w305.t w305.y w305.r w305.cap) (P33.root 1) :=
  Night6836Tree.sound w305 pick305 1 t8460 _ k305_1_6
theorem cov305_2 : PA.Covered 2 (OZ.Valid 2 w305.low w305.t w305.y w305.r w305.cap) (P33.root 2) :=
  Night6836Tree.sound w305 pick305 2 t9063 _ (by decide +kernel)
theorem cov305_3 : PA.Covered 3 (OZ.Valid 3 w305.low w305.t w305.y w305.r w305.cap) (P33.root 3) :=
  Night6836Tree.sound w305 pick305 3 t564 _ (by decide +kernel)
theorem cov305_4 : PA.Covered 4 (OZ.Valid 4 w305.low w305.t w305.y w305.r w305.cap) (P33.root 4) :=
  Night6836Tree.sound w305 pick305 4 t565 _ (by decide +kernel)
theorem cov305_5 : PA.Covered 5 (OZ.Valid 5 w305.low w305.t w305.y w305.r w305.cap) (P33.root 5) :=
  Night6836Tree.sound w305 pick305 5 t566 _ (by decide +kernel)
theorem cov305_6 : PA.Covered 6 (OZ.Valid 6 w305.low w305.t w305.y w305.r w305.cap) (P33.root 6) :=
  Night6836Tree.sound w305 pick305 6 t567 _ (by decide +kernel)
theorem cov305_7 : PA.Covered 7 (OZ.Valid 7 w305.low w305.t w305.y w305.r w305.cap) (P33.root 7) :=
  Night6836Tree.sound w305 pick305 7 t2134 _ (by decide +kernel)
theorem window305 : P33.WindowCount w305 := by
  apply P33.window_count w305 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov305_1
  · exact cov305_2
  · exact cov305_3
  · exact cov305_4
  · exact cov305_5
  · exact cov305_6
  · exact cov305_7
def w306 : P33.Window := ⟨15,32,4431,4220,239423197171048216,29261,42000,5000000,81920000000⟩
def h306_0 : Height w306 := ⟨29261,42000,by decide +kernel⟩
def h306_1 : Height w306 := ⟨33738,39000,by decide +kernel⟩
def h306_2 : Height w306 := ⟨39183,36000,by decide +kernel⟩
def h306_3 : Height w306 := ⟨46161,33000,by decide +kernel⟩
def h306_4 : Height w306 := ⟨55770,30000,by decide +kernel⟩
def pick306 (cl : ℕ) : Height w306 := if cl<32 then (if cl<5 then (h306_0) else (h306_1)) else (if cl<92 then (h306_2) else (if cl<335 then (h306_3) else (h306_4)))
private theorem k306_1_0 : check w306 pick306 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k306_1_1 : check w306 pick306 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k306_1_2 : check w306 pick306 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w306 pick306 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k306_1_0 k306_1_1
private theorem k306_1_3 : check w306 pick306 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k306_1_4 : check w306 pick306 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k306_1_5 : check w306 pick306 1 t7219 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w306 pick306 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t7097 k306_1_3 k306_1_4
private theorem k306_1_6 : check w306 pick306 1 t8460 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w306 pick306 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t7219 k306_1_2 k306_1_5
theorem cov306_1 : PA.Covered 1 (OZ.Valid 1 w306.low w306.t w306.y w306.r w306.cap) (P33.root 1) :=
  Night6836Tree.sound w306 pick306 1 t8460 _ k306_1_6
theorem cov306_2 : PA.Covered 2 (OZ.Valid 2 w306.low w306.t w306.y w306.r w306.cap) (P33.root 2) :=
  Night6836Tree.sound w306 pick306 2 t8952 _ (by decide +kernel)
theorem cov306_3 : PA.Covered 3 (OZ.Valid 3 w306.low w306.t w306.y w306.r w306.cap) (P33.root 3) :=
  Night6836Tree.sound w306 pick306 3 t564 _ (by decide +kernel)
theorem cov306_4 : PA.Covered 4 (OZ.Valid 4 w306.low w306.t w306.y w306.r w306.cap) (P33.root 4) :=
  Night6836Tree.sound w306 pick306 4 t565 _ (by decide +kernel)
theorem cov306_5 : PA.Covered 5 (OZ.Valid 5 w306.low w306.t w306.y w306.r w306.cap) (P33.root 5) :=
  Night6836Tree.sound w306 pick306 5 t566 _ (by decide +kernel)
theorem cov306_6 : PA.Covered 6 (OZ.Valid 6 w306.low w306.t w306.y w306.r w306.cap) (P33.root 6) :=
  Night6836Tree.sound w306 pick306 6 t567 _ (by decide +kernel)
theorem cov306_7 : PA.Covered 7 (OZ.Valid 7 w306.low w306.t w306.y w306.r w306.cap) (P33.root 7) :=
  Night6836Tree.sound w306 pick306 7 t2134 _ (by decide +kernel)
theorem window306 : P33.WindowCount w306 := by
  apply P33.window_count w306 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov306_1
  · exact cov306_2
  · exact cov306_3
  · exact cov306_4
  · exact cov306_5
  · exact cov306_6
  · exact cov306_7
def w307 : P33.Window := ⟨15,33,4219,4005,242565925816083589,31954,45000,5000000,81920000000⟩
def h307_0 : Height w307 := ⟨31954,45000,by decide +kernel⟩
def h307_1 : Height w307 := ⟨36345,42000,by decide +kernel⟩
def h307_2 : Height w307 := ⟨41582,39000,by decide +kernel⟩
def h307_3 : Height w307 := ⟨48099,36000,by decide +kernel⟩
def h307_4 : Height w307 := ⟨56682,33000,by decide +kernel⟩
def pick307 (cl : ℕ) : Height w307 := if cl<32 then (if cl<5 then (h307_0) else (h307_1)) else (if cl<62 then (h307_2) else (if cl<302 then (h307_3) else (h307_4)))
private theorem k307_1_0 : check w307 pick307 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k307_1_1 : check w307 pick307 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k307_1_2 : check w307 pick307 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w307 pick307 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k307_1_0 k307_1_1
private theorem k307_1_3 : check w307 pick307 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k307_1_4 : check w307 pick307 1 t8752 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k307_1_5 : check w307 pick307 1 t8753 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w307 pick307 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t8752 k307_1_3 k307_1_4
private theorem k307_1_6 : check w307 pick307 1 t9064 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w307 pick307 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t8753 k307_1_2 k307_1_5
theorem cov307_1 : PA.Covered 1 (OZ.Valid 1 w307.low w307.t w307.y w307.r w307.cap) (P33.root 1) :=
  Night6836Tree.sound w307 pick307 1 t9064 _ k307_1_6
theorem cov307_2 : PA.Covered 2 (OZ.Valid 2 w307.low w307.t w307.y w307.r w307.cap) (P33.root 2) :=
  Night6836Tree.sound w307 pick307 2 t6109 _ (by decide +kernel)
theorem cov307_3 : PA.Covered 3 (OZ.Valid 3 w307.low w307.t w307.y w307.r w307.cap) (P33.root 3) :=
  Night6836Tree.sound w307 pick307 3 t564 _ (by decide +kernel)
theorem cov307_4 : PA.Covered 4 (OZ.Valid 4 w307.low w307.t w307.y w307.r w307.cap) (P33.root 4) :=
  Night6836Tree.sound w307 pick307 4 t565 _ (by decide +kernel)
theorem cov307_5 : PA.Covered 5 (OZ.Valid 5 w307.low w307.t w307.y w307.r w307.cap) (P33.root 5) :=
  Night6836Tree.sound w307 pick307 5 t566 _ (by decide +kernel)
theorem cov307_6 : PA.Covered 6 (OZ.Valid 6 w307.low w307.t w307.y w307.r w307.cap) (P33.root 6) :=
  Night6836Tree.sound w307 pick307 6 t567 _ (by decide +kernel)
theorem cov307_7 : PA.Covered 7 (OZ.Valid 7 w307.low w307.t w307.y w307.r w307.cap) (P33.root 7) :=
  Night6836Tree.sound w307 pick307 7 t2134 _ (by decide +kernel)
theorem window307 : P33.WindowCount w307 := by
  apply P33.window_count w307 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov307_1
  · exact cov307_2
  · exact cov307_3
  · exact cov307_4
  · exact cov307_5
  · exact cov307_6
  · exact cov307_7
def w308 : P33.Window := ⟨15,34,4004,3784,241718004639635876,35556,48000,5000000,81920000000⟩
def h308_0 : Height w308 := ⟨35556,48000,by decide +kernel⟩
def h308_1 : Height w308 := ⟨39954,45000,by decide +kernel⟩
def h308_2 : Height w308 := ⟨45126,42000,by decide +kernel⟩
def h308_3 : Height w308 := ⟨51429,39000,by decide +kernel⟩
def h308_4 : Height w308 := ⟨59478,36000,by decide +kernel⟩
def pick308 (cl : ℕ) : Height w308 := if cl<18 then (if cl<5 then (h308_0) else (h308_1)) else (if cl<49 then (h308_2) else (if cl<312 then (h308_3) else (h308_4)))
private theorem k308_1_0 : check w308 pick308 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k308_1_1 : check w308 pick308 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k308_1_2 : check w308 pick308 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w308 pick308 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k308_1_0 k308_1_1
private theorem k308_1_3 : check w308 pick308 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k308_1_4 : check w308 pick308 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k308_1_5 : check w308 pick308 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w308 pick308 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k308_1_3 k308_1_4
private theorem k308_1_6 : check w308 pick308 1 t9065 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w308 pick308 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t8758 k308_1_2 k308_1_5
theorem cov308_1 : PA.Covered 1 (OZ.Valid 1 w308.low w308.t w308.y w308.r w308.cap) (P33.root 1) :=
  Night6836Tree.sound w308 pick308 1 t9065 _ k308_1_6
theorem cov308_2 : PA.Covered 2 (OZ.Valid 2 w308.low w308.t w308.y w308.r w308.cap) (P33.root 2) :=
  Night6836Tree.sound w308 pick308 2 t6109 _ (by decide +kernel)
theorem cov308_3 : PA.Covered 3 (OZ.Valid 3 w308.low w308.t w308.y w308.r w308.cap) (P33.root 3) :=
  Night6836Tree.sound w308 pick308 3 t564 _ (by decide +kernel)
theorem cov308_4 : PA.Covered 4 (OZ.Valid 4 w308.low w308.t w308.y w308.r w308.cap) (P33.root 4) :=
  Night6836Tree.sound w308 pick308 4 t565 _ (by decide +kernel)
theorem cov308_5 : PA.Covered 5 (OZ.Valid 5 w308.low w308.t w308.y w308.r w308.cap) (P33.root 5) :=
  Night6836Tree.sound w308 pick308 5 t566 _ (by decide +kernel)
theorem cov308_6 : PA.Covered 6 (OZ.Valid 6 w308.low w308.t w308.y w308.r w308.cap) (P33.root 6) :=
  Night6836Tree.sound w308 pick308 6 t567 _ (by decide +kernel)
theorem cov308_7 : PA.Covered 7 (OZ.Valid 7 w308.low w308.t w308.y w308.r w308.cap) (P33.root 7) :=
  Night6836Tree.sound w308 pick308 7 t2134 _ (by decide +kernel)
theorem window308 : P33.WindowCount w308 := by
  apply P33.window_count w308 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov308_1
  · exact cov308_2
  · exact cov308_3
  · exact cov308_4
  · exact cov308_5
  · exact cov308_6
  · exact cov308_7
def w309 : P33.Window := ⟨15,35,3783,3559,233254532918467680,36277,54000,5000000,81920000000⟩
def h309_0 : Height w309 := ⟨36277,54000,by decide +kernel⟩
def h309_1 : Height w309 := ⟨40226,51000,by decide +kernel⟩
def h309_2 : Height w309 := ⟨44715,48000,by decide +kernel⟩
def h309_3 : Height w309 := ⟨49943,45000,by decide +kernel⟩
def h309_4 : Height w309 := ⟨56222,42000,by decide +kernel⟩
def h309_5 : Height w309 := ⟨64069,39000,by decide +kernel⟩
def h309_6 : Height w309 := ⟨74398,36000,by decide +kernel⟩
def pick309 (cl : ℕ) : Height w309 := if cl<32 then (if cl<2 then (h309_0) else (if cl<5 then (h309_1) else (h309_2))) else (if cl<312 then (if cl<46 then (h309_3) else (h309_4)) else (if cl<644 then (h309_5) else (h309_6)))
private theorem k309_1_0 : check w309 pick309 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k309_1_1 : check w309 pick309 1 t7326 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k309_1_2 : check w309 pick309 1 t7327 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w309 pick309 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7326 k309_1_0 k309_1_1
private theorem k309_1_3 : check w309 pick309 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k309_1_4 : check w309 pick309 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k309_1_5 : check w309 pick309 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w309 pick309 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k309_1_3 k309_1_4
private theorem k309_1_6 : check w309 pick309 1 t9066 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w309 pick309 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7327 t8758 k309_1_2 k309_1_5
theorem cov309_1 : PA.Covered 1 (OZ.Valid 1 w309.low w309.t w309.y w309.r w309.cap) (P33.root 1) :=
  Night6836Tree.sound w309 pick309 1 t9066 _ k309_1_6
theorem cov309_2 : PA.Covered 2 (OZ.Valid 2 w309.low w309.t w309.y w309.r w309.cap) (P33.root 2) :=
  Night6836Tree.sound w309 pick309 2 t6109 _ (by decide +kernel)
theorem cov309_3 : PA.Covered 3 (OZ.Valid 3 w309.low w309.t w309.y w309.r w309.cap) (P33.root 3) :=
  Night6836Tree.sound w309 pick309 3 t564 _ (by decide +kernel)
theorem cov309_4 : PA.Covered 4 (OZ.Valid 4 w309.low w309.t w309.y w309.r w309.cap) (P33.root 4) :=
  Night6836Tree.sound w309 pick309 4 t565 _ (by decide +kernel)
theorem cov309_5 : PA.Covered 5 (OZ.Valid 5 w309.low w309.t w309.y w309.r w309.cap) (P33.root 5) :=
  Night6836Tree.sound w309 pick309 5 t566 _ (by decide +kernel)
theorem cov309_6 : PA.Covered 6 (OZ.Valid 6 w309.low w309.t w309.y w309.r w309.cap) (P33.root 6) :=
  Night6836Tree.sound w309 pick309 6 t567 _ (by decide +kernel)
theorem cov309_7 : PA.Covered 7 (OZ.Valid 7 w309.low w309.t w309.y w309.r w309.cap) (P33.root 7) :=
  Night6836Tree.sound w309 pick309 7 t2134 _ (by decide +kernel)
theorem window309 : P33.WindowCount w309 := by
  apply P33.window_count w309 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov309_1
  · exact cov309_2
  · exact cov309_3
  · exact cov309_4
  · exact cov309_5
  · exact cov309_6
  · exact cov309_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w310 : P33.Window := ⟨15,36,3558,3329,224063062056897880,42167,57000,5000000,81920000000⟩
def h310_0 : Height w310 := ⟨42167,57000,by decide +kernel⟩
def h310_1 : Height w310 := ⟨46297,54000,by decide +kernel⟩
def h310_2 : Height w310 := ⟨50973,51000,by decide +kernel⟩
def h310_3 : Height w310 := ⟨56387,48000,by decide +kernel⟩
def h310_4 : Height w310 := ⟨62828,45000,by decide +kernel⟩
def h310_5 : Height w310 := ⟨70757,42000,by decide +kernel⟩
def h310_6 : Height w310 := ⟨80961,39000,by decide +kernel⟩
def pick310 (cl : ℕ) : Height w310 := if cl<32 then (if cl<3 then (h310_0) else (if cl<10 then (h310_1) else (h310_2))) else (if cl<312 then (if cl<55 then (h310_3) else (h310_4)) else (if cl<594 then (h310_5) else (h310_6)))
private theorem k310_1_0 : check w310 pick310 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k310_1_1 : check w310 pick310 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k310_1_2 : check w310 pick310 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w310 pick310 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k310_1_0 k310_1_1
private theorem k310_1_3 : check w310 pick310 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k310_1_4 : check w310 pick310 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k310_1_5 : check w310 pick310 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w310 pick310 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k310_1_3 k310_1_4
private theorem k310_1_6 : check w310 pick310 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w310 pick310 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k310_1_2 k310_1_5
theorem cov310_1 : PA.Covered 1 (OZ.Valid 1 w310.low w310.t w310.y w310.r w310.cap) (P33.root 1) :=
  Night6836Tree.sound w310 pick310 1 t8759 _ k310_1_6
theorem cov310_2 : PA.Covered 2 (OZ.Valid 2 w310.low w310.t w310.y w310.r w310.cap) (P33.root 2) :=
  Night6836Tree.sound w310 pick310 2 t6560 _ (by decide +kernel)
theorem cov310_3 : PA.Covered 3 (OZ.Valid 3 w310.low w310.t w310.y w310.r w310.cap) (P33.root 3) :=
  Night6836Tree.sound w310 pick310 3 t564 _ (by decide +kernel)
theorem cov310_4 : PA.Covered 4 (OZ.Valid 4 w310.low w310.t w310.y w310.r w310.cap) (P33.root 4) :=
  Night6836Tree.sound w310 pick310 4 t565 _ (by decide +kernel)
theorem cov310_5 : PA.Covered 5 (OZ.Valid 5 w310.low w310.t w310.y w310.r w310.cap) (P33.root 5) :=
  Night6836Tree.sound w310 pick310 5 t566 _ (by decide +kernel)
theorem cov310_6 : PA.Covered 6 (OZ.Valid 6 w310.low w310.t w310.y w310.r w310.cap) (P33.root 6) :=
  Night6836Tree.sound w310 pick310 6 t567 _ (by decide +kernel)
theorem cov310_7 : PA.Covered 7 (OZ.Valid 7 w310.low w310.t w310.y w310.r w310.cap) (P33.root 7) :=
  Night6836Tree.sound w310 pick310 7 t2134 _ (by decide +kernel)
theorem window310 : P33.WindowCount w310 := by
  apply P33.window_count w310 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov310_1
  · exact cov310_2
  · exact cov310_3
  · exact cov310_4
  · exact cov310_5
  · exact cov310_6
  · exact cov310_7
def w311 : P33.Window := ⟨15,37,3328,3093,219588213048766967,45897,63000,5000000,81920000000⟩
def h311_0 : Height w311 := ⟨45897,63000,by decide +kernel⟩
def h311_1 : Height w311 := ⟨49865,60000,by decide +kernel⟩
def h311_2 : Height w311 := ⟨54278,57000,by decide +kernel⟩
def h311_3 : Height w311 := ⟨59270,54000,by decide +kernel⟩
def h311_4 : Height w311 := ⟨65031,51000,by decide +kernel⟩
def h311_5 : Height w311 := ⟨71847,48000,by decide +kernel⟩
def h311_6 : Height w311 := ⟨80162,45000,by decide +kernel⟩
def pick311 (cl : ℕ) : Height w311 := if cl<14 then (if cl<2 then (h311_0) else (if cl<5 then (h311_1) else (h311_2))) else (if cl<83 then (if cl<32 then (h311_3) else (h311_4)) else (if cl<312 then (h311_5) else (h311_6)))
private theorem k311_1_0 : check w311 pick311 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k311_1_1 : check w311 pick311 1 t9068 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k311_1_2 : check w311 pick311 1 t9069 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w311 pick311 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t9068 k311_1_0 k311_1_1
private theorem k311_1_3 : check w311 pick311 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k311_1_4 : check w311 pick311 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k311_1_5 : check w311 pick311 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w311 pick311 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k311_1_3 k311_1_4
private theorem k311_1_6 : check w311 pick311 1 t9070 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w311 pick311 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9069 t8758 k311_1_2 k311_1_5
theorem cov311_1 : PA.Covered 1 (OZ.Valid 1 w311.low w311.t w311.y w311.r w311.cap) (P33.root 1) :=
  Night6836Tree.sound w311 pick311 1 t9070 _ k311_1_6
theorem cov311_2 : PA.Covered 2 (OZ.Valid 2 w311.low w311.t w311.y w311.r w311.cap) (P33.root 2) :=
  Night6836Tree.sound w311 pick311 2 t6560 _ (by decide +kernel)
theorem cov311_3 : PA.Covered 3 (OZ.Valid 3 w311.low w311.t w311.y w311.r w311.cap) (P33.root 3) :=
  Night6836Tree.sound w311 pick311 3 t564 _ (by decide +kernel)
theorem cov311_4 : PA.Covered 4 (OZ.Valid 4 w311.low w311.t w311.y w311.r w311.cap) (P33.root 4) :=
  Night6836Tree.sound w311 pick311 4 t565 _ (by decide +kernel)
theorem cov311_5 : PA.Covered 5 (OZ.Valid 5 w311.low w311.t w311.y w311.r w311.cap) (P33.root 5) :=
  Night6836Tree.sound w311 pick311 5 t566 _ (by decide +kernel)
theorem cov311_6 : PA.Covered 6 (OZ.Valid 6 w311.low w311.t w311.y w311.r w311.cap) (P33.root 6) :=
  Night6836Tree.sound w311 pick311 6 t567 _ (by decide +kernel)
theorem cov311_7 : PA.Covered 7 (OZ.Valid 7 w311.low w311.t w311.y w311.r w311.cap) (P33.root 7) :=
  Night6836Tree.sound w311 pick311 7 t2134 _ (by decide +kernel)
theorem window311 : P33.WindowCount w311 := by
  apply P33.window_count w311 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov311_1
  · exact cov311_2
  · exact cov311_3
  · exact cov311_4
  · exact cov311_5
  · exact cov311_6
  · exact cov311_7
def w312 : P33.Window := ⟨15,38,3092,2852,220562398200452887,51736,69000,5000000,81920000000⟩
def h312_0 : Height w312 := ⟨51736,69000,by decide +kernel⟩
def h312_1 : Height w312 := ⟨55684,66000,by decide +kernel⟩
def h312_2 : Height w312 := ⟨60026,63000,by decide +kernel⟩
def h312_3 : Height w312 := ⟨64866,60000,by decide +kernel⟩
def h312_4 : Height w312 := ⟨70347,57000,by decide +kernel⟩
def h312_5 : Height w312 := ⟨76673,54000,by decide +kernel⟩
def h312_6 : Height w312 := ⟨84141,51000,by decide +kernel⟩
def h312_7 : Height w312 := ⟨93211,48000,by decide +kernel⟩
def pick312 (cl : ℕ) : Height w312 := if cl<32 then (if cl<5 then (if cl<2 then (h312_0) else (h312_1)) else (if cl<12 then (h312_2) else (h312_3))) else (if cl<132 then (if cl<49 then (h312_4) else (h312_5)) else (if cl<312 then (h312_6) else (h312_7)))
private theorem k312_1_0 : check w312 pick312 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k312_1_1 : check w312 pick312 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k312_1_2 : check w312 pick312 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w312 pick312 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k312_1_0 k312_1_1
private theorem k312_1_3 : check w312 pick312 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k312_1_4 : check w312 pick312 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k312_1_5 : check w312 pick312 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w312 pick312 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k312_1_3 k312_1_4
private theorem k312_1_6 : check w312 pick312 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w312 pick312 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k312_1_2 k312_1_5
theorem cov312_1 : PA.Covered 1 (OZ.Valid 1 w312.low w312.t w312.y w312.r w312.cap) (P33.root 1) :=
  Night6836Tree.sound w312 pick312 1 t8759 _ k312_1_6
theorem cov312_2 : PA.Covered 2 (OZ.Valid 2 w312.low w312.t w312.y w312.r w312.cap) (P33.root 2) :=
  Night6836Tree.sound w312 pick312 2 t6560 _ (by decide +kernel)
theorem cov312_3 : PA.Covered 3 (OZ.Valid 3 w312.low w312.t w312.y w312.r w312.cap) (P33.root 3) :=
  Night6836Tree.sound w312 pick312 3 t564 _ (by decide +kernel)
theorem cov312_4 : PA.Covered 4 (OZ.Valid 4 w312.low w312.t w312.y w312.r w312.cap) (P33.root 4) :=
  Night6836Tree.sound w312 pick312 4 t565 _ (by decide +kernel)
theorem cov312_5 : PA.Covered 5 (OZ.Valid 5 w312.low w312.t w312.y w312.r w312.cap) (P33.root 5) :=
  Night6836Tree.sound w312 pick312 5 t566 _ (by decide +kernel)
theorem cov312_6 : PA.Covered 6 (OZ.Valid 6 w312.low w312.t w312.y w312.r w312.cap) (P33.root 6) :=
  Night6836Tree.sound w312 pick312 6 t567 _ (by decide +kernel)
theorem cov312_7 : PA.Covered 7 (OZ.Valid 7 w312.low w312.t w312.y w312.r w312.cap) (P33.root 7) :=
  Night6836Tree.sound w312 pick312 7 t2134 _ (by decide +kernel)
theorem window312 : P33.WindowCount w312 := by
  apply P33.window_count w312 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov312_1
  · exact cov312_2
  · exact cov312_3
  · exact cov312_4
  · exact cov312_5
  · exact cov312_6
  · exact cov312_7
def w313 : P33.Window := ⟨15,39,2851,2606,213979466442119573,60344,75000,5000000,81920000000⟩
def h313_0 : Height w313 := ⟨60344,75000,by decide +kernel⟩
def h313_1 : Height w313 := ⟨64406,72000,by decide +kernel⟩
def h313_2 : Height w313 := ⟨68845,69000,by decide +kernel⟩
def h313_3 : Height w313 := ⟨73749,66000,by decide +kernel⟩
def h313_4 : Height w313 := ⟨79239,63000,by decide +kernel⟩
def h313_5 : Height w313 := ⟨85478,60000,by decide +kernel⟩
def h313_6 : Height w313 := ⟨92697,57000,by decide +kernel⟩
def h313_7 : Height w313 := ⟨101236,54000,by decide +kernel⟩
def h313_8 : Height w313 := ⟨111604,51000,by decide +kernel⟩
def pick313 (cl : ℕ) : Height w313 := if cl<32 then (if cl<5 then (if cl<2 then (h313_0) else (h313_1)) else (if cl<12 then (h313_2) else (h313_3))) else (if cl<105 then (if cl<46 then (h313_4) else (h313_5)) else (if cl<312 then (h313_6) else (if cl<644 then (h313_7) else (h313_8))))
private theorem k313_1_0 : check w313 pick313 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k313_1_1 : check w313 pick313 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k313_1_2 : check w313 pick313 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w313 pick313 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k313_1_0 k313_1_1
private theorem k313_1_3 : check w313 pick313 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k313_1_4 : check w313 pick313 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k313_1_5 : check w313 pick313 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w313 pick313 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k313_1_3 k313_1_4
private theorem k313_1_6 : check w313 pick313 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w313 pick313 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k313_1_2 k313_1_5
theorem cov313_1 : PA.Covered 1 (OZ.Valid 1 w313.low w313.t w313.y w313.r w313.cap) (P33.root 1) :=
  Night6836Tree.sound w313 pick313 1 t8759 _ k313_1_6
theorem cov313_2 : PA.Covered 2 (OZ.Valid 2 w313.low w313.t w313.y w313.r w313.cap) (P33.root 2) :=
  Night6836Tree.sound w313 pick313 2 t6560 _ (by decide +kernel)
theorem cov313_3 : PA.Covered 3 (OZ.Valid 3 w313.low w313.t w313.y w313.r w313.cap) (P33.root 3) :=
  Night6836Tree.sound w313 pick313 3 t564 _ (by decide +kernel)
theorem cov313_4 : PA.Covered 4 (OZ.Valid 4 w313.low w313.t w313.y w313.r w313.cap) (P33.root 4) :=
  Night6836Tree.sound w313 pick313 4 t565 _ (by decide +kernel)
theorem cov313_5 : PA.Covered 5 (OZ.Valid 5 w313.low w313.t w313.y w313.r w313.cap) (P33.root 5) :=
  Night6836Tree.sound w313 pick313 5 t566 _ (by decide +kernel)
theorem cov313_6 : PA.Covered 6 (OZ.Valid 6 w313.low w313.t w313.y w313.r w313.cap) (P33.root 6) :=
  Night6836Tree.sound w313 pick313 6 t567 _ (by decide +kernel)
theorem cov313_7 : PA.Covered 7 (OZ.Valid 7 w313.low w313.t w313.y w313.r w313.cap) (P33.root 7) :=
  Night6836Tree.sound w313 pick313 7 t2134 _ (by decide +kernel)
theorem window313 : P33.WindowCount w313 := by
  apply P33.window_count w313 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov313_1
  · exact cov313_2
  · exact cov313_3
  · exact cov313_4
  · exact cov313_5
  · exact cov313_6
  · exact cov313_7
def w314 : P33.Window := ⟨15,40,2605,2353,205716296242581898,69000,84000,5000000,81920000000⟩
def h314_0 : Height w314 := ⟨69000,84000,by decide +kernel⟩
def h314_1 : Height w314 := ⟨73024,81000,by decide +kernel⟩
def h314_2 : Height w314 := ⟨77371,78000,by decide +kernel⟩
def h314_3 : Height w314 := ⟨82106,75000,by decide +kernel⟩
def h314_4 : Height w314 := ⟨93109,69000,by decide +kernel⟩
def h314_5 : Height w314 := ⟨99638,66000,by decide +kernel⟩
def h314_6 : Height w314 := ⟨107108,63000,by decide +kernel⟩
def h314_7 : Height w314 := ⟨115806,60000,by decide +kernel⟩
def h314_8 : Height w314 := ⟨126152,57000,by decide +kernel⟩
def pick314 (cl : ℕ) : Height w314 := if cl<32 then (if cl<5 then (if cl<2 then (h314_0) else (h314_1)) else (if cl<10 then (h314_2) else (h314_3))) else (if cl<132 then (if cl<62 then (h314_4) else (h314_5)) else (if cl<312 then (h314_6) else (if cl<644 then (h314_7) else (h314_8))))
private theorem k314_1_0 : check w314 pick314 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k314_1_1 : check w314 pick314 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k314_1_2 : check w314 pick314 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w314 pick314 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k314_1_0 k314_1_1
private theorem k314_1_3 : check w314 pick314 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k314_1_4 : check w314 pick314 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k314_1_5 : check w314 pick314 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w314 pick314 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k314_1_3 k314_1_4
private theorem k314_1_6 : check w314 pick314 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w314 pick314 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k314_1_2 k314_1_5
theorem cov314_1 : PA.Covered 1 (OZ.Valid 1 w314.low w314.t w314.y w314.r w314.cap) (P33.root 1) :=
  Night6836Tree.sound w314 pick314 1 t8759 _ k314_1_6
theorem cov314_2 : PA.Covered 2 (OZ.Valid 2 w314.low w314.t w314.y w314.r w314.cap) (P33.root 2) :=
  Night6836Tree.sound w314 pick314 2 t6560 _ (by decide +kernel)
theorem cov314_3 : PA.Covered 3 (OZ.Valid 3 w314.low w314.t w314.y w314.r w314.cap) (P33.root 3) :=
  Night6836Tree.sound w314 pick314 3 t564 _ (by decide +kernel)
theorem cov314_4 : PA.Covered 4 (OZ.Valid 4 w314.low w314.t w314.y w314.r w314.cap) (P33.root 4) :=
  Night6836Tree.sound w314 pick314 4 t565 _ (by decide +kernel)
theorem cov314_5 : PA.Covered 5 (OZ.Valid 5 w314.low w314.t w314.y w314.r w314.cap) (P33.root 5) :=
  Night6836Tree.sound w314 pick314 5 t566 _ (by decide +kernel)
theorem cov314_6 : PA.Covered 6 (OZ.Valid 6 w314.low w314.t w314.y w314.r w314.cap) (P33.root 6) :=
  Night6836Tree.sound w314 pick314 6 t567 _ (by decide +kernel)
theorem cov314_7 : PA.Covered 7 (OZ.Valid 7 w314.low w314.t w314.y w314.r w314.cap) (P33.root 7) :=
  Night6836Tree.sound w314 pick314 7 t2134 _ (by decide +kernel)
theorem window314 : P33.WindowCount w314 := by
  apply P33.window_count w314 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov314_1
  · exact cov314_2
  · exact cov314_3
  · exact cov314_4
  · exact cov314_5
  · exact cov314_6
  · exact cov314_7
def w315 : P33.Window := ⟨15,41,2352,2095,196644552243891726,79126,96000,5000000,81920000000⟩
def h315_0 : Height w315 := ⟨79126,96000,by decide +kernel⟩
def h315_1 : Height w315 := ⟨83060,93000,by decide +kernel⟩
def h315_2 : Height w315 := ⟨87259,90000,by decide +kernel⟩
def h315_3 : Height w315 := ⟨91767,87000,by decide +kernel⟩
def h315_4 : Height w315 := ⟨96641,84000,by decide +kernel⟩
def h315_5 : Height w315 := ⟨101953,81000,by decide +kernel⟩
def h315_6 : Height w315 := ⟨107792,78000,by decide +kernel⟩
def h315_7 : Height w315 := ⟨114276,75000,by decide +kernel⟩
def h315_8 : Height w315 := ⟨121558,72000,by decide +kernel⟩
def h315_9 : Height w315 := ⟨129846,69000,by decide +kernel⟩
def h315_10 : Height w315 := ⟨139424,66000,by decide +kernel⟩
def pick315 (cl : ℕ) : Height w315 := if cl<32 then (if cl<4 then (if cl<2 then (h315_0) else (h315_1)) else (if cl<6 then (h315_2) else (if cl<12 then (h315_3) else (h315_4)))) else (if cl<107 then (if cl<36 then (h315_5) else (if cl<62 then (h315_6) else (h315_7))) else (if cl<312 then (h315_8) else (if cl<331 then (h315_9) else (h315_10))))
private theorem k315_1_0 : check w315 pick315 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k315_1_1 : check w315 pick315 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k315_1_2 : check w315 pick315 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w315 pick315 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k315_1_0 k315_1_1
private theorem k315_1_3 : check w315 pick315 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k315_1_4 : check w315 pick315 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k315_1_5 : check w315 pick315 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w315 pick315 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k315_1_3 k315_1_4
private theorem k315_1_6 : check w315 pick315 1 t8759 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w315 pick315 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8758 k315_1_2 k315_1_5
theorem cov315_1 : PA.Covered 1 (OZ.Valid 1 w315.low w315.t w315.y w315.r w315.cap) (P33.root 1) :=
  Night6836Tree.sound w315 pick315 1 t8759 _ k315_1_6
theorem cov315_2 : PA.Covered 2 (OZ.Valid 2 w315.low w315.t w315.y w315.r w315.cap) (P33.root 2) :=
  Night6836Tree.sound w315 pick315 2 t6618 _ (by decide +kernel)
theorem cov315_3 : PA.Covered 3 (OZ.Valid 3 w315.low w315.t w315.y w315.r w315.cap) (P33.root 3) :=
  Night6836Tree.sound w315 pick315 3 t564 _ (by decide +kernel)
theorem cov315_4 : PA.Covered 4 (OZ.Valid 4 w315.low w315.t w315.y w315.r w315.cap) (P33.root 4) :=
  Night6836Tree.sound w315 pick315 4 t565 _ (by decide +kernel)
theorem cov315_5 : PA.Covered 5 (OZ.Valid 5 w315.low w315.t w315.y w315.r w315.cap) (P33.root 5) :=
  Night6836Tree.sound w315 pick315 5 t566 _ (by decide +kernel)
theorem cov315_6 : PA.Covered 6 (OZ.Valid 6 w315.low w315.t w315.y w315.r w315.cap) (P33.root 6) :=
  Night6836Tree.sound w315 pick315 6 t567 _ (by decide +kernel)
theorem cov315_7 : PA.Covered 7 (OZ.Valid 7 w315.low w315.t w315.y w315.r w315.cap) (P33.root 7) :=
  Night6836Tree.sound w315 pick315 7 t2134 _ (by decide +kernel)
theorem window315 : P33.WindowCount w315 := by
  apply P33.window_count w315 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov315_1
  · exact cov315_2
  · exact cov315_3
  · exact cov315_4
  · exact cov315_5
  · exact cov315_6
  · exact cov315_7
def w316 : P33.Window := ⟨15,42,2094,1924,228782668922593479,89622,105000,5000000,81920000000⟩
def h316_0 : Height w316 := ⟨89622,105000,by decide +kernel⟩
def h316_1 : Height w316 := ⟨93575,102000,by decide +kernel⟩
def h316_2 : Height w316 := ⟨97768,99000,by decide +kernel⟩
def h316_3 : Height w316 := ⟨102238,96000,by decide +kernel⟩
def h316_4 : Height w316 := ⟨107030,93000,by decide +kernel⟩
def h316_5 : Height w316 := ⟨112199,90000,by decide +kernel⟩
def h316_6 : Height w316 := ⟨117814,87000,by decide +kernel⟩
def h316_7 : Height w316 := ⟨123960,84000,by decide +kernel⟩
def h316_8 : Height w316 := ⟨130748,81000,by decide +kernel⟩
def h316_9 : Height w316 := ⟨138317,78000,by decide +kernel⟩
def h316_10 : Height w316 := ⟨146855,75000,by decide +kernel⟩
def h316_11 : Height w316 := ⟨156609,72000,by decide +kernel⟩
def pick316 (cl : ℕ) : Height w316 := if cl<32 then (if cl<5 then (if cl<2 then (h316_0) else (if cl<4 then (h316_1) else (h316_2))) else (if cl<10 then (h316_3) else (if cl<18 then (h316_4) else (h316_5)))) else (if cl<145 then (if cl<43 then (h316_6) else (if cl<83 then (h316_7) else (h316_8))) else (if cl<312 then (h316_9) else (if cl<388 then (h316_10) else (h316_11))))
private theorem k316_1_0 : check w316 pick316 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k316_1_1 : check w316 pick316 1 t8748 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k316_1_2 : check w316 pick316 1 t8749 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w316 pick316 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t8748 k316_1_0 k316_1_1
private theorem k316_1_3 : check w316 pick316 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k316_1_4 : check w316 pick316 1 t8767 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k316_1_5 : check w316 pick316 1 t8768 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w316 pick316 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8767 k316_1_3 k316_1_4
private theorem k316_1_6 : check w316 pick316 1 t8958 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w316 pick316 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8749 t8768 k316_1_2 k316_1_5
theorem cov316_1 : PA.Covered 1 (OZ.Valid 1 w316.low w316.t w316.y w316.r w316.cap) (P33.root 1) :=
  Night6836Tree.sound w316 pick316 1 t8958 _ k316_1_6
theorem cov316_2 : PA.Covered 2 (OZ.Valid 2 w316.low w316.t w316.y w316.r w316.cap) (P33.root 2) :=
  Night6836Tree.sound w316 pick316 2 t6618 _ (by decide +kernel)
theorem cov316_3 : PA.Covered 3 (OZ.Valid 3 w316.low w316.t w316.y w316.r w316.cap) (P33.root 3) :=
  Night6836Tree.sound w316 pick316 3 t564 _ (by decide +kernel)
theorem cov316_4 : PA.Covered 4 (OZ.Valid 4 w316.low w316.t w316.y w316.r w316.cap) (P33.root 4) :=
  Night6836Tree.sound w316 pick316 4 t565 _ (by decide +kernel)
theorem cov316_5 : PA.Covered 5 (OZ.Valid 5 w316.low w316.t w316.y w316.r w316.cap) (P33.root 5) :=
  Night6836Tree.sound w316 pick316 5 t566 _ (by decide +kernel)
theorem cov316_6 : PA.Covered 6 (OZ.Valid 6 w316.low w316.t w316.y w316.r w316.cap) (P33.root 6) :=
  Night6836Tree.sound w316 pick316 6 t567 _ (by decide +kernel)
theorem cov316_7 : PA.Covered 7 (OZ.Valid 7 w316.low w316.t w316.y w316.r w316.cap) (P33.root 7) :=
  Night6836Tree.sound w316 pick316 7 t2134 _ (by decide +kernel)
theorem window316 : P33.WindowCount w316 := by
  apply P33.window_count w316 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov316_1
  · exact cov316_2
  · exact cov316_3
  · exact cov316_4
  · exact cov316_5
  · exact cov316_6
  · exact cov316_7
def w317 : P33.Window := ⟨16,21,4955,4778,230403381059484109,11104,33000,5000000,81920000000⟩
def h317_0 : Height w317 := ⟨11104,33000,by decide +kernel⟩
def h317_1 : Height w317 := ⟨15756,30000,by decide +kernel⟩
def h317_2 : Height w317 := ⟨22232,27000,by decide +kernel⟩
def h317_3 : Height w317 := ⟨32747,24000,by decide +kernel⟩
def pick317 (cl : ℕ) : Height w317 := if cl<55 then (if cl<6 then (h317_0) else (h317_1)) else (if cl<685 then (h317_2) else (h317_3))
private theorem k317_1_0 : check w317 pick317 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k317_1_1 : check w317 pick317 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k317_1_2 : check w317 pick317 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w317 pick317 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k317_1_0 k317_1_1
private theorem k317_1_3 : check w317 pick317 1 t9073 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k317_1_4 : check w317 pick317 1 t7452 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k317_1_5 : check w317 pick317 1 t9074 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w317 pick317 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9073 t7452 k317_1_3 k317_1_4
private theorem k317_1_6 : check w317 pick317 1 t9075 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w317 pick317 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t9074 k317_1_2 k317_1_5
theorem cov317_1 : PA.Covered 1 (OZ.Valid 1 w317.low w317.t w317.y w317.r w317.cap) (P33.root 1) :=
  Night6836Tree.sound w317 pick317 1 t9075 _ k317_1_6
theorem cov317_2 : PA.Covered 2 (OZ.Valid 2 w317.low w317.t w317.y w317.r w317.cap) (P33.root 2) :=
  Night6836Tree.sound w317 pick317 2 t6109 _ (by decide +kernel)
theorem cov317_3 : PA.Covered 3 (OZ.Valid 3 w317.low w317.t w317.y w317.r w317.cap) (P33.root 3) :=
  Night6836Tree.sound w317 pick317 3 t564 _ (by decide +kernel)
theorem cov317_4 : PA.Covered 4 (OZ.Valid 4 w317.low w317.t w317.y w317.r w317.cap) (P33.root 4) :=
  Night6836Tree.sound w317 pick317 4 t565 _ (by decide +kernel)
theorem cov317_5 : PA.Covered 5 (OZ.Valid 5 w317.low w317.t w317.y w317.r w317.cap) (P33.root 5) :=
  Night6836Tree.sound w317 pick317 5 t566 _ (by decide +kernel)
theorem cov317_6 : PA.Covered 6 (OZ.Valid 6 w317.low w317.t w317.y w317.r w317.cap) (P33.root 6) :=
  Night6836Tree.sound w317 pick317 6 t567 _ (by decide +kernel)
theorem cov317_7 : PA.Covered 7 (OZ.Valid 7 w317.low w317.t w317.y w317.r w317.cap) (P33.root 7) :=
  Night6836Tree.sound w317 pick317 7 t2134 _ (by decide +kernel)
theorem window317 : P33.WindowCount w317 := by
  apply P33.window_count w317 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov317_1
  · exact cov317_2
  · exact cov317_3
  · exact cov317_4
  · exact cov317_5
  · exact cov317_6
  · exact cov317_7
def w318 : P33.Window := ⟨16,22,4771,4585,227794052988093155,11614,36000,5000000,81920000000⟩
def h318_0 : Height w318 := ⟨11614,36000,by decide +kernel⟩
def h318_1 : Height w318 := ⟨15869,33000,by decide +kernel⟩
def h318_2 : Height w318 := ⟨21427,30000,by decide +kernel⟩
def h318_3 : Height w318 := ⟨29498,27000,by decide +kernel⟩
def pick318 (cl : ℕ) : Height w318 := if cl<32 then (if cl<4 then (h318_0) else (h318_1)) else (if cl<312 then (h318_2) else (h318_3))
private theorem k318_1_0 : check w318 pick318 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k318_1_1 : check w318 pick318 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k318_1_2 : check w318 pick318 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w318 pick318 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k318_1_0 k318_1_1
private theorem k318_1_3 : check w318 pick318 1 t9073 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k318_1_4 : check w318 pick318 1 t7452 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k318_1_5 : check w318 pick318 1 t9074 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w318 pick318 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9073 t7452 k318_1_3 k318_1_4
private theorem k318_1_6 : check w318 pick318 1 t9075 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w318 pick318 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t9074 k318_1_2 k318_1_5
theorem cov318_1 : PA.Covered 1 (OZ.Valid 1 w318.low w318.t w318.y w318.r w318.cap) (P33.root 1) :=
  Night6836Tree.sound w318 pick318 1 t9075 _ k318_1_6
theorem cov318_2 : PA.Covered 2 (OZ.Valid 2 w318.low w318.t w318.y w318.r w318.cap) (P33.root 2) :=
  Night6836Tree.sound w318 pick318 2 t6109 _ (by decide +kernel)
theorem cov318_3 : PA.Covered 3 (OZ.Valid 3 w318.low w318.t w318.y w318.r w318.cap) (P33.root 3) :=
  Night6836Tree.sound w318 pick318 3 t564 _ (by decide +kernel)
theorem cov318_4 : PA.Covered 4 (OZ.Valid 4 w318.low w318.t w318.y w318.r w318.cap) (P33.root 4) :=
  Night6836Tree.sound w318 pick318 4 t565 _ (by decide +kernel)
theorem cov318_5 : PA.Covered 5 (OZ.Valid 5 w318.low w318.t w318.y w318.r w318.cap) (P33.root 5) :=
  Night6836Tree.sound w318 pick318 5 t566 _ (by decide +kernel)
theorem cov318_6 : PA.Covered 6 (OZ.Valid 6 w318.low w318.t w318.y w318.r w318.cap) (P33.root 6) :=
  Night6836Tree.sound w318 pick318 6 t567 _ (by decide +kernel)
theorem cov318_7 : PA.Covered 7 (OZ.Valid 7 w318.low w318.t w318.y w318.r w318.cap) (P33.root 7) :=
  Night6836Tree.sound w318 pick318 7 t2134 _ (by decide +kernel)
theorem window318 : P33.WindowCount w318 := by
  apply P33.window_count w318 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov318_1
  · exact cov318_2
  · exact cov318_3
  · exact cov318_4
  · exact cov318_5
  · exact cov318_6
  · exact cov318_7
def w319 : P33.Window := ⟨16,23,4584,4394,224619907799729881,12501,39000,5000000,81920000000⟩
def h319_0 : Height w319 := ⟨12501,39000,by decide +kernel⟩
def h319_1 : Height w319 := ⟨16507,36000,by decide +kernel⟩
def h319_2 : Height w319 := ⟨21520,33000,by decide +kernel⟩
def h319_3 : Height w319 := ⟨28297,30000,by decide +kernel⟩
def h319_4 : Height w319 := ⟨38602,27000,by decide +kernel⟩
def pick319 (cl : ℕ) : Height w319 := if cl<14 then (if cl<2 then (h319_0) else (h319_1)) else (if cl<83 then (h319_2) else (if cl<644 then (h319_3) else (h319_4)))
private theorem k319_1_0 : check w319 pick319 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k319_1_1 : check w319 pick319 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k319_1_2 : check w319 pick319 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w319 pick319 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k319_1_0 k319_1_1
private theorem k319_1_3 : check w319 pick319 1 t9073 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k319_1_4 : check w319 pick319 1 t7452 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k319_1_5 : check w319 pick319 1 t9074 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w319 pick319 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9073 t7452 k319_1_3 k319_1_4
private theorem k319_1_6 : check w319 pick319 1 t9075 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w319 pick319 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t9074 k319_1_2 k319_1_5
theorem cov319_1 : PA.Covered 1 (OZ.Valid 1 w319.low w319.t w319.y w319.r w319.cap) (P33.root 1) :=
  Night6836Tree.sound w319 pick319 1 t9075 _ k319_1_6
theorem cov319_2 : PA.Covered 2 (OZ.Valid 2 w319.low w319.t w319.y w319.r w319.cap) (P33.root 2) :=
  Night6836Tree.sound w319 pick319 2 t6109 _ (by decide +kernel)
theorem cov319_3 : PA.Covered 3 (OZ.Valid 3 w319.low w319.t w319.y w319.r w319.cap) (P33.root 3) :=
  Night6836Tree.sound w319 pick319 3 t564 _ (by decide +kernel)
theorem cov319_4 : PA.Covered 4 (OZ.Valid 4 w319.low w319.t w319.y w319.r w319.cap) (P33.root 4) :=
  Night6836Tree.sound w319 pick319 4 t565 _ (by decide +kernel)
theorem cov319_5 : PA.Covered 5 (OZ.Valid 5 w319.low w319.t w319.y w319.r w319.cap) (P33.root 5) :=
  Night6836Tree.sound w319 pick319 5 t566 _ (by decide +kernel)
theorem cov319_6 : PA.Covered 6 (OZ.Valid 6 w319.low w319.t w319.y w319.r w319.cap) (P33.root 6) :=
  Night6836Tree.sound w319 pick319 6 t567 _ (by decide +kernel)
theorem cov319_7 : PA.Covered 7 (OZ.Valid 7 w319.low w319.t w319.y w319.r w319.cap) (P33.root 7) :=
  Night6836Tree.sound w319 pick319 7 t2134 _ (by decide +kernel)
theorem window319 : P33.WindowCount w319 := by
  apply P33.window_count w319 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov319_1
  · exact cov319_2
  · exact cov319_3
  · exact cov319_4
  · exact cov319_5
  · exact cov319_6
  · exact cov319_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w320 : P33.Window := ⟨16,24,4393,4199,220822095927382052,17720,39000,5000000,81920000000⟩
def h320_0 : Height w320 := ⟨17720,39000,by decide +kernel⟩
def h320_1 : Height w320 := ⟨22414,36000,by decide +kernel⟩
def h320_2 : Height w320 := ⟨28467,33000,by decide +kernel⟩
def h320_3 : Height w320 := ⟨36971,30000,by decide +kernel⟩
def pick320 (cl : ℕ) : Height w320 := if cl<40 then (if cl<8 then (h320_0) else (h320_1)) else (if cl<312 then (h320_2) else (h320_3))
private theorem k320_1_0 : check w320 pick320 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k320_1_1 : check w320 pick320 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k320_1_2 : check w320 pick320 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w320 pick320 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k320_1_0 k320_1_1
private theorem k320_1_3 : check w320 pick320 1 t9073 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k320_1_4 : check w320 pick320 1 t7452 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k320_1_5 : check w320 pick320 1 t9074 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w320 pick320 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9073 t7452 k320_1_3 k320_1_4
private theorem k320_1_6 : check w320 pick320 1 t9075 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w320 pick320 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t9074 k320_1_2 k320_1_5
theorem cov320_1 : PA.Covered 1 (OZ.Valid 1 w320.low w320.t w320.y w320.r w320.cap) (P33.root 1) :=
  Night6836Tree.sound w320 pick320 1 t9075 _ k320_1_6
theorem cov320_2 : PA.Covered 2 (OZ.Valid 2 w320.low w320.t w320.y w320.r w320.cap) (P33.root 2) :=
  Night6836Tree.sound w320 pick320 2 t6109 _ (by decide +kernel)
theorem cov320_3 : PA.Covered 3 (OZ.Valid 3 w320.low w320.t w320.y w320.r w320.cap) (P33.root 3) :=
  Night6836Tree.sound w320 pick320 3 t564 _ (by decide +kernel)
theorem cov320_4 : PA.Covered 4 (OZ.Valid 4 w320.low w320.t w320.y w320.r w320.cap) (P33.root 4) :=
  Night6836Tree.sound w320 pick320 4 t565 _ (by decide +kernel)
theorem cov320_5 : PA.Covered 5 (OZ.Valid 5 w320.low w320.t w320.y w320.r w320.cap) (P33.root 5) :=
  Night6836Tree.sound w320 pick320 5 t566 _ (by decide +kernel)
theorem cov320_6 : PA.Covered 6 (OZ.Valid 6 w320.low w320.t w320.y w320.r w320.cap) (P33.root 6) :=
  Night6836Tree.sound w320 pick320 6 t567 _ (by decide +kernel)
theorem cov320_7 : PA.Covered 7 (OZ.Valid 7 w320.low w320.t w320.y w320.r w320.cap) (P33.root 7) :=
  Night6836Tree.sound w320 pick320 7 t2134 _ (by decide +kernel)
theorem window320 : P33.WindowCount w320 := by
  apply P33.window_count w320 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov320_1
  · exact cov320_2
  · exact cov320_3
  · exact cov320_4
  · exact cov320_5
  · exact cov320_6
  · exact cov320_7
def w321 : P33.Window := ⟨16,25,4198,4001,241052782552456560,19515,42000,5000000,81920000000⟩
def h321_0 : Height w321 := ⟨19515,42000,by decide +kernel⟩
def h321_1 : Height w321 := ⟨24036,39000,by decide +kernel⟩
def h321_2 : Height w321 := ⟨29676,36000,by decide +kernel⟩
def h321_3 : Height w321 := ⟨37196,33000,by decide +kernel⟩
def pick321 (cl : ℕ) : Height w321 := if cl<32 then (if cl<6 then (h321_0) else (h321_1)) else (if cl<136 then (h321_2) else (h321_3))
private theorem k321_1_0 : check w321 pick321 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k321_1_1 : check w321 pick321 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k321_1_2 : check w321 pick321 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w321 pick321 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k321_1_0 k321_1_1
private theorem k321_1_3 : check w321 pick321 1 t9073 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k321_1_4 : check w321 pick321 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k321_1_5 : check w321 pick321 1 t9076 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w321 pick321 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9073 t8757 k321_1_3 k321_1_4
private theorem k321_1_6 : check w321 pick321 1 t9077 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w321 pick321 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t9076 k321_1_2 k321_1_5
theorem cov321_1 : PA.Covered 1 (OZ.Valid 1 w321.low w321.t w321.y w321.r w321.cap) (P33.root 1) :=
  Night6836Tree.sound w321 pick321 1 t9077 _ k321_1_6
theorem cov321_2 : PA.Covered 2 (OZ.Valid 2 w321.low w321.t w321.y w321.r w321.cap) (P33.root 2) :=
  Night6836Tree.sound w321 pick321 2 t6109 _ (by decide +kernel)
theorem cov321_3 : PA.Covered 3 (OZ.Valid 3 w321.low w321.t w321.y w321.r w321.cap) (P33.root 3) :=
  Night6836Tree.sound w321 pick321 3 t564 _ (by decide +kernel)
theorem cov321_4 : PA.Covered 4 (OZ.Valid 4 w321.low w321.t w321.y w321.r w321.cap) (P33.root 4) :=
  Night6836Tree.sound w321 pick321 4 t565 _ (by decide +kernel)
theorem cov321_5 : PA.Covered 5 (OZ.Valid 5 w321.low w321.t w321.y w321.r w321.cap) (P33.root 5) :=
  Night6836Tree.sound w321 pick321 5 t566 _ (by decide +kernel)
theorem cov321_6 : PA.Covered 6 (OZ.Valid 6 w321.low w321.t w321.y w321.r w321.cap) (P33.root 6) :=
  Night6836Tree.sound w321 pick321 6 t567 _ (by decide +kernel)
theorem cov321_7 : PA.Covered 7 (OZ.Valid 7 w321.low w321.t w321.y w321.r w321.cap) (P33.root 7) :=
  Night6836Tree.sound w321 pick321 7 t2134 _ (by decide +kernel)
theorem window321 : P33.WindowCount w321 := by
  apply P33.window_count w321 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov321_1
  · exact cov321_2
  · exact cov321_3
  · exact cov321_4
  · exact cov321_5
  · exact cov321_6
  · exact cov321_7
def w322 : P33.Window := ⟨16,26,4000,3800,231659555326811952,21964,45000,5000000,81920000000⟩
def h322_0 : Height w322 := ⟨21964,45000,by decide +kernel⟩
def h322_1 : Height w322 := ⟨26418,42000,by decide +kernel⟩
def h322_2 : Height w322 := ⟨31848,39000,by decide +kernel⟩
def h322_3 : Height w322 := ⟨38831,36000,by decide +kernel⟩
def h322_4 : Height w322 := ⟨48505,33000,by decide +kernel⟩
def pick322 (cl : ℕ) : Height w322 := if cl<32 then (if cl<5 then (h322_0) else (h322_1)) else (if cl<92 then (h322_2) else (if cl<352 then (h322_3) else (h322_4)))
private theorem k322_1_0 : check w322 pick322 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k322_1_1 : check w322 pick322 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k322_1_2 : check w322 pick322 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w322 pick322 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k322_1_0 k322_1_1
private theorem k322_1_3 : check w322 pick322 1 t9073 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k322_1_4 : check w322 pick322 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k322_1_5 : check w322 pick322 1 t9076 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w322 pick322 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9073 t8757 k322_1_3 k322_1_4
private theorem k322_1_6 : check w322 pick322 1 t9077 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w322 pick322 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t9076 k322_1_2 k322_1_5
theorem cov322_1 : PA.Covered 1 (OZ.Valid 1 w322.low w322.t w322.y w322.r w322.cap) (P33.root 1) :=
  Night6836Tree.sound w322 pick322 1 t9077 _ k322_1_6
theorem cov322_2 : PA.Covered 2 (OZ.Valid 2 w322.low w322.t w322.y w322.r w322.cap) (P33.root 2) :=
  Night6836Tree.sound w322 pick322 2 t6109 _ (by decide +kernel)
theorem cov322_3 : PA.Covered 3 (OZ.Valid 3 w322.low w322.t w322.y w322.r w322.cap) (P33.root 3) :=
  Night6836Tree.sound w322 pick322 3 t564 _ (by decide +kernel)
theorem cov322_4 : PA.Covered 4 (OZ.Valid 4 w322.low w322.t w322.y w322.r w322.cap) (P33.root 4) :=
  Night6836Tree.sound w322 pick322 4 t565 _ (by decide +kernel)
theorem cov322_5 : PA.Covered 5 (OZ.Valid 5 w322.low w322.t w322.y w322.r w322.cap) (P33.root 5) :=
  Night6836Tree.sound w322 pick322 5 t566 _ (by decide +kernel)
theorem cov322_6 : PA.Covered 6 (OZ.Valid 6 w322.low w322.t w322.y w322.r w322.cap) (P33.root 6) :=
  Night6836Tree.sound w322 pick322 6 t567 _ (by decide +kernel)
theorem cov322_7 : PA.Covered 7 (OZ.Valid 7 w322.low w322.t w322.y w322.r w322.cap) (P33.root 7) :=
  Night6836Tree.sound w322 pick322 7 t2134 _ (by decide +kernel)
theorem window322 : P33.WindowCount w322 := by
  apply P33.window_count w322 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov322_1
  · exact cov322_2
  · exact cov322_3
  · exact cov322_4
  · exact cov322_5
  · exact cov322_6
  · exact cov322_7
def w323 : P33.Window := ⟨16,27,3799,3594,222119607261225264,25237,48000,5000000,81920000000⟩
def h323_0 : Height w323 := ⟨25237,48000,by decide +kernel⟩
def h323_1 : Height w323 := ⟨29721,45000,by decide +kernel⟩
def h323_2 : Height w323 := ⟨35100,42000,by decide +kernel⟩
def h323_3 : Height w323 := ⟨41848,39000,by decide +kernel⟩
def h323_4 : Height w323 := ⟨50835,36000,by decide +kernel⟩
def pick323 (cl : ℕ) : Height w323 := if cl<32 then (if cl<5 then (h323_0) else (h323_1)) else (if cl<83 then (h323_2) else (if cl<312 then (h323_3) else (h323_4)))
private theorem k323_1_0 : check w323 pick323 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k323_1_1 : check w323 pick323 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k323_1_2 : check w323 pick323 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w323 pick323 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k323_1_0 k323_1_1
private theorem k323_1_3 : check w323 pick323 1 t9073 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k323_1_4 : check w323 pick323 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k323_1_5 : check w323 pick323 1 t9076 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w323 pick323 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9073 t8757 k323_1_3 k323_1_4
private theorem k323_1_6 : check w323 pick323 1 t9077 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w323 pick323 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t9076 k323_1_2 k323_1_5
theorem cov323_1 : PA.Covered 1 (OZ.Valid 1 w323.low w323.t w323.y w323.r w323.cap) (P33.root 1) :=
  Night6836Tree.sound w323 pick323 1 t9077 _ k323_1_6
theorem cov323_2 : PA.Covered 2 (OZ.Valid 2 w323.low w323.t w323.y w323.r w323.cap) (P33.root 2) :=
  Night6836Tree.sound w323 pick323 2 t8957 _ (by decide +kernel)
theorem cov323_3 : PA.Covered 3 (OZ.Valid 3 w323.low w323.t w323.y w323.r w323.cap) (P33.root 3) :=
  Night6836Tree.sound w323 pick323 3 t564 _ (by decide +kernel)
theorem cov323_4 : PA.Covered 4 (OZ.Valid 4 w323.low w323.t w323.y w323.r w323.cap) (P33.root 4) :=
  Night6836Tree.sound w323 pick323 4 t565 _ (by decide +kernel)
theorem cov323_5 : PA.Covered 5 (OZ.Valid 5 w323.low w323.t w323.y w323.r w323.cap) (P33.root 5) :=
  Night6836Tree.sound w323 pick323 5 t566 _ (by decide +kernel)
theorem cov323_6 : PA.Covered 6 (OZ.Valid 6 w323.low w323.t w323.y w323.r w323.cap) (P33.root 6) :=
  Night6836Tree.sound w323 pick323 6 t567 _ (by decide +kernel)
theorem cov323_7 : PA.Covered 7 (OZ.Valid 7 w323.low w323.t w323.y w323.r w323.cap) (P33.root 7) :=
  Night6836Tree.sound w323 pick323 7 t2134 _ (by decide +kernel)
theorem window323 : P33.WindowCount w323 := by
  apply P33.window_count w323 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov323_1
  · exact cov323_2
  · exact cov323_3
  · exact cov323_4
  · exact cov323_5
  · exact cov323_6
  · exact cov323_7
def w324 : P33.Window := ⟨16,28,3593,3385,212335163432044208,25484,54000,5000000,81920000000⟩
def h324_0 : Height w324 := ⟨25484,54000,by decide +kernel⟩
def h324_1 : Height w324 := ⟨29480,51000,by decide +kernel⟩
def h324_2 : Height w324 := ⟨34084,48000,by decide +kernel⟩
def h324_3 : Height w324 := ⟨39547,45000,by decide +kernel⟩
def h324_4 : Height w324 := ⟨46282,42000,by decide +kernel⟩
def h324_5 : Height w324 := ⟨55014,39000,by decide +kernel⟩
def pick324 (cl : ℕ) : Height w324 := if cl<32 then (if cl<2 then (h324_0) else (if cl<6 then (h324_1) else (h324_2))) else (if cl<83 then (h324_3) else (if cl<312 then (h324_4) else (h324_5)))
private theorem k324_1_0 : check w324 pick324 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k324_1_1 : check w324 pick324 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k324_1_2 : check w324 pick324 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w324 pick324 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k324_1_0 k324_1_1
private theorem k324_1_3 : check w324 pick324 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k324_1_4 : check w324 pick324 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k324_1_5 : check w324 pick324 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w324 pick324 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k324_1_3 k324_1_4
private theorem k324_1_6 : check w324 pick324 1 t9065 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w324 pick324 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t8758 k324_1_2 k324_1_5
theorem cov324_1 : PA.Covered 1 (OZ.Valid 1 w324.low w324.t w324.y w324.r w324.cap) (P33.root 1) :=
  Night6836Tree.sound w324 pick324 1 t9065 _ k324_1_6
theorem cov324_2 : PA.Covered 2 (OZ.Valid 2 w324.low w324.t w324.y w324.r w324.cap) (P33.root 2) :=
  Night6836Tree.sound w324 pick324 2 t6560 _ (by decide +kernel)
theorem cov324_3 : PA.Covered 3 (OZ.Valid 3 w324.low w324.t w324.y w324.r w324.cap) (P33.root 3) :=
  Night6836Tree.sound w324 pick324 3 t564 _ (by decide +kernel)
theorem cov324_4 : PA.Covered 4 (OZ.Valid 4 w324.low w324.t w324.y w324.r w324.cap) (P33.root 4) :=
  Night6836Tree.sound w324 pick324 4 t565 _ (by decide +kernel)
theorem cov324_5 : PA.Covered 5 (OZ.Valid 5 w324.low w324.t w324.y w324.r w324.cap) (P33.root 5) :=
  Night6836Tree.sound w324 pick324 5 t566 _ (by decide +kernel)
theorem cov324_6 : PA.Covered 6 (OZ.Valid 6 w324.low w324.t w324.y w324.r w324.cap) (P33.root 6) :=
  Night6836Tree.sound w324 pick324 6 t567 _ (by decide +kernel)
theorem cov324_7 : PA.Covered 7 (OZ.Valid 7 w324.low w324.t w324.y w324.r w324.cap) (P33.root 7) :=
  Night6836Tree.sound w324 pick324 7 t2134 _ (by decide +kernel)
theorem window324 : P33.WindowCount w324 := by
  apply P33.window_count w324 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov324_1
  · exact cov324_2
  · exact cov324_3
  · exact cov324_4
  · exact cov324_5
  · exact cov324_6
  · exact cov324_7
def w325 : P33.Window := ⟨16,29,3384,3172,202403995374256512,30798,57000,5000000,81920000000⟩
def h325_0 : Height w325 := ⟨30798,57000,by decide +kernel⟩
def h325_1 : Height w325 := ⟨35004,54000,by decide +kernel⟩
def h325_2 : Height w325 := ⟨39832,51000,by decide +kernel⟩
def h325_3 : Height w325 := ⟨45523,48000,by decide +kernel⟩
def h325_4 : Height w325 := ⟨52461,45000,by decide +kernel⟩
def h325_5 : Height w325 := ⟨61293,42000,by decide +kernel⟩
def pick325 (cl : ℕ) : Height w325 := if cl<32 then (if cl<4 then (h325_0) else (if cl<10 then (h325_1) else (h325_2))) else (if cl<92 then (h325_3) else (if cl<312 then (h325_4) else (h325_5)))
private theorem k325_1_0 : check w325 pick325 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k325_1_1 : check w325 pick325 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k325_1_2 : check w325 pick325 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w325 pick325 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k325_1_0 k325_1_1
private theorem k325_1_3 : check w325 pick325 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k325_1_4 : check w325 pick325 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k325_1_5 : check w325 pick325 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w325 pick325 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k325_1_3 k325_1_4
private theorem k325_1_6 : check w325 pick325 1 t9065 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w325 pick325 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t8758 k325_1_2 k325_1_5
theorem cov325_1 : PA.Covered 1 (OZ.Valid 1 w325.low w325.t w325.y w325.r w325.cap) (P33.root 1) :=
  Night6836Tree.sound w325 pick325 1 t9065 _ k325_1_6
theorem cov325_2 : PA.Covered 2 (OZ.Valid 2 w325.low w325.t w325.y w325.r w325.cap) (P33.root 2) :=
  Night6836Tree.sound w325 pick325 2 t6560 _ (by decide +kernel)
theorem cov325_3 : PA.Covered 3 (OZ.Valid 3 w325.low w325.t w325.y w325.r w325.cap) (P33.root 3) :=
  Night6836Tree.sound w325 pick325 3 t564 _ (by decide +kernel)
theorem cov325_4 : PA.Covered 4 (OZ.Valid 4 w325.low w325.t w325.y w325.r w325.cap) (P33.root 4) :=
  Night6836Tree.sound w325 pick325 4 t565 _ (by decide +kernel)
theorem cov325_5 : PA.Covered 5 (OZ.Valid 5 w325.low w325.t w325.y w325.r w325.cap) (P33.root 5) :=
  Night6836Tree.sound w325 pick325 5 t566 _ (by decide +kernel)
theorem cov325_6 : PA.Covered 6 (OZ.Valid 6 w325.low w325.t w325.y w325.r w325.cap) (P33.root 6) :=
  Night6836Tree.sound w325 pick325 6 t567 _ (by decide +kernel)
theorem cov325_7 : PA.Covered 7 (OZ.Valid 7 w325.low w325.t w325.y w325.r w325.cap) (P33.root 7) :=
  Night6836Tree.sound w325 pick325 7 t2134 _ (by decide +kernel)
theorem window325 : P33.WindowCount w325 := by
  apply P33.window_count w325 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov325_1
  · exact cov325_2
  · exact cov325_3
  · exact cov325_4
  · exact cov325_5
  · exact cov325_6
  · exact cov325_7
def w326 : P33.Window := ⟨16,30,3171,2954,197099473664514701,33729,63000,5000000,81920000000⟩
def h326_0 : Height w326 := ⟨33729,63000,by decide +kernel⟩
def h326_1 : Height w326 := ⟨37757,60000,by decide +kernel⟩
def h326_2 : Height w326 := ⟨42284,57000,by decide +kernel⟩
def h326_3 : Height w326 := ⟨47476,54000,by decide +kernel⟩
def h326_4 : Height w326 := ⟨53577,51000,by decide +kernel⟩
def h326_5 : Height w326 := ⟨60967,48000,by decide +kernel⟩
def h326_6 : Height w326 := ⟨70274,45000,by decide +kernel⟩
def pick326 (cl : ℕ) : Height w326 := if cl<32 then (if cl<2 then (h326_0) else (if cl<6 then (h326_1) else (h326_2))) else (if cl<120 then (if cl<42 then (h326_3) else (h326_4)) else (if cl<312 then (h326_5) else (h326_6)))
private theorem k326_1_0 : check w326 pick326 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k326_1_1 : check w326 pick326 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k326_1_2 : check w326 pick326 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w326 pick326 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k326_1_0 k326_1_1
private theorem k326_1_3 : check w326 pick326 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k326_1_4 : check w326 pick326 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k326_1_5 : check w326 pick326 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w326 pick326 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k326_1_3 k326_1_4
private theorem k326_1_6 : check w326 pick326 1 t9065 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w326 pick326 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t8758 k326_1_2 k326_1_5
theorem cov326_1 : PA.Covered 1 (OZ.Valid 1 w326.low w326.t w326.y w326.r w326.cap) (P33.root 1) :=
  Night6836Tree.sound w326 pick326 1 t9065 _ k326_1_6
theorem cov326_2 : PA.Covered 2 (OZ.Valid 2 w326.low w326.t w326.y w326.r w326.cap) (P33.root 2) :=
  Night6836Tree.sound w326 pick326 2 t6560 _ (by decide +kernel)
theorem cov326_3 : PA.Covered 3 (OZ.Valid 3 w326.low w326.t w326.y w326.r w326.cap) (P33.root 3) :=
  Night6836Tree.sound w326 pick326 3 t564 _ (by decide +kernel)
theorem cov326_4 : PA.Covered 4 (OZ.Valid 4 w326.low w326.t w326.y w326.r w326.cap) (P33.root 4) :=
  Night6836Tree.sound w326 pick326 4 t565 _ (by decide +kernel)
theorem cov326_5 : PA.Covered 5 (OZ.Valid 5 w326.low w326.t w326.y w326.r w326.cap) (P33.root 5) :=
  Night6836Tree.sound w326 pick326 5 t566 _ (by decide +kernel)
theorem cov326_6 : PA.Covered 6 (OZ.Valid 6 w326.low w326.t w326.y w326.r w326.cap) (P33.root 6) :=
  Night6836Tree.sound w326 pick326 6 t567 _ (by decide +kernel)
theorem cov326_7 : PA.Covered 7 (OZ.Valid 7 w326.low w326.t w326.y w326.r w326.cap) (P33.root 7) :=
  Night6836Tree.sound w326 pick326 7 t2134 _ (by decide +kernel)
theorem window326 : P33.WindowCount w326 := by
  apply P33.window_count w326 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov326_1
  · exact cov326_2
  · exact cov326_3
  · exact cov326_4
  · exact cov326_5
  · exact cov326_6
  · exact cov326_7
def w327 : P33.Window := ⟨16,31,2953,2733,197686550305489101,38473,69000,5000000,81920000000⟩
def h327_0 : Height w327 := ⟨38473,69000,by decide +kernel⟩
def h327_1 : Height w327 := ⟨42471,66000,by decide +kernel⟩
def h327_2 : Height w327 := ⟨46907,63000,by decide +kernel⟩
def h327_3 : Height w327 := ⟨51906,60000,by decide +kernel⟩
def h327_4 : Height w327 := ⟨57649,57000,by decide +kernel⟩
def h327_5 : Height w327 := ⟨64398,54000,by decide +kernel⟩
def h327_6 : Height w327 := ⟨72557,51000,by decide +kernel⟩
def h327_7 : Height w327 := ⟨82776,48000,by decide +kernel⟩
def pick327 (cl : ℕ) : Height w327 := if cl<32 then (if cl<5 then (if cl<2 then (h327_0) else (h327_1)) else (if cl<14 then (h327_2) else (h327_3))) else (if cl<312 then (if cl<83 then (h327_4) else (h327_5)) else (if cl<594 then (h327_6) else (h327_7)))
private theorem k327_1_0 : check w327 pick327 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k327_1_1 : check w327 pick327 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k327_1_2 : check w327 pick327 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w327 pick327 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k327_1_0 k327_1_1
private theorem k327_1_3 : check w327 pick327 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k327_1_4 : check w327 pick327 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k327_1_5 : check w327 pick327 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w327 pick327 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k327_1_3 k327_1_4
private theorem k327_1_6 : check w327 pick327 1 t9065 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w327 pick327 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t8758 k327_1_2 k327_1_5
theorem cov327_1 : PA.Covered 1 (OZ.Valid 1 w327.low w327.t w327.y w327.r w327.cap) (P33.root 1) :=
  Night6836Tree.sound w327 pick327 1 t9065 _ k327_1_6
theorem cov327_2 : PA.Covered 2 (OZ.Valid 2 w327.low w327.t w327.y w327.r w327.cap) (P33.root 2) :=
  Night6836Tree.sound w327 pick327 2 t6560 _ (by decide +kernel)
theorem cov327_3 : PA.Covered 3 (OZ.Valid 3 w327.low w327.t w327.y w327.r w327.cap) (P33.root 3) :=
  Night6836Tree.sound w327 pick327 3 t564 _ (by decide +kernel)
theorem cov327_4 : PA.Covered 4 (OZ.Valid 4 w327.low w327.t w327.y w327.r w327.cap) (P33.root 4) :=
  Night6836Tree.sound w327 pick327 4 t565 _ (by decide +kernel)
theorem cov327_5 : PA.Covered 5 (OZ.Valid 5 w327.low w327.t w327.y w327.r w327.cap) (P33.root 5) :=
  Night6836Tree.sound w327 pick327 5 t566 _ (by decide +kernel)
theorem cov327_6 : PA.Covered 6 (OZ.Valid 6 w327.low w327.t w327.y w327.r w327.cap) (P33.root 6) :=
  Night6836Tree.sound w327 pick327 6 t567 _ (by decide +kernel)
theorem cov327_7 : PA.Covered 7 (OZ.Valid 7 w327.low w327.t w327.y w327.r w327.cap) (P33.root 7) :=
  Night6836Tree.sound w327 pick327 7 t2134 _ (by decide +kernel)
theorem window327 : P33.WindowCount w327 := by
  apply P33.window_count w327 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov327_1
  · exact cov327_2
  · exact cov327_3
  · exact cov327_4
  · exact cov327_5
  · exact cov327_6
  · exact cov327_7
def w328 : P33.Window := ⟨16,32,2732,2575,192162659825245726,45815,72000,5000000,81920000000⟩
def h328_0 : Height w328 := ⟨45815,72000,by decide +kernel⟩
def h328_1 : Height w328 := ⟨50066,69000,by decide +kernel⟩
def h328_2 : Height w328 := ⟨54783,66000,by decide +kernel⟩
def h328_3 : Height w328 := ⟨60092,63000,by decide +kernel⟩
def h328_4 : Height w328 := ⟨66175,60000,by decide +kernel⟩
def h328_5 : Height w328 := ⟨73291,57000,by decide +kernel⟩
def h328_6 : Height w328 := ⟨81831,54000,by decide +kernel⟩
def pick328 (cl : ℕ) : Height w328 := if cl<32 then (if cl<4 then (h328_0) else (if cl<8 then (h328_1) else (h328_2))) else (if cl<100 then (if cl<41 then (h328_3) else (h328_4)) else (if cl<312 then (h328_5) else (h328_6)))
private theorem k328_1_0 : check w328 pick328 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k328_1_1 : check w328 pick328 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k328_1_2 : check w328 pick328 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w328 pick328 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k328_1_0 k328_1_1
private theorem k328_1_3 : check w328 pick328 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k328_1_4 : check w328 pick328 1 t8757 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k328_1_5 : check w328 pick328 1 t8758 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w328 pick328 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8757 k328_1_3 k328_1_4
private theorem k328_1_6 : check w328 pick328 1 t9065 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w328 pick328 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t8758 k328_1_2 k328_1_5
theorem cov328_1 : PA.Covered 1 (OZ.Valid 1 w328.low w328.t w328.y w328.r w328.cap) (P33.root 1) :=
  Night6836Tree.sound w328 pick328 1 t9065 _ k328_1_6
theorem cov328_2 : PA.Covered 2 (OZ.Valid 2 w328.low w328.t w328.y w328.r w328.cap) (P33.root 2) :=
  Night6836Tree.sound w328 pick328 2 t6560 _ (by decide +kernel)
theorem cov328_3 : PA.Covered 3 (OZ.Valid 3 w328.low w328.t w328.y w328.r w328.cap) (P33.root 3) :=
  Night6836Tree.sound w328 pick328 3 t564 _ (by decide +kernel)
theorem cov328_4 : PA.Covered 4 (OZ.Valid 4 w328.low w328.t w328.y w328.r w328.cap) (P33.root 4) :=
  Night6836Tree.sound w328 pick328 4 t565 _ (by decide +kernel)
theorem cov328_5 : PA.Covered 5 (OZ.Valid 5 w328.low w328.t w328.y w328.r w328.cap) (P33.root 5) :=
  Night6836Tree.sound w328 pick328 5 t566 _ (by decide +kernel)
theorem cov328_6 : PA.Covered 6 (OZ.Valid 6 w328.low w328.t w328.y w328.r w328.cap) (P33.root 6) :=
  Night6836Tree.sound w328 pick328 6 t567 _ (by decide +kernel)
theorem cov328_7 : PA.Covered 7 (OZ.Valid 7 w328.low w328.t w328.y w328.r w328.cap) (P33.root 7) :=
  Night6836Tree.sound w328 pick328 7 t2134 _ (by decide +kernel)
theorem window328 : P33.WindowCount w328 := by
  apply P33.window_count w328 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov328_1
  · exact cov328_2
  · exact cov328_3
  · exact cov328_4
  · exact cov328_5
  · exact cov328_6
  · exact cov328_7
def w329 : P33.Window := ⟨5,29,8155,8120,232480530772361838,15941,12000,5000000,81920000000⟩
def h329_0 : Height w329 := ⟨15941,12000,by decide +kernel⟩
def h329_1 : Height w329 := ⟨20282,9000,by decide +kernel⟩
def h329_2 : Height w329 := ⟨30420,6000,by decide +kernel⟩
def pick329 (cl : ℕ) : Height w329 := if cl<5 then (h329_0) else (if cl<561 then (h329_1) else (h329_2))
private theorem k329_1_0 : check w329 pick329 1 t9079 ⟨1,7,2,16,1,52,1,83⟩ = true := by decide +kernel
private theorem k329_1_1 : check w329 pick329 1 t2541 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k329_1_2 : check w329 pick329 1 t2559 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k329_1_3 : check w329 pick329 1 t2560 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w329 pick329 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t2541 t2559 k329_1_1 k329_1_2
private theorem k329_1_4 : check w329 pick329 1 t9080 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w329 pick329 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t9079 t2560 k329_1_0 k329_1_3
private theorem k329_1_5 : check w329 pick329 1 t2576 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k329_1_6 : check w329 pick329 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k329_1_7 : check w329 pick329 1 t2577 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w329 pick329 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t2576 t382 k329_1_5 k329_1_6
private theorem k329_1_8 : check w329 pick329 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k329_1_9 : check w329 pick329 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k329_1_10 : check w329 pick329 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w329 pick329 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k329_1_8 k329_1_9
private theorem k329_1_11 : check w329 pick329 1 t9085 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w329 pick329 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t2577 t9084 k329_1_7 k329_1_10
private theorem k329_1_12 : check w329 pick329 1 t9086 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w329 pick329 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t9080 t9085 k329_1_4 k329_1_11
theorem cov329_1 : PA.Covered 1 (OZ.Valid 1 w329.low w329.t w329.y w329.r w329.cap) (P33.root 1) :=
  Night6836Tree.sound w329 pick329 1 t9086 _ k329_1_12
theorem cov329_2 : PA.Covered 2 (OZ.Valid 2 w329.low w329.t w329.y w329.r w329.cap) (P33.root 2) :=
  Night6836Tree.sound w329 pick329 2 t2403 _ (by decide +kernel)
theorem cov329_3 : PA.Covered 3 (OZ.Valid 3 w329.low w329.t w329.y w329.r w329.cap) (P33.root 3) :=
  Night6836Tree.sound w329 pick329 3 t564 _ (by decide +kernel)
theorem cov329_4 : PA.Covered 4 (OZ.Valid 4 w329.low w329.t w329.y w329.r w329.cap) (P33.root 4) :=
  Night6836Tree.sound w329 pick329 4 t565 _ (by decide +kernel)
theorem cov329_5 : PA.Covered 5 (OZ.Valid 5 w329.low w329.t w329.y w329.r w329.cap) (P33.root 5) :=
  Night6836Tree.sound w329 pick329 5 t566 _ (by decide +kernel)
theorem cov329_6 : PA.Covered 6 (OZ.Valid 6 w329.low w329.t w329.y w329.r w329.cap) (P33.root 6) :=
  Night6836Tree.sound w329 pick329 6 t567 _ (by decide +kernel)
theorem cov329_7 : PA.Covered 7 (OZ.Valid 7 w329.low w329.t w329.y w329.r w329.cap) (P33.root 7) :=
  Night6836Tree.sound w329 pick329 7 t568 _ (by decide +kernel)
theorem window329 : P33.WindowCount w329 := by
  apply P33.window_count w329 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov329_1
  · exact cov329_2
  · exact cov329_3
  · exact cov329_4
  · exact cov329_5
  · exact cov329_6
  · exact cov329_7
end ProximityPrize.SubmissionLower.Night6836Bank
