/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT02
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w210 : P33.Window := ⟨12,57,1874,1650,213335122698833132,160618,120000,5000000,81920000000⟩
def h210_0 : Height w210 := ⟨160618,120000,by decide +kernel⟩
def h210_1 : Height w210 := ⟨168601,114000,by decide +kernel⟩
def h210_2 : Height w210 := ⟨172886,111000,by decide +kernel⟩
def h210_3 : Height w210 := ⟨177398,108000,by decide +kernel⟩
def h210_4 : Height w210 := ⟨182166,105000,by decide +kernel⟩
def h210_5 : Height w210 := ⟨187225,102000,by decide +kernel⟩
def h210_6 : Height w210 := ⟨198381,96000,by decide +kernel⟩
def h210_7 : Height w210 := ⟨204585,93000,by decide +kernel⟩
def h210_8 : Height w210 := ⟨211296,90000,by decide +kernel⟩
def h210_9 : Height w210 := ⟨218599,87000,by decide +kernel⟩
def h210_10 : Height w210 := ⟨235433,81000,by decide +kernel⟩
def h210_11 : Height w210 := ⟨245267,78000,by decide +kernel⟩
def pick210 (cl : ℕ) : Height w210 := if cl<32 then (if cl<6 then (if cl<2 then (h210_0) else (if cl<4 then (h210_1) else (h210_2))) else (if cl<10 then (h210_3) else (if cl<14 then (h210_4) else (h210_5)))) else (if cl<117 then (if cl<44 then (h210_6) else (if cl<83 then (h210_7) else (h210_8))) else (if cl<312 then (h210_9) else (if cl<416 then (h210_10) else (h210_11))))
private theorem k210_1_0 : check w210 pick210 1 t8364 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k210_1_1 : check w210 pick210 1 t8359 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k210_1_2 : check w210 pick210 1 t8365 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w210 pick210 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t8364 t8359 k210_1_0 k210_1_1
private theorem k210_1_3 : check w210 pick210 1 t7434 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k210_1_4 : check w210 pick210 1 t8373 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k210_1_5 : check w210 pick210 1 t8374 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w210 pick210 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7434 t8373 k210_1_3 k210_1_4
private theorem k210_1_6 : check w210 pick210 1 t8375 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w210 pick210 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8365 t8374 k210_1_2 k210_1_5
theorem cov210_1 : PA.Covered 1 (OZ.Valid 1 w210.low w210.t w210.y w210.r w210.cap) (P33.root 1) :=
  Night6836Tree.sound w210 pick210 1 t8375 _ k210_1_6
theorem cov210_2 : PA.Covered 2 (OZ.Valid 2 w210.low w210.t w210.y w210.r w210.cap) (P33.root 2) :=
  Night6836Tree.sound w210 pick210 2 t6618 _ (by decide +kernel)
theorem cov210_3 : PA.Covered 3 (OZ.Valid 3 w210.low w210.t w210.y w210.r w210.cap) (P33.root 3) :=
  Night6836Tree.sound w210 pick210 3 t564 _ (by decide +kernel)
theorem cov210_4 : PA.Covered 4 (OZ.Valid 4 w210.low w210.t w210.y w210.r w210.cap) (P33.root 4) :=
  Night6836Tree.sound w210 pick210 4 t565 _ (by decide +kernel)
theorem cov210_5 : PA.Covered 5 (OZ.Valid 5 w210.low w210.t w210.y w210.r w210.cap) (P33.root 5) :=
  Night6836Tree.sound w210 pick210 5 t566 _ (by decide +kernel)
theorem cov210_6 : PA.Covered 6 (OZ.Valid 6 w210.low w210.t w210.y w210.r w210.cap) (P33.root 6) :=
  Night6836Tree.sound w210 pick210 6 t567 _ (by decide +kernel)
theorem cov210_7 : PA.Covered 7 (OZ.Valid 7 w210.low w210.t w210.y w210.r w210.cap) (P33.root 7) :=
  Night6836Tree.sound w210 pick210 7 t2134 _ (by decide +kernel)
theorem window210 : P33.WindowCount w210 := by
  apply P33.window_count w210 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov210_1
  · exact cov210_2
  · exact cov210_3
  · exact cov210_4
  · exact cov210_5
  · exact cov210_6
  · exact cov210_7
def w211 : P33.Window := ⟨13,17,7441,7403,235249288951954431,4844,18000,5000000,81920000000⟩
def h211_0 : Height w211 := ⟨4844,18000,by decide +kernel⟩
def h211_1 : Height w211 := ⟨9591,15000,by decide +kernel⟩
def h211_2 : Height w211 := ⟨20319,12000,by decide +kernel⟩
def pick211 (cl : ℕ) : Height w211 := if cl<8 then (h211_0) else (if cl<922 then (h211_1) else (h211_2))
private theorem k211_1_0 : check w211 pick211 1 t7116 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k211_1_1 : check w211 pick211 1 t8381 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k211_1_2 : check w211 pick211 1 t8382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w211 pick211 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7116 t8381 k211_1_0 k211_1_1
private theorem k211_1_3 : check w211 pick211 1 t7064 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k211_1_4 : check w211 pick211 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k211_1_5 : check w211 pick211 1 t7098 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w211 pick211 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7064 t7097 k211_1_3 k211_1_4
private theorem k211_1_6 : check w211 pick211 1 t8383 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w211 pick211 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8382 t7098 k211_1_2 k211_1_5
theorem cov211_1 : PA.Covered 1 (OZ.Valid 1 w211.low w211.t w211.y w211.r w211.cap) (P33.root 1) :=
  Night6836Tree.sound w211 pick211 1 t8383 _ k211_1_6
theorem cov211_2 : PA.Covered 2 (OZ.Valid 2 w211.low w211.t w211.y w211.r w211.cap) (P33.root 2) :=
  Night6836Tree.sound w211 pick211 2 t7224 _ (by decide +kernel)
theorem cov211_3 : PA.Covered 3 (OZ.Valid 3 w211.low w211.t w211.y w211.r w211.cap) (P33.root 3) :=
  Night6836Tree.sound w211 pick211 3 t564 _ (by decide +kernel)
theorem cov211_4 : PA.Covered 4 (OZ.Valid 4 w211.low w211.t w211.y w211.r w211.cap) (P33.root 4) :=
  Night6836Tree.sound w211 pick211 4 t565 _ (by decide +kernel)
theorem cov211_5 : PA.Covered 5 (OZ.Valid 5 w211.low w211.t w211.y w211.r w211.cap) (P33.root 5) :=
  Night6836Tree.sound w211 pick211 5 t566 _ (by decide +kernel)
theorem cov211_6 : PA.Covered 6 (OZ.Valid 6 w211.low w211.t w211.y w211.r w211.cap) (P33.root 6) :=
  Night6836Tree.sound w211 pick211 6 t567 _ (by decide +kernel)
theorem cov211_7 : PA.Covered 7 (OZ.Valid 7 w211.low w211.t w211.y w211.r w211.cap) (P33.root 7) :=
  Night6836Tree.sound w211 pick211 7 t568 _ (by decide +kernel)
theorem window211 : P33.WindowCount w211 := by
  apply P33.window_count w211 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov211_1
  · exact cov211_2
  · exact cov211_3
  · exact cov211_4
  · exact cov211_5
  · exact cov211_6
  · exact cov211_7
def w212 : P33.Window := ⟨13,18,7402,7363,239876677976037212,6323,18000,5000000,81920000000⟩
def h212_0 : Height w212 := ⟨6323,18000,by decide +kernel⟩
def h212_1 : Height w212 := ⟨11461,15000,by decide +kernel⟩
def h212_2 : Height w212 := ⟨23392,12000,by decide +kernel⟩
def pick212 (cl : ℕ) : Height w212 := if cl<32 then (h212_0) else (if cl<922 then (h212_1) else (h212_2))
private theorem k212_1_0 : check w212 pick212 1 t7116 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k212_1_1 : check w212 pick212 1 t8381 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k212_1_2 : check w212 pick212 1 t8382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w212 pick212 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7116 t8381 k212_1_0 k212_1_1
private theorem k212_1_3 : check w212 pick212 1 t7064 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k212_1_4 : check w212 pick212 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k212_1_5 : check w212 pick212 1 t7098 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w212 pick212 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7064 t7097 k212_1_3 k212_1_4
private theorem k212_1_6 : check w212 pick212 1 t8383 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w212 pick212 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8382 t7098 k212_1_2 k212_1_5
theorem cov212_1 : PA.Covered 1 (OZ.Valid 1 w212.low w212.t w212.y w212.r w212.cap) (P33.root 1) :=
  Night6836Tree.sound w212 pick212 1 t8383 _ k212_1_6
theorem cov212_2 : PA.Covered 2 (OZ.Valid 2 w212.low w212.t w212.y w212.r w212.cap) (P33.root 2) :=
  Night6836Tree.sound w212 pick212 2 t7224 _ (by decide +kernel)
theorem cov212_3 : PA.Covered 3 (OZ.Valid 3 w212.low w212.t w212.y w212.r w212.cap) (P33.root 3) :=
  Night6836Tree.sound w212 pick212 3 t564 _ (by decide +kernel)
theorem cov212_4 : PA.Covered 4 (OZ.Valid 4 w212.low w212.t w212.y w212.r w212.cap) (P33.root 4) :=
  Night6836Tree.sound w212 pick212 4 t565 _ (by decide +kernel)
theorem cov212_5 : PA.Covered 5 (OZ.Valid 5 w212.low w212.t w212.y w212.r w212.cap) (P33.root 5) :=
  Night6836Tree.sound w212 pick212 5 t566 _ (by decide +kernel)
theorem cov212_6 : PA.Covered 6 (OZ.Valid 6 w212.low w212.t w212.y w212.r w212.cap) (P33.root 6) :=
  Night6836Tree.sound w212 pick212 6 t567 _ (by decide +kernel)
theorem cov212_7 : PA.Covered 7 (OZ.Valid 7 w212.low w212.t w212.y w212.r w212.cap) (P33.root 7) :=
  Night6836Tree.sound w212 pick212 7 t568 _ (by decide +kernel)
theorem window212 : P33.WindowCount w212 := by
  apply P33.window_count w212 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov212_1
  · exact cov212_2
  · exact cov212_3
  · exact cov212_4
  · exact cov212_5
  · exact cov212_6
  · exact cov212_7
def w213 : P33.Window := ⟨13,19,7218,6219,203859019399271695,6918,23000,5000000,81920000000⟩
def h213_0 : Height w213 := ⟨6918,23000,by decide +kernel⟩
def h213_1 : Height w213 := ⟨12819,19000,by decide +kernel⟩
def h213_2 : Height w213 := ⟨25497,15000,by decide +kernel⟩
def pick213 (cl : ℕ) : Height w213 := if cl<5 then (h213_0) else (if cl<317 then (h213_1) else (h213_2))
private theorem k213_1_0 : check w213 pick213 1 t7465 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k213_1_1 : check w213 pick213 1 t8386 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k213_1_2 : check w213 pick213 1 t8387 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w213 pick213 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7465 t8386 k213_1_0 k213_1_1
private theorem k213_1_3 : check w213 pick213 1 t8390 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k213_1_4 : check w213 pick213 1 t7482 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k213_1_5 : check w213 pick213 1 t8391 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w213 pick213 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t8390 t7482 k213_1_3 k213_1_4
private theorem k213_1_6 : check w213 pick213 1 t8392 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w213 pick213 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8387 t8391 k213_1_2 k213_1_5
private theorem k213_1_7 : check w213 pick213 1 t7179 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k213_1_8 : check w213 pick213 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k213_1_9 : check w213 pick213 1 t7180 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w213 pick213 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7179 t6872 k213_1_7 k213_1_8
private theorem k213_1_10 : check w213 pick213 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k213_1_11 : check w213 pick213 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k213_1_12 : check w213 pick213 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w213 pick213 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k213_1_10 k213_1_11
private theorem k213_1_13 : check w213 pick213 1 t7191 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w213 pick213 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7180 t7190 k213_1_9 k213_1_12
private theorem k213_1_14 : check w213 pick213 1 t8393 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w213 pick213 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8392 t7191 k213_1_6 k213_1_13
theorem cov213_1 : PA.Covered 1 (OZ.Valid 1 w213.low w213.t w213.y w213.r w213.cap) (P33.root 1) :=
  Night6836Tree.sound w213 pick213 1 t8393 _ k213_1_14
private theorem k213_2_0 : check w213 pick213 2 t7548 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k213_2_1 : check w213 pick213 2 t8396 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k213_2_2 : check w213 pick213 2 t8397 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w213 pick213 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7548 t8396 k213_2_0 k213_2_1
theorem cov213_2 : PA.Covered 2 (OZ.Valid 2 w213.low w213.t w213.y w213.r w213.cap) (P33.root 2) :=
  Night6836Tree.sound w213 pick213 2 t8397 _ k213_2_2
theorem cov213_3 : PA.Covered 3 (OZ.Valid 3 w213.low w213.t w213.y w213.r w213.cap) (P33.root 3) :=
  Night6836Tree.sound w213 pick213 3 t564 _ (by decide +kernel)
theorem cov213_4 : PA.Covered 4 (OZ.Valid 4 w213.low w213.t w213.y w213.r w213.cap) (P33.root 4) :=
  Night6836Tree.sound w213 pick213 4 t565 _ (by decide +kernel)
theorem cov213_5 : PA.Covered 5 (OZ.Valid 5 w213.low w213.t w213.y w213.r w213.cap) (P33.root 5) :=
  Night6836Tree.sound w213 pick213 5 t566 _ (by decide +kernel)
theorem cov213_6 : PA.Covered 6 (OZ.Valid 6 w213.low w213.t w213.y w213.r w213.cap) (P33.root 6) :=
  Night6836Tree.sound w213 pick213 6 t567 _ (by decide +kernel)
theorem cov213_7 : PA.Covered 7 (OZ.Valid 7 w213.low w213.t w213.y w213.r w213.cap) (P33.root 7) :=
  Night6836Tree.sound w213 pick213 7 t568 _ (by decide +kernel)
theorem window213 : P33.WindowCount w213 := by
  apply P33.window_count w213 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov213_1
  · exact cov213_2
  · exact cov213_3
  · exact cov213_4
  · exact cov213_5
  · exact cov213_6
  · exact cov213_7
def w214 : P33.Window := ⟨13,19,7362,7283,243384989643320887,8016,18000,5000000,81920000000⟩
def h214_0 : Height w214 := ⟨8016,18000,by decide +kernel⟩
def h214_1 : Height w214 := ⟨13662,15000,by decide +kernel⟩
def h214_2 : Height w214 := ⟨27274,12000,by decide +kernel⟩
def pick214 (cl : ℕ) : Height w214 := if cl<32 then (h214_0) else (if cl<1021 then (h214_1) else (h214_2))
private theorem k214_1_0 : check w214 pick214 1 t7116 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k214_1_1 : check w214 pick214 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k214_1_2 : check w214 pick214 1 t7117 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w214 pick214 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7116 t7032 k214_1_0 k214_1_1
private theorem k214_1_3 : check w214 pick214 1 t7064 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k214_1_4 : check w214 pick214 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k214_1_5 : check w214 pick214 1 t7098 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w214 pick214 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7064 t7097 k214_1_3 k214_1_4
private theorem k214_1_6 : check w214 pick214 1 t7118 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w214 pick214 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7117 t7098 k214_1_2 k214_1_5
theorem cov214_1 : PA.Covered 1 (OZ.Valid 1 w214.low w214.t w214.y w214.r w214.cap) (P33.root 1) :=
  Night6836Tree.sound w214 pick214 1 t7118 _ k214_1_6
theorem cov214_2 : PA.Covered 2 (OZ.Valid 2 w214.low w214.t w214.y w214.r w214.cap) (P33.root 2) :=
  Night6836Tree.sound w214 pick214 2 t8398 _ (by decide +kernel)
theorem cov214_3 : PA.Covered 3 (OZ.Valid 3 w214.low w214.t w214.y w214.r w214.cap) (P33.root 3) :=
  Night6836Tree.sound w214 pick214 3 t564 _ (by decide +kernel)
theorem cov214_4 : PA.Covered 4 (OZ.Valid 4 w214.low w214.t w214.y w214.r w214.cap) (P33.root 4) :=
  Night6836Tree.sound w214 pick214 4 t565 _ (by decide +kernel)
theorem cov214_5 : PA.Covered 5 (OZ.Valid 5 w214.low w214.t w214.y w214.r w214.cap) (P33.root 5) :=
  Night6836Tree.sound w214 pick214 5 t566 _ (by decide +kernel)
theorem cov214_6 : PA.Covered 6 (OZ.Valid 6 w214.low w214.t w214.y w214.r w214.cap) (P33.root 6) :=
  Night6836Tree.sound w214 pick214 6 t567 _ (by decide +kernel)
theorem cov214_7 : PA.Covered 7 (OZ.Valid 7 w214.low w214.t w214.y w214.r w214.cap) (P33.root 7) :=
  Night6836Tree.sound w214 pick214 7 t568 _ (by decide +kernel)
theorem window214 : P33.WindowCount w214 := by
  apply P33.window_count w214 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov214_1
  · exact cov214_2
  · exact cov214_3
  · exact cov214_4
  · exact cov214_5
  · exact cov214_6
  · exact cov214_7
def w215 : P33.Window := ⟨13,20,7322,7283,244343827483380703,9375,18000,5000000,81920000000⟩
def h215_0 : Height w215 := ⟨9375,18000,by decide +kernel⟩
def h215_1 : Height w215 := ⟨15350,15000,by decide +kernel⟩
def h215_2 : Height w215 := ⟨29909,12000,by decide +kernel⟩
def pick215 (cl : ℕ) : Height w215 := if cl<37 then (h215_0) else (if cl<1002 then (h215_1) else (h215_2))
private theorem k215_1_0 : check w215 pick215 1 t8399 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k215_1_1 : check w215 pick215 1 t2523 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k215_1_2 : check w215 pick215 1 t8400 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w215 pick215 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t8399 t2523 k215_1_0 k215_1_1
private theorem k215_1_3 : check w215 pick215 1 t8410 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k215_1_4 : check w215 pick215 1 t8425 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k215_1_5 : check w215 pick215 1 t8426 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w215 pick215 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t8410 t8425 k215_1_3 k215_1_4
private theorem k215_1_6 : check w215 pick215 1 t8427 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w215 pick215 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t8400 t8426 k215_1_2 k215_1_5
private theorem k215_1_7 : check w215 pick215 1 t8438 ⟨1,7,2,16,1,52,146,179⟩ = true := by decide +kernel
private theorem k215_1_8 : check w215 pick215 1 t8448 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k215_1_9 : check w215 pick215 1 t8449 ⟨1,7,2,16,1,52,146,206⟩ = true := glue w215 pick215 1 ⟨1,7,2,16,1,52,146,206⟩ 3 179 t8438 t8448 k215_1_7 k215_1_8
private theorem k215_1_10 : check w215 pick215 1 t8452 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k215_1_11 : check w215 pick215 1 t8455 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k215_1_12 : check w215 pick215 1 t8456 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w215 pick215 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t8452 t8455 k215_1_10 k215_1_11
private theorem k215_1_13 : check w215 pick215 1 t8457 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w215 pick215 1 ⟨1,7,2,16,1,52,146,450⟩ 3 206 t8449 t8456 k215_1_9 k215_1_12
private theorem k215_1_14 : check w215 pick215 1 t8458 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w215 pick215 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t8427 t8457 k215_1_6 k215_1_13
theorem cov215_1 : PA.Covered 1 (OZ.Valid 1 w215.low w215.t w215.y w215.r w215.cap) (P33.root 1) :=
  Night6836Tree.sound w215 pick215 1 t8458 _ k215_1_14
theorem cov215_2 : PA.Covered 2 (OZ.Valid 2 w215.low w215.t w215.y w215.r w215.cap) (P33.root 2) :=
  Night6836Tree.sound w215 pick215 2 t8398 _ (by decide +kernel)
theorem cov215_3 : PA.Covered 3 (OZ.Valid 3 w215.low w215.t w215.y w215.r w215.cap) (P33.root 3) :=
  Night6836Tree.sound w215 pick215 3 t564 _ (by decide +kernel)
theorem cov215_4 : PA.Covered 4 (OZ.Valid 4 w215.low w215.t w215.y w215.r w215.cap) (P33.root 4) :=
  Night6836Tree.sound w215 pick215 4 t565 _ (by decide +kernel)
theorem cov215_5 : PA.Covered 5 (OZ.Valid 5 w215.low w215.t w215.y w215.r w215.cap) (P33.root 5) :=
  Night6836Tree.sound w215 pick215 5 t566 _ (by decide +kernel)
theorem cov215_6 : PA.Covered 6 (OZ.Valid 6 w215.low w215.t w215.y w215.r w215.cap) (P33.root 6) :=
  Night6836Tree.sound w215 pick215 6 t567 _ (by decide +kernel)
theorem cov215_7 : PA.Covered 7 (OZ.Valid 7 w215.low w215.t w215.y w215.r w215.cap) (P33.root 7) :=
  Night6836Tree.sound w215 pick215 7 t568 _ (by decide +kernel)
theorem window215 : P33.WindowCount w215 := by
  apply P33.window_count w215 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov215_1
  · exact cov215_2
  · exact cov215_3
  · exact cov215_4
  · exact cov215_5
  · exact cov215_6
  · exact cov215_7
def w216 : P33.Window := ⟨13,21,7282,7242,236139295298835842,6981,21000,5000000,81920000000⟩
def h216_0 : Height w216 := ⟨6981,21000,by decide +kernel⟩
def h216_1 : Height w216 := ⟨10957,18000,by decide +kernel⟩
def h216_2 : Height w216 := ⟨17382,15000,by decide +kernel⟩
def h216_3 : Height w216 := ⟨33389,12000,by decide +kernel⟩
def pick216 (cl : ℕ) : Height w216 := if cl<55 then (if cl<2 then (h216_0) else (h216_1)) else (if cl<1021 then (h216_2) else (h216_3))
private theorem k216_1_0 : check w216 pick216 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k216_1_1 : check w216 pick216 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k216_1_2 : check w216 pick216 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w216 pick216 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k216_1_0 k216_1_1
private theorem k216_1_3 : check w216 pick216 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k216_1_4 : check w216 pick216 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k216_1_5 : check w216 pick216 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w216 pick216 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k216_1_3 k216_1_4
private theorem k216_1_6 : check w216 pick216 1 t7382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w216 pick216 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7381 k216_1_2 k216_1_5
private theorem k216_1_7 : check w216 pick216 1 t7356 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k216_1_8 : check w216 pick216 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k216_1_9 : check w216 pick216 1 t7363 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w216 pick216 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7356 t7362 k216_1_7 k216_1_8
private theorem k216_1_10 : check w216 pick216 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k216_1_11 : check w216 pick216 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k216_1_12 : check w216 pick216 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w216 pick216 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k216_1_10 k216_1_11
private theorem k216_1_13 : check w216 pick216 1 t7370 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w216 pick216 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7363 t7369 k216_1_9 k216_1_12
private theorem k216_1_14 : check w216 pick216 1 t8459 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w216 pick216 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7382 t7370 k216_1_6 k216_1_13
theorem cov216_1 : PA.Covered 1 (OZ.Valid 1 w216.low w216.t w216.y w216.r w216.cap) (P33.root 1) :=
  Night6836Tree.sound w216 pick216 1 t8459 _ k216_1_14
theorem cov216_2 : PA.Covered 2 (OZ.Valid 2 w216.low w216.t w216.y w216.r w216.cap) (P33.root 2) :=
  Night6836Tree.sound w216 pick216 2 t7377 _ (by decide +kernel)
theorem cov216_3 : PA.Covered 3 (OZ.Valid 3 w216.low w216.t w216.y w216.r w216.cap) (P33.root 3) :=
  Night6836Tree.sound w216 pick216 3 t564 _ (by decide +kernel)
theorem cov216_4 : PA.Covered 4 (OZ.Valid 4 w216.low w216.t w216.y w216.r w216.cap) (P33.root 4) :=
  Night6836Tree.sound w216 pick216 4 t565 _ (by decide +kernel)
theorem cov216_5 : PA.Covered 5 (OZ.Valid 5 w216.low w216.t w216.y w216.r w216.cap) (P33.root 5) :=
  Night6836Tree.sound w216 pick216 5 t566 _ (by decide +kernel)
theorem cov216_6 : PA.Covered 6 (OZ.Valid 6 w216.low w216.t w216.y w216.r w216.cap) (P33.root 6) :=
  Night6836Tree.sound w216 pick216 6 t567 _ (by decide +kernel)
theorem cov216_7 : PA.Covered 7 (OZ.Valid 7 w216.low w216.t w216.y w216.r w216.cap) (P33.root 7) :=
  Night6836Tree.sound w216 pick216 7 t568 _ (by decide +kernel)
theorem window216 : P33.WindowCount w216 := by
  apply P33.window_count w216 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov216_1
  · exact cov216_2
  · exact cov216_3
  · exact cov216_4
  · exact cov216_5
  · exact cov216_6
  · exact cov216_7
def w217 : P33.Window := ⟨13,22,7241,7201,241682463612563774,8372,21000,5000000,81920000000⟩
def h217_0 : Height w217 := ⟨8372,21000,by decide +kernel⟩
def h217_1 : Height w217 := ⟨12573,18000,by decide +kernel⟩
def h217_2 : Height w217 := ⟨19469,15000,by decide +kernel⟩
def pick217 (cl : ℕ) : Height w217 := if cl<4 then (h217_0) else (if cl<83 then (h217_1) else (h217_2))
private theorem k217_1_0 : check w217 pick217 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k217_1_1 : check w217 pick217 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k217_1_2 : check w217 pick217 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w217 pick217 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k217_1_0 k217_1_1
private theorem k217_1_3 : check w217 pick217 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k217_1_4 : check w217 pick217 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k217_1_5 : check w217 pick217 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w217 pick217 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k217_1_3 k217_1_4
private theorem k217_1_6 : check w217 pick217 1 t7382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w217 pick217 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7381 k217_1_2 k217_1_5
private theorem k217_1_7 : check w217 pick217 1 t7356 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k217_1_8 : check w217 pick217 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k217_1_9 : check w217 pick217 1 t7363 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w217 pick217 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7356 t7362 k217_1_7 k217_1_8
private theorem k217_1_10 : check w217 pick217 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k217_1_11 : check w217 pick217 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k217_1_12 : check w217 pick217 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w217 pick217 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k217_1_10 k217_1_11
private theorem k217_1_13 : check w217 pick217 1 t7370 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w217 pick217 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7363 t7369 k217_1_9 k217_1_12
private theorem k217_1_14 : check w217 pick217 1 t8459 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w217 pick217 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7382 t7370 k217_1_6 k217_1_13
theorem cov217_1 : PA.Covered 1 (OZ.Valid 1 w217.low w217.t w217.y w217.r w217.cap) (P33.root 1) :=
  Night6836Tree.sound w217 pick217 1 t8459 _ k217_1_14
theorem cov217_2 : PA.Covered 2 (OZ.Valid 2 w217.low w217.t w217.y w217.r w217.cap) (P33.root 2) :=
  Night6836Tree.sound w217 pick217 2 t7392 _ (by decide +kernel)
theorem cov217_3 : PA.Covered 3 (OZ.Valid 3 w217.low w217.t w217.y w217.r w217.cap) (P33.root 3) :=
  Night6836Tree.sound w217 pick217 3 t564 _ (by decide +kernel)
theorem cov217_4 : PA.Covered 4 (OZ.Valid 4 w217.low w217.t w217.y w217.r w217.cap) (P33.root 4) :=
  Night6836Tree.sound w217 pick217 4 t565 _ (by decide +kernel)
theorem cov217_5 : PA.Covered 5 (OZ.Valid 5 w217.low w217.t w217.y w217.r w217.cap) (P33.root 5) :=
  Night6836Tree.sound w217 pick217 5 t566 _ (by decide +kernel)
theorem cov217_6 : PA.Covered 6 (OZ.Valid 6 w217.low w217.t w217.y w217.r w217.cap) (P33.root 6) :=
  Night6836Tree.sound w217 pick217 6 t567 _ (by decide +kernel)
theorem cov217_7 : PA.Covered 7 (OZ.Valid 7 w217.low w217.t w217.y w217.r w217.cap) (P33.root 7) :=
  Night6836Tree.sound w217 pick217 7 t568 _ (by decide +kernel)
theorem window217 : P33.WindowCount w217 := by
  apply P33.window_count w217 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov217_1
  · exact cov217_2
  · exact cov217_3
  · exact cov217_4
  · exact cov217_5
  · exact cov217_6
  · exact cov217_7
def w218 : P33.Window := ⟨13,23,7200,6644,239786775586528732,12734,21000,5000000,81920000000⟩
def h218_0 : Height w218 := ⟨12734,21000,by decide +kernel⟩
def h218_1 : Height w218 := ⟨18163,18000,by decide +kernel⟩
def h218_2 : Height w218 := ⟨28057,15000,by decide +kernel⟩
def pick218 (cl : ℕ) : Height w218 := if cl<32 then (h218_0) else (if cl<440 then (h218_1) else (h218_2))
private theorem k218_1_0 : check w218 pick218 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k218_1_1 : check w218 pick218 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k218_1_2 : check w218 pick218 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w218 pick218 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k218_1_0 k218_1_1
private theorem k218_1_3 : check w218 pick218 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k218_1_4 : check w218 pick218 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k218_1_5 : check w218 pick218 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w218 pick218 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k218_1_3 k218_1_4
private theorem k218_1_6 : check w218 pick218 1 t7382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w218 pick218 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7381 k218_1_2 k218_1_5
private theorem k218_1_7 : check w218 pick218 1 t7356 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k218_1_8 : check w218 pick218 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k218_1_9 : check w218 pick218 1 t7363 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w218 pick218 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7356 t7362 k218_1_7 k218_1_8
private theorem k218_1_10 : check w218 pick218 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k218_1_11 : check w218 pick218 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k218_1_12 : check w218 pick218 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w218 pick218 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k218_1_10 k218_1_11
private theorem k218_1_13 : check w218 pick218 1 t7370 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w218 pick218 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7363 t7369 k218_1_9 k218_1_12
private theorem k218_1_14 : check w218 pick218 1 t8459 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w218 pick218 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7382 t7370 k218_1_6 k218_1_13
theorem cov218_1 : PA.Covered 1 (OZ.Valid 1 w218.low w218.t w218.y w218.r w218.cap) (P33.root 1) :=
  Night6836Tree.sound w218 pick218 1 t8459 _ k218_1_14
private theorem k218_2_0 : check w218 pick218 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k218_2_1 : check w218 pick218 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k218_2_2 : check w218 pick218 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w218 pick218 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k218_2_0 k218_2_1
theorem cov218_2 : PA.Covered 2 (OZ.Valid 2 w218.low w218.t w218.y w218.r w218.cap) (P33.root 2) :=
  Night6836Tree.sound w218 pick218 2 t5461 _ k218_2_2
theorem cov218_3 : PA.Covered 3 (OZ.Valid 3 w218.low w218.t w218.y w218.r w218.cap) (P33.root 3) :=
  Night6836Tree.sound w218 pick218 3 t564 _ (by decide +kernel)
theorem cov218_4 : PA.Covered 4 (OZ.Valid 4 w218.low w218.t w218.y w218.r w218.cap) (P33.root 4) :=
  Night6836Tree.sound w218 pick218 4 t565 _ (by decide +kernel)
theorem cov218_5 : PA.Covered 5 (OZ.Valid 5 w218.low w218.t w218.y w218.r w218.cap) (P33.root 5) :=
  Night6836Tree.sound w218 pick218 5 t566 _ (by decide +kernel)
theorem cov218_6 : PA.Covered 6 (OZ.Valid 6 w218.low w218.t w218.y w218.r w218.cap) (P33.root 6) :=
  Night6836Tree.sound w218 pick218 6 t567 _ (by decide +kernel)
theorem cov218_7 : PA.Covered 7 (OZ.Valid 7 w218.low w218.t w218.y w218.r w218.cap) (P33.root 7) :=
  Night6836Tree.sound w218 pick218 7 t568 _ (by decide +kernel)
theorem window218 : P33.WindowCount w218 := by
  apply P33.window_count w218 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov218_1
  · exact cov218_2
  · exact cov218_3
  · exact cov218_4
  · exact cov218_5
  · exact cov218_6
  · exact cov218_7
def w219 : P33.Window := ⟨13,24,5023,4024,191667665230937810,17597,39000,5000000,81920000000⟩
def h219_0 : Height w219 := ⟨17597,39000,by decide +kernel⟩
def h219_1 : Height w219 := ⟨22837,35000,by decide +kernel⟩
def h219_2 : Height w219 := ⟨29806,31000,by decide +kernel⟩
def h219_3 : Height w219 := ⟨40384,27000,by decide +kernel⟩
def pick219 (cl : ℕ) : Height w219 := if cl<32 then (if cl<2 then (h219_0) else (h219_1)) else (if cl<302 then (h219_2) else (h219_3))
private theorem k219_1_0 : check w219 pick219 1 t7005 ⟨1,7,2,16,1,52,1,76⟩ = true := by decide +kernel
private theorem k219_1_1 : check w219 pick219 1 t7032 ⟨1,7,2,16,1,52,77,138⟩ = true := by decide +kernel
private theorem k219_1_2 : check w219 pick219 1 t7033 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w219 pick219 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7005 t7032 k219_1_0 k219_1_1
private theorem k219_1_3 : check w219 pick219 1 t7218 ⟨1,7,2,16,1,52,139,199⟩ = true := by decide +kernel
private theorem k219_1_4 : check w219 pick219 1 t7097 ⟨1,7,2,16,1,52,200,450⟩ = true := by decide +kernel
private theorem k219_1_5 : check w219 pick219 1 t7219 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w219 pick219 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7218 t7097 k219_1_3 k219_1_4
private theorem k219_1_6 : check w219 pick219 1 t8460 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w219 pick219 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7033 t7219 k219_1_2 k219_1_5
theorem cov219_1 : PA.Covered 1 (OZ.Valid 1 w219.low w219.t w219.y w219.r w219.cap) (P33.root 1) :=
  Night6836Tree.sound w219 pick219 1 t8460 _ k219_1_6
theorem cov219_2 : PA.Covered 2 (OZ.Valid 2 w219.low w219.t w219.y w219.r w219.cap) (P33.root 2) :=
  Night6836Tree.sound w219 pick219 2 t5320 _ (by decide +kernel)
theorem cov219_3 : PA.Covered 3 (OZ.Valid 3 w219.low w219.t w219.y w219.r w219.cap) (P33.root 3) :=
  Night6836Tree.sound w219 pick219 3 t564 _ (by decide +kernel)
theorem cov219_4 : PA.Covered 4 (OZ.Valid 4 w219.low w219.t w219.y w219.r w219.cap) (P33.root 4) :=
  Night6836Tree.sound w219 pick219 4 t565 _ (by decide +kernel)
theorem cov219_5 : PA.Covered 5 (OZ.Valid 5 w219.low w219.t w219.y w219.r w219.cap) (P33.root 5) :=
  Night6836Tree.sound w219 pick219 5 t566 _ (by decide +kernel)
theorem cov219_6 : PA.Covered 6 (OZ.Valid 6 w219.low w219.t w219.y w219.r w219.cap) (P33.root 6) :=
  Night6836Tree.sound w219 pick219 6 t567 _ (by decide +kernel)
theorem cov219_7 : PA.Covered 7 (OZ.Valid 7 w219.low w219.t w219.y w219.r w219.cap) (P33.root 7) :=
  Night6836Tree.sound w219 pick219 7 t2134 _ (by decide +kernel)
theorem window219 : P33.WindowCount w219 := by
  apply P33.window_count w219 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov219_1
  · exact cov219_2
  · exact cov219_3
  · exact cov219_4
  · exact cov219_5
  · exact cov219_6
  · exact cov219_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w220 : P33.Window := ⟨13,24,7159,7020,243427378273025480,11784,21000,5000000,81920000000⟩
def h220_0 : Height w220 := ⟨11784,21000,by decide +kernel⟩
def h220_1 : Height w220 := ⟨16640,18000,by decide +kernel⟩
def h220_2 : Height w220 := ⟨24969,15000,by decide +kernel⟩
def pick220 (cl : ℕ) : Height w220 := if cl<12 then (h220_0) else (if cl<213 then (h220_1) else (h220_2))
private theorem k220_1_0 : check w220 pick220 1 t7379 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k220_1_1 : check w220 pick220 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k220_1_2 : check w220 pick220 1 t7380 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w220 pick220 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7379 t7131 k220_1_0 k220_1_1
private theorem k220_1_3 : check w220 pick220 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k220_1_4 : check w220 pick220 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k220_1_5 : check w220 pick220 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w220 pick220 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k220_1_3 k220_1_4
private theorem k220_1_6 : check w220 pick220 1 t7382 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w220 pick220 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7380 t7381 k220_1_2 k220_1_5
private theorem k220_1_7 : check w220 pick220 1 t7386 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k220_1_8 : check w220 pick220 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k220_1_9 : check w220 pick220 1 t7387 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w220 pick220 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7386 t7362 k220_1_7 k220_1_8
private theorem k220_1_10 : check w220 pick220 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k220_1_11 : check w220 pick220 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k220_1_12 : check w220 pick220 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w220 pick220 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k220_1_10 k220_1_11
private theorem k220_1_13 : check w220 pick220 1 t7388 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w220 pick220 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7387 t7369 k220_1_9 k220_1_12
private theorem k220_1_14 : check w220 pick220 1 t7389 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w220 pick220 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7382 t7388 k220_1_6 k220_1_13
theorem cov220_1 : PA.Covered 1 (OZ.Valid 1 w220.low w220.t w220.y w220.r w220.cap) (P33.root 1) :=
  Night6836Tree.sound w220 pick220 1 t7389 _ k220_1_14
private theorem k220_2_0 : check w220 pick220 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k220_2_1 : check w220 pick220 2 t3026 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k220_2_2 : check w220 pick220 2 t5461 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w220 pick220 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t3026 k220_2_0 k220_2_1
theorem cov220_2 : PA.Covered 2 (OZ.Valid 2 w220.low w220.t w220.y w220.r w220.cap) (P33.root 2) :=
  Night6836Tree.sound w220 pick220 2 t5461 _ k220_2_2
theorem cov220_3 : PA.Covered 3 (OZ.Valid 3 w220.low w220.t w220.y w220.r w220.cap) (P33.root 3) :=
  Night6836Tree.sound w220 pick220 3 t564 _ (by decide +kernel)
theorem cov220_4 : PA.Covered 4 (OZ.Valid 4 w220.low w220.t w220.y w220.r w220.cap) (P33.root 4) :=
  Night6836Tree.sound w220 pick220 4 t565 _ (by decide +kernel)
theorem cov220_5 : PA.Covered 5 (OZ.Valid 5 w220.low w220.t w220.y w220.r w220.cap) (P33.root 5) :=
  Night6836Tree.sound w220 pick220 5 t566 _ (by decide +kernel)
theorem cov220_6 : PA.Covered 6 (OZ.Valid 6 w220.low w220.t w220.y w220.r w220.cap) (P33.root 6) :=
  Night6836Tree.sound w220 pick220 6 t567 _ (by decide +kernel)
theorem cov220_7 : PA.Covered 7 (OZ.Valid 7 w220.low w220.t w220.y w220.r w220.cap) (P33.root 7) :=
  Night6836Tree.sound w220 pick220 7 t568 _ (by decide +kernel)
theorem window220 : P33.WindowCount w220 := by
  apply P33.window_count w220 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov220_1
  · exact cov220_2
  · exact cov220_3
  · exact cov220_4
  · exact cov220_5
  · exact cov220_6
  · exact cov220_7
def w221 : P33.Window := ⟨13,25,7115,7068,244470082295150047,12772,21000,5000000,81920000000⟩
def h221_0 : Height w221 := ⟨12772,21000,by decide +kernel⟩
def h221_1 : Height w221 := ⟨17726,18000,by decide +kernel⟩
def h221_2 : Height w221 := ⟨26217,15000,by decide +kernel⟩
def pick221 (cl : ℕ) : Height w221 := if cl<14 then (h221_0) else (if cl<242 then (h221_1) else (h221_2))
private theorem k221_1_0 : check w221 pick221 1 t7124 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k221_1_1 : check w221 pick221 1 t7131 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k221_1_2 : check w221 pick221 1 t7132 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w221 pick221 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7124 t7131 k221_1_0 k221_1_1
private theorem k221_1_3 : check w221 pick221 1 t7154 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k221_1_4 : check w221 pick221 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k221_1_5 : check w221 pick221 1 t7381 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w221 pick221 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7154 t7348 k221_1_3 k221_1_4
private theorem k221_1_6 : check w221 pick221 1 t7455 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w221 pick221 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7132 t7381 k221_1_2 k221_1_5
private theorem k221_1_7 : check w221 pick221 1 t7386 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k221_1_8 : check w221 pick221 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k221_1_9 : check w221 pick221 1 t7387 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w221 pick221 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7386 t7362 k221_1_7 k221_1_8
private theorem k221_1_10 : check w221 pick221 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k221_1_11 : check w221 pick221 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k221_1_12 : check w221 pick221 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w221 pick221 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k221_1_10 k221_1_11
private theorem k221_1_13 : check w221 pick221 1 t7388 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w221 pick221 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7387 t7369 k221_1_9 k221_1_12
private theorem k221_1_14 : check w221 pick221 1 t8461 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w221 pick221 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7455 t7388 k221_1_6 k221_1_13
theorem cov221_1 : PA.Covered 1 (OZ.Valid 1 w221.low w221.t w221.y w221.r w221.cap) (P33.root 1) :=
  Night6836Tree.sound w221 pick221 1 t8461 _ k221_1_14
private theorem k221_2_0 : check w221 pick221 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k221_2_1 : check w221 pick221 2 t8463 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k221_2_2 : check w221 pick221 2 t8464 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w221 pick221 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t8463 k221_2_0 k221_2_1
theorem cov221_2 : PA.Covered 2 (OZ.Valid 2 w221.low w221.t w221.y w221.r w221.cap) (P33.root 2) :=
  Night6836Tree.sound w221 pick221 2 t8464 _ k221_2_2
theorem cov221_3 : PA.Covered 3 (OZ.Valid 3 w221.low w221.t w221.y w221.r w221.cap) (P33.root 3) :=
  Night6836Tree.sound w221 pick221 3 t564 _ (by decide +kernel)
theorem cov221_4 : PA.Covered 4 (OZ.Valid 4 w221.low w221.t w221.y w221.r w221.cap) (P33.root 4) :=
  Night6836Tree.sound w221 pick221 4 t565 _ (by decide +kernel)
theorem cov221_5 : PA.Covered 5 (OZ.Valid 5 w221.low w221.t w221.y w221.r w221.cap) (P33.root 5) :=
  Night6836Tree.sound w221 pick221 5 t566 _ (by decide +kernel)
theorem cov221_6 : PA.Covered 6 (OZ.Valid 6 w221.low w221.t w221.y w221.r w221.cap) (P33.root 6) :=
  Night6836Tree.sound w221 pick221 6 t567 _ (by decide +kernel)
theorem cov221_7 : PA.Covered 7 (OZ.Valid 7 w221.low w221.t w221.y w221.r w221.cap) (P33.root 7) :=
  Night6836Tree.sound w221 pick221 7 t568 _ (by decide +kernel)
theorem window221 : P33.WindowCount w221 := by
  apply P33.window_count w221 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov221_1
  · exact cov221_2
  · exact cov221_3
  · exact cov221_4
  · exact cov221_5
  · exact cov221_6
  · exact cov221_7
def w222 : P33.Window := ⟨13,26,7067,7020,245409908844744860,14327,21000,5000000,81920000000⟩
def h222_0 : Height w222 := ⟨14327,21000,by decide +kernel⟩
def h222_1 : Height w222 := ⟨19562,18000,by decide +kernel⟩
def h222_2 : Height w222 := ⟨28659,15000,by decide +kernel⟩
def pick222 (cl : ℕ) : Height w222 := if cl<32 then (h222_0) else (if cl<287 then (h222_1) else (h222_2))
private theorem k222_1_0 : check w222 pick222 1 t7465 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k222_1_1 : check w222 pick222 1 t7341 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k222_1_2 : check w222 pick222 1 t7967 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w222 pick222 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7465 t7341 k222_1_0 k222_1_1
private theorem k222_1_3 : check w222 pick222 1 t7345 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k222_1_4 : check w222 pick222 1 t7482 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k222_1_5 : check w222 pick222 1 t8465 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w222 pick222 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t7345 t7482 k222_1_3 k222_1_4
private theorem k222_1_6 : check w222 pick222 1 t8466 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w222 pick222 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t7967 t8465 k222_1_2 k222_1_5
private theorem k222_1_7 : check w222 pick222 1 t7489 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k222_1_8 : check w222 pick222 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k222_1_9 : check w222 pick222 1 t7490 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w222 pick222 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7489 t6872 k222_1_7 k222_1_8
private theorem k222_1_10 : check w222 pick222 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k222_1_11 : check w222 pick222 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k222_1_12 : check w222 pick222 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w222 pick222 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k222_1_10 k222_1_11
private theorem k222_1_13 : check w222 pick222 1 t7491 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w222 pick222 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7490 t7190 k222_1_9 k222_1_12
private theorem k222_1_14 : check w222 pick222 1 t8467 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w222 pick222 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8466 t7491 k222_1_6 k222_1_13
theorem cov222_1 : PA.Covered 1 (OZ.Valid 1 w222.low w222.t w222.y w222.r w222.cap) (P33.root 1) :=
  Night6836Tree.sound w222 pick222 1 t8467 _ k222_1_14
private theorem k222_2_0 : check w222 pick222 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k222_2_1 : check w222 pick222 2 t8463 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k222_2_2 : check w222 pick222 2 t8464 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w222 pick222 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t8463 k222_2_0 k222_2_1
theorem cov222_2 : PA.Covered 2 (OZ.Valid 2 w222.low w222.t w222.y w222.r w222.cap) (P33.root 2) :=
  Night6836Tree.sound w222 pick222 2 t8464 _ k222_2_2
theorem cov222_3 : PA.Covered 3 (OZ.Valid 3 w222.low w222.t w222.y w222.r w222.cap) (P33.root 3) :=
  Night6836Tree.sound w222 pick222 3 t564 _ (by decide +kernel)
theorem cov222_4 : PA.Covered 4 (OZ.Valid 4 w222.low w222.t w222.y w222.r w222.cap) (P33.root 4) :=
  Night6836Tree.sound w222 pick222 4 t565 _ (by decide +kernel)
theorem cov222_5 : PA.Covered 5 (OZ.Valid 5 w222.low w222.t w222.y w222.r w222.cap) (P33.root 5) :=
  Night6836Tree.sound w222 pick222 5 t566 _ (by decide +kernel)
theorem cov222_6 : PA.Covered 6 (OZ.Valid 6 w222.low w222.t w222.y w222.r w222.cap) (P33.root 6) :=
  Night6836Tree.sound w222 pick222 6 t567 _ (by decide +kernel)
theorem cov222_7 : PA.Covered 7 (OZ.Valid 7 w222.low w222.t w222.y w222.r w222.cap) (P33.root 7) :=
  Night6836Tree.sound w222 pick222 7 t568 _ (by decide +kernel)
theorem window222 : P33.WindowCount w222 := by
  apply P33.window_count w222 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov222_1
  · exact cov222_2
  · exact cov222_3
  · exact cov222_4
  · exact cov222_5
  · exact cov222_6
  · exact cov222_7
def w223 : P33.Window := ⟨13,27,7019,6644,245115962306845128,14031,24000,5000000,81920000000⟩
def h223_0 : Height w223 := ⟨14031,24000,by decide +kernel⟩
def h223_1 : Height w223 := ⟨18355,21000,by decide +kernel⟩
def h223_2 : Height w223 := ⟨24724,18000,by decide +kernel⟩
def h223_3 : Height w223 := ⟨36609,15000,by decide +kernel⟩
def pick223 (cl : ℕ) : Height w223 := if cl<51 then (if cl<4 then (h223_0) else (h223_1)) else (if cl<922 then (h223_2) else (h223_3))
private theorem k223_1_0 : check w223 pick223 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k223_1_1 : check w223 pick223 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k223_1_2 : check w223 pick223 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w223 pick223 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k223_1_0 k223_1_1
private theorem k223_1_3 : check w223 pick223 1 t8472 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k223_1_4 : check w223 pick223 1 t6792 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k223_1_5 : check w223 pick223 1 t8473 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w223 pick223 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t8472 t6792 k223_1_3 k223_1_4
private theorem k223_1_6 : check w223 pick223 1 t8474 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w223 pick223 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t8473 k223_1_2 k223_1_5
private theorem k223_1_7 : check w223 pick223 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k223_1_8 : check w223 pick223 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k223_1_9 : check w223 pick223 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w223 pick223 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k223_1_7 k223_1_8
private theorem k223_1_10 : check w223 pick223 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k223_1_11 : check w223 pick223 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k223_1_12 : check w223 pick223 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w223 pick223 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k223_1_10 k223_1_11
private theorem k223_1_13 : check w223 pick223 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w223 pick223 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k223_1_9 k223_1_12
private theorem k223_1_14 : check w223 pick223 1 t8475 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w223 pick223 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8474 t7519 k223_1_6 k223_1_13
theorem cov223_1 : PA.Covered 1 (OZ.Valid 1 w223.low w223.t w223.y w223.r w223.cap) (P33.root 1) :=
  Night6836Tree.sound w223 pick223 1 t8475 _ k223_1_14
private theorem k223_2_0 : check w223 pick223 2 t7548 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k223_2_1 : check w223 pick223 2 t8480 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k223_2_2 : check w223 pick223 2 t8481 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w223 pick223 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7548 t8480 k223_2_0 k223_2_1
theorem cov223_2 : PA.Covered 2 (OZ.Valid 2 w223.low w223.t w223.y w223.r w223.cap) (P33.root 2) :=
  Night6836Tree.sound w223 pick223 2 t8481 _ k223_2_2
theorem cov223_3 : PA.Covered 3 (OZ.Valid 3 w223.low w223.t w223.y w223.r w223.cap) (P33.root 3) :=
  Night6836Tree.sound w223 pick223 3 t564 _ (by decide +kernel)
theorem cov223_4 : PA.Covered 4 (OZ.Valid 4 w223.low w223.t w223.y w223.r w223.cap) (P33.root 4) :=
  Night6836Tree.sound w223 pick223 4 t565 _ (by decide +kernel)
theorem cov223_5 : PA.Covered 5 (OZ.Valid 5 w223.low w223.t w223.y w223.r w223.cap) (P33.root 5) :=
  Night6836Tree.sound w223 pick223 5 t566 _ (by decide +kernel)
theorem cov223_6 : PA.Covered 6 (OZ.Valid 6 w223.low w223.t w223.y w223.r w223.cap) (P33.root 6) :=
  Night6836Tree.sound w223 pick223 6 t567 _ (by decide +kernel)
theorem cov223_7 : PA.Covered 7 (OZ.Valid 7 w223.low w223.t w223.y w223.r w223.cap) (P33.root 7) :=
  Night6836Tree.sound w223 pick223 7 t568 _ (by decide +kernel)
theorem window223 : P33.WindowCount w223 := by
  apply P33.window_count w223 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov223_1
  · exact cov223_2
  · exact cov223_3
  · exact cov223_4
  · exact cov223_5
  · exact cov223_6
  · exact cov223_7
def w224 : P33.Window := ⟨13,28,6969,6921,245411635032223978,13507,24000,5000000,81920000000⟩
def h224_0 : Height w224 := ⟨13507,24000,by decide +kernel⟩
def h224_1 : Height w224 := ⟨17575,21000,by decide +kernel⟩
def h224_2 : Height w224 := ⟨23420,18000,by decide +kernel⟩
def h224_3 : Height w224 := ⟨33852,15000,by decide +kernel⟩
def pick224 (cl : ℕ) : Height w224 := if cl<36 then (if cl<2 then (h224_0) else (h224_1)) else (if cl<673 then (h224_2) else (h224_3))
private theorem k224_1_0 : check w224 pick224 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k224_1_1 : check w224 pick224 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k224_1_2 : check w224 pick224 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w224 pick224 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k224_1_0 k224_1_1
private theorem k224_1_3 : check w224 pick224 1 t7526 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k224_1_4 : check w224 pick224 1 t7529 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k224_1_5 : check w224 pick224 1 t7530 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w224 pick224 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t7526 t7529 k224_1_3 k224_1_4
private theorem k224_1_6 : check w224 pick224 1 t7531 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w224 pick224 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t7530 k224_1_2 k224_1_5
private theorem k224_1_7 : check w224 pick224 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k224_1_8 : check w224 pick224 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k224_1_9 : check w224 pick224 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w224 pick224 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k224_1_7 k224_1_8
private theorem k224_1_10 : check w224 pick224 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k224_1_11 : check w224 pick224 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k224_1_12 : check w224 pick224 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w224 pick224 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k224_1_10 k224_1_11
private theorem k224_1_13 : check w224 pick224 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w224 pick224 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k224_1_9 k224_1_12
private theorem k224_1_14 : check w224 pick224 1 t7532 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w224 pick224 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t7531 t7519 k224_1_6 k224_1_13
theorem cov224_1 : PA.Covered 1 (OZ.Valid 1 w224.low w224.t w224.y w224.r w224.cap) (P33.root 1) :=
  Night6836Tree.sound w224 pick224 1 t7532 _ k224_1_14
private theorem k224_2_0 : check w224 pick224 2 t7548 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k224_2_1 : check w224 pick224 2 t8495 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k224_2_2 : check w224 pick224 2 t8496 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w224 pick224 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7548 t8495 k224_2_0 k224_2_1
theorem cov224_2 : PA.Covered 2 (OZ.Valid 2 w224.low w224.t w224.y w224.r w224.cap) (P33.root 2) :=
  Night6836Tree.sound w224 pick224 2 t8496 _ k224_2_2
theorem cov224_3 : PA.Covered 3 (OZ.Valid 3 w224.low w224.t w224.y w224.r w224.cap) (P33.root 3) :=
  Night6836Tree.sound w224 pick224 3 t564 _ (by decide +kernel)
theorem cov224_4 : PA.Covered 4 (OZ.Valid 4 w224.low w224.t w224.y w224.r w224.cap) (P33.root 4) :=
  Night6836Tree.sound w224 pick224 4 t565 _ (by decide +kernel)
theorem cov224_5 : PA.Covered 5 (OZ.Valid 5 w224.low w224.t w224.y w224.r w224.cap) (P33.root 5) :=
  Night6836Tree.sound w224 pick224 5 t566 _ (by decide +kernel)
theorem cov224_6 : PA.Covered 6 (OZ.Valid 6 w224.low w224.t w224.y w224.r w224.cap) (P33.root 6) :=
  Night6836Tree.sound w224 pick224 6 t567 _ (by decide +kernel)
theorem cov224_7 : PA.Covered 7 (OZ.Valid 7 w224.low w224.t w224.y w224.r w224.cap) (P33.root 7) :=
  Night6836Tree.sound w224 pick224 7 t568 _ (by decide +kernel)
theorem window224 : P33.WindowCount w224 := by
  apply P33.window_count w224 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov224_1
  · exact cov224_2
  · exact cov224_3
  · exact cov224_4
  · exact cov224_5
  · exact cov224_6
  · exact cov224_7
def w225 : P33.Window := ⟨13,29,6920,6758,242281605768701631,15764,24000,5000000,81920000000⟩
def h225_0 : Height w225 := ⟨15764,24000,by decide +kernel⟩
def h225_1 : Height w225 := ⟨20181,21000,by decide +kernel⟩
def h225_2 : Height w225 := ⟨26669,18000,by decide +kernel⟩
def h225_3 : Height w225 := ⟨38632,15000,by decide +kernel⟩
def pick225 (cl : ℕ) : Height w225 := if cl<62 then (if cl<5 then (h225_0) else (h225_1)) else (if cl<922 then (h225_2) else (h225_3))
private theorem k225_1_0 : check w225 pick225 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k225_1_1 : check w225 pick225 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k225_1_2 : check w225 pick225 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w225 pick225 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k225_1_0 k225_1_1
private theorem k225_1_3 : check w225 pick225 1 t8472 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k225_1_4 : check w225 pick225 1 t6792 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k225_1_5 : check w225 pick225 1 t8473 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w225 pick225 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t8472 t6792 k225_1_3 k225_1_4
private theorem k225_1_6 : check w225 pick225 1 t8474 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w225 pick225 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t8473 k225_1_2 k225_1_5
private theorem k225_1_7 : check w225 pick225 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k225_1_8 : check w225 pick225 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k225_1_9 : check w225 pick225 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w225 pick225 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k225_1_7 k225_1_8
private theorem k225_1_10 : check w225 pick225 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k225_1_11 : check w225 pick225 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k225_1_12 : check w225 pick225 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w225 pick225 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k225_1_10 k225_1_11
private theorem k225_1_13 : check w225 pick225 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w225 pick225 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k225_1_9 k225_1_12
private theorem k225_1_14 : check w225 pick225 1 t8475 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w225 pick225 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8474 t7519 k225_1_6 k225_1_13
theorem cov225_1 : PA.Covered 1 (OZ.Valid 1 w225.low w225.t w225.y w225.r w225.cap) (P33.root 1) :=
  Night6836Tree.sound w225 pick225 1 t8475 _ k225_1_14
private theorem k225_2_0 : check w225 pick225 2 t7595 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k225_2_1 : check w225 pick225 2 t5624 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k225_2_2 : check w225 pick225 2 t7596 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w225 pick225 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7595 t5624 k225_2_0 k225_2_1
theorem cov225_2 : PA.Covered 2 (OZ.Valid 2 w225.low w225.t w225.y w225.r w225.cap) (P33.root 2) :=
  Night6836Tree.sound w225 pick225 2 t7596 _ k225_2_2
theorem cov225_3 : PA.Covered 3 (OZ.Valid 3 w225.low w225.t w225.y w225.r w225.cap) (P33.root 3) :=
  Night6836Tree.sound w225 pick225 3 t564 _ (by decide +kernel)
theorem cov225_4 : PA.Covered 4 (OZ.Valid 4 w225.low w225.t w225.y w225.r w225.cap) (P33.root 4) :=
  Night6836Tree.sound w225 pick225 4 t565 _ (by decide +kernel)
theorem cov225_5 : PA.Covered 5 (OZ.Valid 5 w225.low w225.t w225.y w225.r w225.cap) (P33.root 5) :=
  Night6836Tree.sound w225 pick225 5 t566 _ (by decide +kernel)
theorem cov225_6 : PA.Covered 6 (OZ.Valid 6 w225.low w225.t w225.y w225.r w225.cap) (P33.root 6) :=
  Night6836Tree.sound w225 pick225 6 t567 _ (by decide +kernel)
theorem cov225_7 : PA.Covered 7 (OZ.Valid 7 w225.low w225.t w225.y w225.r w225.cap) (P33.root 7) :=
  Night6836Tree.sound w225 pick225 7 t568 _ (by decide +kernel)
theorem window225 : P33.WindowCount w225 := by
  apply P33.window_count w225 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov225_1
  · exact cov225_2
  · exact cov225_3
  · exact cov225_4
  · exact cov225_5
  · exact cov225_6
  · exact cov225_7
def w226 : P33.Window := ⟨13,30,6869,6818,244890186333423074,16574,24000,5000000,81920000000⟩
def h226_0 : Height w226 := ⟨16574,24000,by decide +kernel⟩
def h226_1 : Height w226 := ⟨21027,21000,by decide +kernel⟩
def h226_2 : Height w226 := ⟨27555,18000,by decide +kernel⟩
def h226_3 : Height w226 := ⟨39519,15000,by decide +kernel⟩
def pick226 (cl : ℕ) : Height w226 := if cl<62 then (if cl<5 then (h226_0) else (h226_1)) else (if cl<922 then (h226_2) else (h226_3))
private theorem k226_1_0 : check w226 pick226 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k226_1_1 : check w226 pick226 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k226_1_2 : check w226 pick226 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w226 pick226 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k226_1_0 k226_1_1
private theorem k226_1_3 : check w226 pick226 1 t8472 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k226_1_4 : check w226 pick226 1 t6792 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k226_1_5 : check w226 pick226 1 t8473 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w226 pick226 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t8472 t6792 k226_1_3 k226_1_4
private theorem k226_1_6 : check w226 pick226 1 t8474 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w226 pick226 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t8473 k226_1_2 k226_1_5
private theorem k226_1_7 : check w226 pick226 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k226_1_8 : check w226 pick226 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k226_1_9 : check w226 pick226 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w226 pick226 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k226_1_7 k226_1_8
private theorem k226_1_10 : check w226 pick226 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k226_1_11 : check w226 pick226 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k226_1_12 : check w226 pick226 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w226 pick226 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k226_1_10 k226_1_11
private theorem k226_1_13 : check w226 pick226 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w226 pick226 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k226_1_9 k226_1_12
private theorem k226_1_14 : check w226 pick226 1 t8475 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w226 pick226 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8474 t7519 k226_1_6 k226_1_13
theorem cov226_1 : PA.Covered 1 (OZ.Valid 1 w226.low w226.t w226.y w226.r w226.cap) (P33.root 1) :=
  Night6836Tree.sound w226 pick226 1 t8475 _ k226_1_14
private theorem k226_2_0 : check w226 pick226 2 t7595 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k226_2_1 : check w226 pick226 2 t5624 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k226_2_2 : check w226 pick226 2 t7596 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w226 pick226 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t7595 t5624 k226_2_0 k226_2_1
theorem cov226_2 : PA.Covered 2 (OZ.Valid 2 w226.low w226.t w226.y w226.r w226.cap) (P33.root 2) :=
  Night6836Tree.sound w226 pick226 2 t7596 _ k226_2_2
theorem cov226_3 : PA.Covered 3 (OZ.Valid 3 w226.low w226.t w226.y w226.r w226.cap) (P33.root 3) :=
  Night6836Tree.sound w226 pick226 3 t564 _ (by decide +kernel)
theorem cov226_4 : PA.Covered 4 (OZ.Valid 4 w226.low w226.t w226.y w226.r w226.cap) (P33.root 4) :=
  Night6836Tree.sound w226 pick226 4 t565 _ (by decide +kernel)
theorem cov226_5 : PA.Covered 5 (OZ.Valid 5 w226.low w226.t w226.y w226.r w226.cap) (P33.root 5) :=
  Night6836Tree.sound w226 pick226 5 t566 _ (by decide +kernel)
theorem cov226_6 : PA.Covered 6 (OZ.Valid 6 w226.low w226.t w226.y w226.r w226.cap) (P33.root 6) :=
  Night6836Tree.sound w226 pick226 6 t567 _ (by decide +kernel)
theorem cov226_7 : PA.Covered 7 (OZ.Valid 7 w226.low w226.t w226.y w226.r w226.cap) (P33.root 7) :=
  Night6836Tree.sound w226 pick226 7 t568 _ (by decide +kernel)
theorem window226 : P33.WindowCount w226 := by
  apply P33.window_count w226 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov226_1
  · exact cov226_2
  · exact cov226_3
  · exact cov226_4
  · exact cov226_5
  · exact cov226_6
  · exact cov226_7
def w227 : P33.Window := ⟨13,31,6817,6758,246383932412121478,18228,24000,5000000,81920000000⟩
def h227_0 : Height w227 := ⟨18228,24000,by decide +kernel⟩
def h227_1 : Height w227 := ⟨22901,21000,by decide +kernel⟩
def h227_2 : Height w227 := ⟨29826,18000,by decide +kernel⟩
def h227_3 : Height w227 := ⟨42698,15000,by decide +kernel⟩
def pick227 (cl : ℕ) : Height w227 := if cl<92 then (if cl<6 then (h227_0) else (h227_1)) else (if cl<961 then (h227_2) else (h227_3))
private theorem k227_1_0 : check w227 pick227 1 t7551 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k227_1_1 : check w227 pick227 1 t7555 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k227_1_2 : check w227 pick227 1 t7556 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w227 pick227 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7551 t7555 k227_1_0 k227_1_1
private theorem k227_1_3 : check w227 pick227 1 t8499 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k227_1_4 : check w227 pick227 1 t7482 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k227_1_5 : check w227 pick227 1 t8500 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w227 pick227 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t8499 t7482 k227_1_3 k227_1_4
private theorem k227_1_6 : check w227 pick227 1 t8501 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w227 pick227 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7556 t8500 k227_1_2 k227_1_5
private theorem k227_1_7 : check w227 pick227 1 t7565 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k227_1_8 : check w227 pick227 1 t8505 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k227_1_9 : check w227 pick227 1 t8506 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w227 pick227 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7565 t8505 k227_1_7 k227_1_8
private theorem k227_1_10 : check w227 pick227 1 t7585 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k227_1_11 : check w227 pick227 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k227_1_12 : check w227 pick227 1 t7591 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w227 pick227 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7585 t7590 k227_1_10 k227_1_11
private theorem k227_1_13 : check w227 pick227 1 t8507 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w227 pick227 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t8506 t7591 k227_1_9 k227_1_12
private theorem k227_1_14 : check w227 pick227 1 t8508 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w227 pick227 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8501 t8507 k227_1_6 k227_1_13
theorem cov227_1 : PA.Covered 1 (OZ.Valid 1 w227.low w227.t w227.y w227.r w227.cap) (P33.root 1) :=
  Night6836Tree.sound w227 pick227 1 t8508 _ k227_1_14
private theorem k227_2_0 : check w227 pick227 2 t8510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k227_2_1 : check w227 pick227 2 t8516 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k227_2_2 : check w227 pick227 2 t8517 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w227 pick227 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t8510 t8516 k227_2_0 k227_2_1
theorem cov227_2 : PA.Covered 2 (OZ.Valid 2 w227.low w227.t w227.y w227.r w227.cap) (P33.root 2) :=
  Night6836Tree.sound w227 pick227 2 t8517 _ k227_2_2
theorem cov227_3 : PA.Covered 3 (OZ.Valid 3 w227.low w227.t w227.y w227.r w227.cap) (P33.root 3) :=
  Night6836Tree.sound w227 pick227 3 t564 _ (by decide +kernel)
theorem cov227_4 : PA.Covered 4 (OZ.Valid 4 w227.low w227.t w227.y w227.r w227.cap) (P33.root 4) :=
  Night6836Tree.sound w227 pick227 4 t565 _ (by decide +kernel)
theorem cov227_5 : PA.Covered 5 (OZ.Valid 5 w227.low w227.t w227.y w227.r w227.cap) (P33.root 5) :=
  Night6836Tree.sound w227 pick227 5 t566 _ (by decide +kernel)
theorem cov227_6 : PA.Covered 6 (OZ.Valid 6 w227.low w227.t w227.y w227.r w227.cap) (P33.root 6) :=
  Night6836Tree.sound w227 pick227 6 t567 _ (by decide +kernel)
theorem cov227_7 : PA.Covered 7 (OZ.Valid 7 w227.low w227.t w227.y w227.r w227.cap) (P33.root 7) :=
  Night6836Tree.sound w227 pick227 7 t568 _ (by decide +kernel)
theorem window227 : P33.WindowCount w227 := by
  apply P33.window_count w227 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov227_1
  · exact cov227_2
  · exact cov227_3
  · exact cov227_4
  · exact cov227_5
  · exact cov227_6
  · exact cov227_7
def w228 : P33.Window := ⟨13,32,6253,5304,241844732145374216,25595,30000,5000000,81920000000⟩
def h228_0 : Height w228 := ⟨25595,30000,by decide +kernel⟩
def h228_1 : Height w228 := ⟨30441,27000,by decide +kernel⟩
def h228_2 : Height w228 := ⟨36978,24000,by decide +kernel⟩
def h228_3 : Height w228 := ⟨46917,21000,by decide +kernel⟩
def pick228 (cl : ℕ) : Height w228 := if cl<62 then (if cl<12 then (h228_0) else (h228_1)) else (if cl<458 then (h228_2) else (h228_3))
private theorem k228_1_0 : check w228 pick228 1 t6686 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k228_1_1 : check w228 pick228 1 t6707 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k228_1_2 : check w228 pick228 1 t6708 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w228 pick228 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t6686 t6707 k228_1_0 k228_1_1
private theorem k228_1_3 : check w228 pick228 1 t7506 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k228_1_4 : check w228 pick228 1 t7510 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k228_1_5 : check w228 pick228 1 t7511 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w228 pick228 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t7506 t7510 k228_1_3 k228_1_4
private theorem k228_1_6 : check w228 pick228 1 t7512 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w228 pick228 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t6708 t7511 k228_1_2 k228_1_5
private theorem k228_1_7 : check w228 pick228 1 t7517 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k228_1_8 : check w228 pick228 1 t6872 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k228_1_9 : check w228 pick228 1 t7518 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w228 pick228 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t7517 t6872 k228_1_7 k228_1_8
private theorem k228_1_10 : check w228 pick228 1 t7182 ⟨1,7,2,16,1,52,193,226⟩ = true := by decide +kernel
private theorem k228_1_11 : check w228 pick228 1 t7189 ⟨1,7,2,16,1,52,227,450⟩ = true := by decide +kernel
private theorem k228_1_12 : check w228 pick228 1 t7190 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w228 pick228 1 ⟨1,7,2,16,1,52,193,450⟩ 3 226 t7182 t7189 k228_1_10 k228_1_11
private theorem k228_1_13 : check w228 pick228 1 t7519 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w228 pick228 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t7518 t7190 k228_1_9 k228_1_12
private theorem k228_1_14 : check w228 pick228 1 t7520 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w228 pick228 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t7512 t7519 k228_1_6 k228_1_13
theorem cov228_1 : PA.Covered 1 (OZ.Valid 1 w228.low w228.t w228.y w228.r w228.cap) (P33.root 1) :=
  Night6836Tree.sound w228 pick228 1 t7520 _ k228_1_14
private theorem k228_2_0 : check w228 pick228 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k228_2_1 : check w228 pick228 2 t5541 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k228_2_2 : check w228 pick228 2 t5542 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w228 pick228 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t5541 k228_2_0 k228_2_1
theorem cov228_2 : PA.Covered 2 (OZ.Valid 2 w228.low w228.t w228.y w228.r w228.cap) (P33.root 2) :=
  Night6836Tree.sound w228 pick228 2 t5542 _ k228_2_2
theorem cov228_3 : PA.Covered 3 (OZ.Valid 3 w228.low w228.t w228.y w228.r w228.cap) (P33.root 3) :=
  Night6836Tree.sound w228 pick228 3 t564 _ (by decide +kernel)
theorem cov228_4 : PA.Covered 4 (OZ.Valid 4 w228.low w228.t w228.y w228.r w228.cap) (P33.root 4) :=
  Night6836Tree.sound w228 pick228 4 t565 _ (by decide +kernel)
theorem cov228_5 : PA.Covered 5 (OZ.Valid 5 w228.low w228.t w228.y w228.r w228.cap) (P33.root 5) :=
  Night6836Tree.sound w228 pick228 5 t566 _ (by decide +kernel)
theorem cov228_6 : PA.Covered 6 (OZ.Valid 6 w228.low w228.t w228.y w228.r w228.cap) (P33.root 6) :=
  Night6836Tree.sound w228 pick228 6 t567 _ (by decide +kernel)
theorem cov228_7 : PA.Covered 7 (OZ.Valid 7 w228.low w228.t w228.y w228.r w228.cap) (P33.root 7) :=
  Night6836Tree.sound w228 pick228 7 t2134 _ (by decide +kernel)
theorem window228 : P33.WindowCount w228 := by
  apply P33.window_count w228 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov228_1
  · exact cov228_2
  · exact cov228_3
  · exact cov228_4
  · exact cov228_5
  · exact cov228_6
  · exact cov228_7
def w229 : P33.Window := ⟨13,32,6757,6254,245820137173018773,19623,27000,5000000,81920000000⟩
def h229_0 : Height w229 := ⟨19623,27000,by decide +kernel⟩
def h229_1 : Height w229 := ⟨23917,24000,by decide +kernel⟩
def h229_2 : Height w229 := ⟨29778,21000,by decide +kernel⟩
def h229_3 : Height w229 := ⟨39035,18000,by decide +kernel⟩
def h229_4 : Height w229 := ⟨58122,15000,by decide +kernel⟩
def pick229 (cl : ℕ) : Height w229 := if cl<36 then (if cl<4 then (h229_0) else (h229_1)) else (if cl<302 then (h229_2) else (if cl<1026 then (h229_3) else (h229_4)))
private theorem k229_1_0 : check w229 pick229 1 t8519 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k229_1_1 : check w229 pick229 1 t8521 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k229_1_2 : check w229 pick229 1 t8522 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w229 pick229 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t8519 t8521 k229_1_0 k229_1_1
private theorem k229_1_3 : check w229 pick229 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k229_1_4 : check w229 pick229 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k229_1_5 : check w229 pick229 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w229 pick229 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k229_1_3 k229_1_4
private theorem k229_1_6 : check w229 pick229 1 t8523 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w229 pick229 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t8522 t7672 k229_1_2 k229_1_5
private theorem k229_1_7 : check w229 pick229 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k229_1_8 : check w229 pick229 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k229_1_9 : check w229 pick229 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w229 pick229 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k229_1_7 k229_1_8
private theorem k229_1_10 : check w229 pick229 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k229_1_11 : check w229 pick229 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k229_1_12 : check w229 pick229 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w229 pick229 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k229_1_10 k229_1_11
private theorem k229_1_13 : check w229 pick229 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w229 pick229 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k229_1_9 k229_1_12
private theorem k229_1_14 : check w229 pick229 1 t8524 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w229 pick229 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8523 t7649 k229_1_6 k229_1_13
theorem cov229_1 : PA.Covered 1 (OZ.Valid 1 w229.low w229.t w229.y w229.r w229.cap) (P33.root 1) :=
  Night6836Tree.sound w229 pick229 1 t8524 _ k229_1_14
private theorem k229_2_0 : check w229 pick229 2 t8541 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k229_2_1 : check w229 pick229 2 t8516 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k229_2_2 : check w229 pick229 2 t8542 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w229 pick229 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t8541 t8516 k229_2_0 k229_2_1
theorem cov229_2 : PA.Covered 2 (OZ.Valid 2 w229.low w229.t w229.y w229.r w229.cap) (P33.root 2) :=
  Night6836Tree.sound w229 pick229 2 t8542 _ k229_2_2
theorem cov229_3 : PA.Covered 3 (OZ.Valid 3 w229.low w229.t w229.y w229.r w229.cap) (P33.root 3) :=
  Night6836Tree.sound w229 pick229 3 t564 _ (by decide +kernel)
theorem cov229_4 : PA.Covered 4 (OZ.Valid 4 w229.low w229.t w229.y w229.r w229.cap) (P33.root 4) :=
  Night6836Tree.sound w229 pick229 4 t565 _ (by decide +kernel)
theorem cov229_5 : PA.Covered 5 (OZ.Valid 5 w229.low w229.t w229.y w229.r w229.cap) (P33.root 5) :=
  Night6836Tree.sound w229 pick229 5 t566 _ (by decide +kernel)
theorem cov229_6 : PA.Covered 6 (OZ.Valid 6 w229.low w229.t w229.y w229.r w229.cap) (P33.root 6) :=
  Night6836Tree.sound w229 pick229 6 t567 _ (by decide +kernel)
theorem cov229_7 : PA.Covered 7 (OZ.Valid 7 w229.low w229.t w229.y w229.r w229.cap) (P33.root 7) :=
  Night6836Tree.sound w229 pick229 7 t568 _ (by decide +kernel)
theorem window229 : P33.WindowCount w229 := by
  apply P33.window_count w229 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov229_1
  · exact cov229_2
  · exact cov229_3
  · exact cov229_4
  · exact cov229_5
  · exact cov229_6
  · exact cov229_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w230 : P33.Window := ⟨13,33,4732,3733,203828379817705205,32820,47000,5000000,81920000000⟩
def h230_0 : Height w230 := ⟨32820,47000,by decide +kernel⟩
def h230_1 : Height w230 := ⟨38050,43000,by decide +kernel⟩
def h230_2 : Height w230 := ⟨44464,39000,by decide +kernel⟩
def h230_3 : Height w230 := ⟨52858,35000,by decide +kernel⟩
def h230_4 : Height w230 := ⟨64939,31000,by decide +kernel⟩
def h230_5 : Height w230 := ⟨85140,27000,by decide +kernel⟩
def pick230 (cl : ℕ) : Height w230 := if cl<48 then (if cl<2 then (h230_0) else (if cl<10 then (h230_1) else (h230_2))) else (if cl<284 then (h230_3) else (if cl<1004 then (h230_4) else (h230_5)))
private theorem k230_1_0 : check w230 pick230 1 t7338 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k230_1_1 : check w230 pick230 1 t8545 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k230_1_2 : check w230 pick230 1 t8546 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w230 pick230 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t7338 t8545 k230_1_0 k230_1_1
private theorem k230_1_3 : check w230 pick230 1 t8556 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k230_1_4 : check w230 pick230 1 t8563 ⟨1,7,2,16,1,52,111,131⟩ = true := by decide +kernel
private theorem k230_1_5 : check w230 pick230 1 t8564 ⟨1,7,2,16,1,52,84,131⟩ = true := glue w230 pick230 1 ⟨1,7,2,16,1,52,84,131⟩ 3 110 t8556 t8563 k230_1_3 k230_1_4
private theorem k230_1_6 : check w230 pick230 1 t8565 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w230 pick230 1 ⟨1,7,2,16,1,52,1,131⟩ 3 83 t8546 t8564 k230_1_2 k230_1_5
private theorem k230_1_7 : check w230 pick230 1 t8569 ⟨1,7,2,16,1,20,132,192⟩ = true := by decide +kernel
private theorem k230_1_8 : check w230 pick230 1 t8570 ⟨1,7,2,16,21,52,132,192⟩ = true := by decide +kernel
private theorem k230_1_9 : check w230 pick230 1 t8571 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w230 pick230 1 ⟨1,7,2,16,1,52,132,192⟩ 2 20 t8569 t8570 k230_1_7 k230_1_8
private theorem k230_1_10 : check w230 pick230 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k230_1_11 : check w230 pick230 1 t8573 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k230_1_12 : check w230 pick230 1 t8574 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w230 pick230 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t8573 k230_1_10 k230_1_11
private theorem k230_1_13 : check w230 pick230 1 t8575 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w230 pick230 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t8571 t8574 k230_1_9 k230_1_12
private theorem k230_1_14 : check w230 pick230 1 t8576 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w230 pick230 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t8565 t8575 k230_1_6 k230_1_13
theorem cov230_1 : PA.Covered 1 (OZ.Valid 1 w230.low w230.t w230.y w230.r w230.cap) (P33.root 1) :=
  Night6836Tree.sound w230 pick230 1 t8576 _ k230_1_14
private theorem k230_2_0 : check w230 pick230 2 t5510 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k230_2_1 : check w230 pick230 2 t3303 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k230_2_2 : check w230 pick230 2 t5528 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w230 pick230 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t5510 t3303 k230_2_0 k230_2_1
theorem cov230_2 : PA.Covered 2 (OZ.Valid 2 w230.low w230.t w230.y w230.r w230.cap) (P33.root 2) :=
  Night6836Tree.sound w230 pick230 2 t5528 _ k230_2_2
theorem cov230_3 : PA.Covered 3 (OZ.Valid 3 w230.low w230.t w230.y w230.r w230.cap) (P33.root 3) :=
  Night6836Tree.sound w230 pick230 3 t564 _ (by decide +kernel)
theorem cov230_4 : PA.Covered 4 (OZ.Valid 4 w230.low w230.t w230.y w230.r w230.cap) (P33.root 4) :=
  Night6836Tree.sound w230 pick230 4 t565 _ (by decide +kernel)
theorem cov230_5 : PA.Covered 5 (OZ.Valid 5 w230.low w230.t w230.y w230.r w230.cap) (P33.root 5) :=
  Night6836Tree.sound w230 pick230 5 t566 _ (by decide +kernel)
theorem cov230_6 : PA.Covered 6 (OZ.Valid 6 w230.low w230.t w230.y w230.r w230.cap) (P33.root 6) :=
  Night6836Tree.sound w230 pick230 6 t567 _ (by decide +kernel)
theorem cov230_7 : PA.Covered 7 (OZ.Valid 7 w230.low w230.t w230.y w230.r w230.cap) (P33.root 7) :=
  Night6836Tree.sound w230 pick230 7 t2134 _ (by decide +kernel)
theorem window230 : P33.WindowCount w230 := by
  apply P33.window_count w230 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov230_1
  · exact cov230_2
  · exact cov230_3
  · exact cov230_4
  · exact cov230_5
  · exact cov230_6
  · exact cov230_7
def w231 : P33.Window := ⟨13,33,6697,6635,246492458327028125,21712,24000,5000000,81920000000⟩
def h231_0 : Height w231 := ⟨21712,24000,by decide +kernel⟩
def h231_1 : Height w231 := ⟨26870,21000,by decide +kernel⟩
def h231_2 : Height w231 := ⟨34675,18000,by decide +kernel⟩
def h231_3 : Height w231 := ⟨49605,15000,by decide +kernel⟩
def pick231 (cl : ℕ) : Height w231 := if cl<159 then (if cl<18 then (h231_0) else (h231_1)) else (if cl<1002 then (h231_2) else (h231_3))
private theorem k231_1_0 : check w231 pick231 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k231_1_1 : check w231 pick231 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k231_1_2 : check w231 pick231 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w231 pick231 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k231_1_0 k231_1_1
private theorem k231_1_3 : check w231 pick231 1 t8580 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k231_1_4 : check w231 pick231 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k231_1_5 : check w231 pick231 1 t8581 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w231 pick231 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t8580 t7623 k231_1_3 k231_1_4
private theorem k231_1_6 : check w231 pick231 1 t8582 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w231 pick231 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t8581 k231_1_2 k231_1_5
private theorem k231_1_7 : check w231 pick231 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k231_1_8 : check w231 pick231 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k231_1_9 : check w231 pick231 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w231 pick231 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k231_1_7 k231_1_8
private theorem k231_1_10 : check w231 pick231 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k231_1_11 : check w231 pick231 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k231_1_12 : check w231 pick231 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w231 pick231 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k231_1_10 k231_1_11
private theorem k231_1_13 : check w231 pick231 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w231 pick231 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k231_1_9 k231_1_12
private theorem k231_1_14 : check w231 pick231 1 t8583 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w231 pick231 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8582 t7649 k231_1_6 k231_1_13
theorem cov231_1 : PA.Covered 1 (OZ.Valid 1 w231.low w231.t w231.y w231.r w231.cap) (P33.root 1) :=
  Night6836Tree.sound w231 pick231 1 t8583 _ k231_1_14
private theorem k231_2_0 : check w231 pick231 2 t8587 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k231_2_1 : check w231 pick231 2 t8591 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k231_2_2 : check w231 pick231 2 t8592 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w231 pick231 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t8587 t8591 k231_2_0 k231_2_1
private theorem k231_2_3 : check w231 pick231 2 t8595 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k231_2_4 : check w231 pick231 2 t8596 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w231 pick231 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t8592 t8595 k231_2_2 k231_2_3
theorem cov231_2 : PA.Covered 2 (OZ.Valid 2 w231.low w231.t w231.y w231.r w231.cap) (P33.root 2) :=
  Night6836Tree.sound w231 pick231 2 t8596 _ k231_2_4
theorem cov231_3 : PA.Covered 3 (OZ.Valid 3 w231.low w231.t w231.y w231.r w231.cap) (P33.root 3) :=
  Night6836Tree.sound w231 pick231 3 t564 _ (by decide +kernel)
theorem cov231_4 : PA.Covered 4 (OZ.Valid 4 w231.low w231.t w231.y w231.r w231.cap) (P33.root 4) :=
  Night6836Tree.sound w231 pick231 4 t565 _ (by decide +kernel)
theorem cov231_5 : PA.Covered 5 (OZ.Valid 5 w231.low w231.t w231.y w231.r w231.cap) (P33.root 5) :=
  Night6836Tree.sound w231 pick231 5 t566 _ (by decide +kernel)
theorem cov231_6 : PA.Covered 6 (OZ.Valid 6 w231.low w231.t w231.y w231.r w231.cap) (P33.root 6) :=
  Night6836Tree.sound w231 pick231 6 t567 _ (by decide +kernel)
theorem cov231_7 : PA.Covered 7 (OZ.Valid 7 w231.low w231.t w231.y w231.r w231.cap) (P33.root 7) :=
  Night6836Tree.sound w231 pick231 7 t568 _ (by decide +kernel)
theorem window231 : P33.WindowCount w231 := by
  apply P33.window_count w231 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov231_1
  · exact cov231_2
  · exact cov231_3
  · exact cov231_4
  · exact cov231_5
  · exact cov231_6
  · exact cov231_7
def w232 : P33.Window := ⟨13,34,6634,6207,246394160258368850,22656,27000,5000000,81920000000⟩
def h232_0 : Height w232 := ⟨22656,27000,by decide +kernel⟩
def h232_1 : Height w232 := ⟨27244,24000,by decide +kernel⟩
def h232_2 : Height w232 := ⟨33576,21000,by decide +kernel⟩
def h232_3 : Height w232 := ⟨43704,18000,by decide +kernel⟩
def h232_4 : Height w232 := ⟨64912,15000,by decide +kernel⟩
def pick232 (cl : ℕ) : Height w232 := if cl<49 then (if cl<6 then (h232_0) else (h232_1)) else (if cl<549 then (h232_2) else (if cl<1028 then (h232_3) else (h232_4)))
private theorem k232_1_0 : check w232 pick232 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k232_1_1 : check w232 pick232 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k232_1_2 : check w232 pick232 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w232 pick232 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k232_1_0 k232_1_1
private theorem k232_1_3 : check w232 pick232 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k232_1_4 : check w232 pick232 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k232_1_5 : check w232 pick232 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w232 pick232 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k232_1_3 k232_1_4
private theorem k232_1_6 : check w232 pick232 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w232 pick232 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k232_1_2 k232_1_5
private theorem k232_1_7 : check w232 pick232 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k232_1_8 : check w232 pick232 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k232_1_9 : check w232 pick232 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w232 pick232 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k232_1_7 k232_1_8
private theorem k232_1_10 : check w232 pick232 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k232_1_11 : check w232 pick232 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k232_1_12 : check w232 pick232 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w232 pick232 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k232_1_10 k232_1_11
private theorem k232_1_13 : check w232 pick232 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w232 pick232 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k232_1_9 k232_1_12
private theorem k232_1_14 : check w232 pick232 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w232 pick232 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k232_1_6 k232_1_13
theorem cov232_1 : PA.Covered 1 (OZ.Valid 1 w232.low w232.t w232.y w232.r w232.cap) (P33.root 1) :=
  Night6836Tree.sound w232 pick232 1 t7674 _ k232_1_14
private theorem k232_2_0 : check w232 pick232 2 t8597 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k232_2_1 : check w232 pick232 2 t5723 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k232_2_2 : check w232 pick232 2 t8598 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w232 pick232 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t8597 t5723 k232_2_0 k232_2_1
private theorem k232_2_3 : check w232 pick232 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k232_2_4 : check w232 pick232 2 t7719 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k232_2_5 : check w232 pick232 2 t7720 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w232 pick232 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t7719 k232_2_3 k232_2_4
private theorem k232_2_6 : check w232 pick232 2 t8599 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w232 pick232 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t8598 t7720 k232_2_2 k232_2_5
theorem cov232_2 : PA.Covered 2 (OZ.Valid 2 w232.low w232.t w232.y w232.r w232.cap) (P33.root 2) :=
  Night6836Tree.sound w232 pick232 2 t8599 _ k232_2_6
theorem cov232_3 : PA.Covered 3 (OZ.Valid 3 w232.low w232.t w232.y w232.r w232.cap) (P33.root 3) :=
  Night6836Tree.sound w232 pick232 3 t564 _ (by decide +kernel)
theorem cov232_4 : PA.Covered 4 (OZ.Valid 4 w232.low w232.t w232.y w232.r w232.cap) (P33.root 4) :=
  Night6836Tree.sound w232 pick232 4 t565 _ (by decide +kernel)
theorem cov232_5 : PA.Covered 5 (OZ.Valid 5 w232.low w232.t w232.y w232.r w232.cap) (P33.root 5) :=
  Night6836Tree.sound w232 pick232 5 t566 _ (by decide +kernel)
theorem cov232_6 : PA.Covered 6 (OZ.Valid 6 w232.low w232.t w232.y w232.r w232.cap) (P33.root 6) :=
  Night6836Tree.sound w232 pick232 6 t567 _ (by decide +kernel)
theorem cov232_7 : PA.Covered 7 (OZ.Valid 7 w232.low w232.t w232.y w232.r w232.cap) (P33.root 7) :=
  Night6836Tree.sound w232 pick232 7 t568 _ (by decide +kernel)
theorem window232 : P33.WindowCount w232 := by
  apply P33.window_count w232 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov232_1
  · exact cov232_2
  · exact cov232_3
  · exact cov232_4
  · exact cov232_5
  · exact cov232_6
  · exact cov232_7
def w233 : P33.Window := ⟨13,35,5148,4199,243000476915320304,32684,42000,5000000,81920000000⟩
def h233_0 : Height w233 := ⟨32684,42000,by decide +kernel⟩
def h233_1 : Height w233 := ⟨36684,39000,by decide +kernel⟩
def h233_2 : Height w233 := ⟨41409,36000,by decide +kernel⟩
def h233_3 : Height w233 := ⟨47225,33000,by decide +kernel⟩
def h233_4 : Height w233 := ⟨54797,30000,by decide +kernel⟩
def h233_5 : Height w233 := ⟨65463,27000,by decide +kernel⟩
def pick233 (cl : ℕ) : Height w233 := if cl<32 then (if cl<2 then (h233_0) else (if cl<10 then (h233_1) else (h233_2))) else (if cl<145 then (h233_3) else (if cl<731 then (h233_4) else (h233_5)))
private theorem k233_1_0 : check w233 pick233 1 t7724 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k233_1_1 : check w233 pick233 1 t7727 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k233_1_2 : check w233 pick233 1 t7728 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w233 pick233 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t7724 t7727 k233_1_0 k233_1_1
private theorem k233_1_3 : check w233 pick233 1 t7732 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k233_1_4 : check w233 pick233 1 t7403 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k233_1_5 : check w233 pick233 1 t7733 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w233 pick233 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7732 t7403 k233_1_3 k233_1_4
private theorem k233_1_6 : check w233 pick233 1 t7734 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w233 pick233 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7728 t7733 k233_1_2 k233_1_5
private theorem k233_1_7 : check w233 pick233 1 t7701 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k233_1_8 : check w233 pick233 1 t7702 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k233_1_9 : check w233 pick233 1 t7703 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w233 pick233 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t7701 t7702 k233_1_7 k233_1_8
private theorem k233_1_10 : check w233 pick233 1 t7317 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k233_1_11 : check w233 pick233 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k233_1_12 : check w233 pick233 1 t7319 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w233 pick233 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t7317 t7318 k233_1_10 k233_1_11
private theorem k233_1_13 : check w233 pick233 1 t7704 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w233 pick233 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t7703 t7319 k233_1_9 k233_1_12
private theorem k233_1_14 : check w233 pick233 1 t7735 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w233 pick233 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7734 t7704 k233_1_6 k233_1_13
theorem cov233_1 : PA.Covered 1 (OZ.Valid 1 w233.low w233.t w233.y w233.r w233.cap) (P33.root 1) :=
  Night6836Tree.sound w233 pick233 1 t7735 _ k233_1_14
theorem cov233_2 : PA.Covered 2 (OZ.Valid 2 w233.low w233.t w233.y w233.r w233.cap) (P33.root 2) :=
  Night6836Tree.sound w233 pick233 2 t5320 _ (by decide +kernel)
theorem cov233_3 : PA.Covered 3 (OZ.Valid 3 w233.low w233.t w233.y w233.r w233.cap) (P33.root 3) :=
  Night6836Tree.sound w233 pick233 3 t564 _ (by decide +kernel)
theorem cov233_4 : PA.Covered 4 (OZ.Valid 4 w233.low w233.t w233.y w233.r w233.cap) (P33.root 4) :=
  Night6836Tree.sound w233 pick233 4 t565 _ (by decide +kernel)
theorem cov233_5 : PA.Covered 5 (OZ.Valid 5 w233.low w233.t w233.y w233.r w233.cap) (P33.root 5) :=
  Night6836Tree.sound w233 pick233 5 t566 _ (by decide +kernel)
theorem cov233_6 : PA.Covered 6 (OZ.Valid 6 w233.low w233.t w233.y w233.r w233.cap) (P33.root 6) :=
  Night6836Tree.sound w233 pick233 6 t567 _ (by decide +kernel)
theorem cov233_7 : PA.Covered 7 (OZ.Valid 7 w233.low w233.t w233.y w233.r w233.cap) (P33.root 7) :=
  Night6836Tree.sound w233 pick233 7 t2134 _ (by decide +kernel)
theorem window233 : P33.WindowCount w233 := by
  apply P33.window_count w233 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov233_1
  · exact cov233_2
  · exact cov233_3
  · exact cov233_4
  · exact cov233_5
  · exact cov233_6
  · exact cov233_7
def w234 : P33.Window := ⟨13,35,6562,6408,245456776817109950,22091,27000,5000000,81920000000⟩
def h234_0 : Height w234 := ⟨22091,27000,by decide +kernel⟩
def h234_1 : Height w234 := ⟨26467,24000,by decide +kernel⟩
def h234_2 : Height w234 := ⟨32418,21000,by decide +kernel⟩
def h234_3 : Height w234 := ⟨41726,18000,by decide +kernel⟩
def h234_4 : Height w234 := ⟨60424,15000,by decide +kernel⟩
def pick234 (cl : ℕ) : Height w234 := if cl<36 then (if cl<5 then (h234_0) else (h234_1)) else (if cl<302 then (h234_2) else (if cl<1026 then (h234_3) else (h234_4)))
private theorem k234_1_0 : check w234 pick234 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k234_1_1 : check w234 pick234 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k234_1_2 : check w234 pick234 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w234 pick234 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k234_1_0 k234_1_1
private theorem k234_1_3 : check w234 pick234 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k234_1_4 : check w234 pick234 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k234_1_5 : check w234 pick234 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w234 pick234 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k234_1_3 k234_1_4
private theorem k234_1_6 : check w234 pick234 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w234 pick234 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k234_1_2 k234_1_5
private theorem k234_1_7 : check w234 pick234 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k234_1_8 : check w234 pick234 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k234_1_9 : check w234 pick234 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w234 pick234 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k234_1_7 k234_1_8
private theorem k234_1_10 : check w234 pick234 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k234_1_11 : check w234 pick234 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k234_1_12 : check w234 pick234 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w234 pick234 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k234_1_10 k234_1_11
private theorem k234_1_13 : check w234 pick234 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w234 pick234 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k234_1_9 k234_1_12
private theorem k234_1_14 : check w234 pick234 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w234 pick234 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k234_1_6 k234_1_13
theorem cov234_1 : PA.Covered 1 (OZ.Valid 1 w234.low w234.t w234.y w234.r w234.cap) (P33.root 1) :=
  Night6836Tree.sound w234 pick234 1 t7674 _ k234_1_14
private theorem k234_2_0 : check w234 pick234 2 t8600 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k234_2_1 : check w234 pick234 2 t5723 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k234_2_2 : check w234 pick234 2 t8601 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w234 pick234 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t8600 t5723 k234_2_0 k234_2_1
private theorem k234_2_3 : check w234 pick234 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k234_2_4 : check w234 pick234 2 t7719 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k234_2_5 : check w234 pick234 2 t7720 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w234 pick234 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t7719 k234_2_3 k234_2_4
private theorem k234_2_6 : check w234 pick234 2 t8602 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w234 pick234 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t8601 t7720 k234_2_2 k234_2_5
theorem cov234_2 : PA.Covered 2 (OZ.Valid 2 w234.low w234.t w234.y w234.r w234.cap) (P33.root 2) :=
  Night6836Tree.sound w234 pick234 2 t8602 _ k234_2_6
theorem cov234_3 : PA.Covered 3 (OZ.Valid 3 w234.low w234.t w234.y w234.r w234.cap) (P33.root 3) :=
  Night6836Tree.sound w234 pick234 3 t4151 _ (by decide +kernel)
theorem cov234_4 : PA.Covered 4 (OZ.Valid 4 w234.low w234.t w234.y w234.r w234.cap) (P33.root 4) :=
  Night6836Tree.sound w234 pick234 4 t565 _ (by decide +kernel)
theorem cov234_5 : PA.Covered 5 (OZ.Valid 5 w234.low w234.t w234.y w234.r w234.cap) (P33.root 5) :=
  Night6836Tree.sound w234 pick234 5 t566 _ (by decide +kernel)
theorem cov234_6 : PA.Covered 6 (OZ.Valid 6 w234.low w234.t w234.y w234.r w234.cap) (P33.root 6) :=
  Night6836Tree.sound w234 pick234 6 t567 _ (by decide +kernel)
theorem cov234_7 : PA.Covered 7 (OZ.Valid 7 w234.low w234.t w234.y w234.r w234.cap) (P33.root 7) :=
  Night6836Tree.sound w234 pick234 7 t568 _ (by decide +kernel)
theorem window234 : P33.WindowCount w234 := by
  apply P33.window_count w234 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov234_1
  · exact cov234_2
  · exact cov234_3
  · exact cov234_4
  · exact cov234_5
  · exact cov234_6
  · exact cov234_7
def w235 : P33.Window := ⟨13,36,6407,6207,246844894257638048,25280,27000,5000000,81920000000⟩
def h235_0 : Height w235 := ⟨25280,27000,by decide +kernel⟩
def h235_1 : Height w235 := ⟨30090,24000,by decide +kernel⟩
def h235_2 : Height w235 := ⟨36767,21000,by decide +kernel⟩
def h235_3 : Height w235 := ⟨47508,18000,by decide +kernel⟩
def pick235 (cl : ℕ) : Height w235 := if cl<70 then (if cl<10 then (h235_0) else (h235_1)) else (if cl<853 then (h235_2) else (h235_3))
private theorem k235_1_0 : check w235 pick235 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k235_1_1 : check w235 pick235 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k235_1_2 : check w235 pick235 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w235 pick235 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k235_1_0 k235_1_1
private theorem k235_1_3 : check w235 pick235 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k235_1_4 : check w235 pick235 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k235_1_5 : check w235 pick235 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w235 pick235 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k235_1_3 k235_1_4
private theorem k235_1_6 : check w235 pick235 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w235 pick235 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k235_1_2 k235_1_5
private theorem k235_1_7 : check w235 pick235 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k235_1_8 : check w235 pick235 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k235_1_9 : check w235 pick235 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w235 pick235 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k235_1_7 k235_1_8
private theorem k235_1_10 : check w235 pick235 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k235_1_11 : check w235 pick235 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k235_1_12 : check w235 pick235 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w235 pick235 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k235_1_10 k235_1_11
private theorem k235_1_13 : check w235 pick235 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w235 pick235 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k235_1_9 k235_1_12
private theorem k235_1_14 : check w235 pick235 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w235 pick235 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k235_1_6 k235_1_13
theorem cov235_1 : PA.Covered 1 (OZ.Valid 1 w235.low w235.t w235.y w235.r w235.cap) (P33.root 1) :=
  Night6836Tree.sound w235 pick235 1 t7674 _ k235_1_14
private theorem k235_2_0 : check w235 pick235 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k235_2_1 : check w235 pick235 2 t5723 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k235_2_2 : check w235 pick235 2 t5724 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w235 pick235 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5723 k235_2_0 k235_2_1
private theorem k235_2_3 : check w235 pick235 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k235_2_4 : check w235 pick235 2 t7719 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k235_2_5 : check w235 pick235 2 t7720 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w235 pick235 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t7719 k235_2_3 k235_2_4
private theorem k235_2_6 : check w235 pick235 2 t7721 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w235 pick235 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5724 t7720 k235_2_2 k235_2_5
theorem cov235_2 : PA.Covered 2 (OZ.Valid 2 w235.low w235.t w235.y w235.r w235.cap) (P33.root 2) :=
  Night6836Tree.sound w235 pick235 2 t7721 _ k235_2_6
theorem cov235_3 : PA.Covered 3 (OZ.Valid 3 w235.low w235.t w235.y w235.r w235.cap) (P33.root 3) :=
  Night6836Tree.sound w235 pick235 3 t564 _ (by decide +kernel)
theorem cov235_4 : PA.Covered 4 (OZ.Valid 4 w235.low w235.t w235.y w235.r w235.cap) (P33.root 4) :=
  Night6836Tree.sound w235 pick235 4 t565 _ (by decide +kernel)
theorem cov235_5 : PA.Covered 5 (OZ.Valid 5 w235.low w235.t w235.y w235.r w235.cap) (P33.root 5) :=
  Night6836Tree.sound w235 pick235 5 t566 _ (by decide +kernel)
theorem cov235_6 : PA.Covered 6 (OZ.Valid 6 w235.low w235.t w235.y w235.r w235.cap) (P33.root 6) :=
  Night6836Tree.sound w235 pick235 6 t567 _ (by decide +kernel)
theorem cov235_7 : PA.Covered 7 (OZ.Valid 7 w235.low w235.t w235.y w235.r w235.cap) (P33.root 7) :=
  Night6836Tree.sound w235 pick235 7 t2134 _ (by decide +kernel)
theorem window235 : P33.WindowCount w235 := by
  apply P33.window_count w235 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov235_1
  · exact cov235_2
  · exact cov235_3
  · exact cov235_4
  · exact cov235_5
  · exact cov235_6
  · exact cov235_7
def w236 : P33.Window := ⟨13,37,6136,5187,245661417074699002,30842,33000,5000000,81920000000⟩
def h236_0 : Height w236 := ⟨30842,33000,by decide +kernel⟩
def h236_1 : Height w236 := ⟨35402,30000,by decide +kernel⟩
def h236_2 : Height w236 := ⟨41218,27000,by decide +kernel⟩
def h236_3 : Height w236 := ⟨49261,24000,by decide +kernel⟩
def h236_4 : Height w236 := ⟨61840,21000,by decide +kernel⟩
def pick236 (cl : ℕ) : Height w236 := if cl<32 then (if cl<6 then (h236_0) else (h236_1)) else (if cl<192 then (h236_2) else (if cl<961 then (h236_3) else (h236_4)))
private theorem k236_1_0 : check w236 pick236 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k236_1_1 : check w236 pick236 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k236_1_2 : check w236 pick236 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w236 pick236 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k236_1_0 k236_1_1
private theorem k236_1_3 : check w236 pick236 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k236_1_4 : check w236 pick236 1 t8081 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k236_1_5 : check w236 pick236 1 t8082 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w236 pick236 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t8081 k236_1_3 k236_1_4
private theorem k236_1_6 : check w236 pick236 1 t8083 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w236 pick236 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t8082 k236_1_2 k236_1_5
private theorem k236_1_7 : check w236 pick236 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k236_1_8 : check w236 pick236 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k236_1_9 : check w236 pick236 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w236 pick236 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k236_1_7 k236_1_8
private theorem k236_1_10 : check w236 pick236 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k236_1_11 : check w236 pick236 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k236_1_12 : check w236 pick236 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w236 pick236 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k236_1_10 k236_1_11
private theorem k236_1_13 : check w236 pick236 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w236 pick236 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k236_1_9 k236_1_12
private theorem k236_1_14 : check w236 pick236 1 t8096 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w236 pick236 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8083 t7649 k236_1_6 k236_1_13
theorem cov236_1 : PA.Covered 1 (OZ.Valid 1 w236.low w236.t w236.y w236.r w236.cap) (P33.root 1) :=
  Night6836Tree.sound w236 pick236 1 t8096 _ k236_1_14
private theorem k236_2_0 : check w236 pick236 2 t8605 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k236_2_1 : check w236 pick236 2 t4008 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k236_2_2 : check w236 pick236 2 t8606 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w236 pick236 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t8605 t4008 k236_2_0 k236_2_1
private theorem k236_2_3 : check w236 pick236 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k236_2_4 : check w236 pick236 2 t8612 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k236_2_5 : check w236 pick236 2 t8613 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w236 pick236 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t8612 k236_2_3 k236_2_4
private theorem k236_2_6 : check w236 pick236 2 t8614 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w236 pick236 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t8606 t8613 k236_2_2 k236_2_5
theorem cov236_2 : PA.Covered 2 (OZ.Valid 2 w236.low w236.t w236.y w236.r w236.cap) (P33.root 2) :=
  Night6836Tree.sound w236 pick236 2 t8614 _ k236_2_6
theorem cov236_3 : PA.Covered 3 (OZ.Valid 3 w236.low w236.t w236.y w236.r w236.cap) (P33.root 3) :=
  Night6836Tree.sound w236 pick236 3 t564 _ (by decide +kernel)
theorem cov236_4 : PA.Covered 4 (OZ.Valid 4 w236.low w236.t w236.y w236.r w236.cap) (P33.root 4) :=
  Night6836Tree.sound w236 pick236 4 t565 _ (by decide +kernel)
theorem cov236_5 : PA.Covered 5 (OZ.Valid 5 w236.low w236.t w236.y w236.r w236.cap) (P33.root 5) :=
  Night6836Tree.sound w236 pick236 5 t566 _ (by decide +kernel)
theorem cov236_6 : PA.Covered 6 (OZ.Valid 6 w236.low w236.t w236.y w236.r w236.cap) (P33.root 6) :=
  Night6836Tree.sound w236 pick236 6 t567 _ (by decide +kernel)
theorem cov236_7 : PA.Covered 7 (OZ.Valid 7 w236.low w236.t w236.y w236.r w236.cap) (P33.root 7) :=
  Night6836Tree.sound w236 pick236 7 t2134 _ (by decide +kernel)
theorem window236 : P33.WindowCount w236 := by
  apply P33.window_count w236 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov236_1
  · exact cov236_2
  · exact cov236_3
  · exact cov236_4
  · exact cov236_5
  · exact cov236_6
  · exact cov236_7
def w237 : P33.Window := ⟨13,37,6206,6002,244477832483589297,24728,30000,5000000,81920000000⟩
def h237_0 : Height w237 := ⟨24728,30000,by decide +kernel⟩
def h237_1 : Height w237 := ⟨28870,27000,by decide +kernel⟩
def h237_2 : Height w237 := ⟨34206,24000,by decide +kernel⟩
def h237_3 : Height w237 := ⟨41779,21000,by decide +kernel⟩
def h237_4 : Height w237 := ⟨54339,18000,by decide +kernel⟩
def pick237 (cl : ℕ) : Height w237 := if cl<25 then (if cl<3 then (h237_0) else (h237_1)) else (if cl<140 then (h237_2) else (if cl<961 then (h237_3) else (h237_4)))
private theorem k237_1_0 : check w237 pick237 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k237_1_1 : check w237 pick237 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k237_1_2 : check w237 pick237 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w237 pick237 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k237_1_0 k237_1_1
private theorem k237_1_3 : check w237 pick237 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k237_1_4 : check w237 pick237 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k237_1_5 : check w237 pick237 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w237 pick237 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k237_1_3 k237_1_4
private theorem k237_1_6 : check w237 pick237 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w237 pick237 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k237_1_2 k237_1_5
private theorem k237_1_7 : check w237 pick237 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k237_1_8 : check w237 pick237 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k237_1_9 : check w237 pick237 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w237 pick237 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k237_1_7 k237_1_8
private theorem k237_1_10 : check w237 pick237 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k237_1_11 : check w237 pick237 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k237_1_12 : check w237 pick237 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w237 pick237 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k237_1_10 k237_1_11
private theorem k237_1_13 : check w237 pick237 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w237 pick237 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k237_1_9 k237_1_12
private theorem k237_1_14 : check w237 pick237 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w237 pick237 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k237_1_6 k237_1_13
theorem cov237_1 : PA.Covered 1 (OZ.Valid 1 w237.low w237.t w237.y w237.r w237.cap) (P33.root 1) :=
  Night6836Tree.sound w237 pick237 1 t7674 _ k237_1_14
private theorem k237_2_0 : check w237 pick237 2 t5721 ⟨2,2,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k237_2_1 : check w237 pick237 2 t5723 ⟨3,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k237_2_2 : check w237 pick237 2 t5724 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w237 pick237 2 ⟨2,7,4,16,2,52,2,139⟩ 0 2 t5721 t5723 k237_2_0 k237_2_1
private theorem k237_2_3 : check w237 pick237 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k237_2_4 : check w237 pick237 2 t7719 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k237_2_5 : check w237 pick237 2 t7720 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w237 pick237 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t7719 k237_2_3 k237_2_4
private theorem k237_2_6 : check w237 pick237 2 t7721 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w237 pick237 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t5724 t7720 k237_2_2 k237_2_5
theorem cov237_2 : PA.Covered 2 (OZ.Valid 2 w237.low w237.t w237.y w237.r w237.cap) (P33.root 2) :=
  Night6836Tree.sound w237 pick237 2 t7721 _ k237_2_6
theorem cov237_3 : PA.Covered 3 (OZ.Valid 3 w237.low w237.t w237.y w237.r w237.cap) (P33.root 3) :=
  Night6836Tree.sound w237 pick237 3 t564 _ (by decide +kernel)
theorem cov237_4 : PA.Covered 4 (OZ.Valid 4 w237.low w237.t w237.y w237.r w237.cap) (P33.root 4) :=
  Night6836Tree.sound w237 pick237 4 t565 _ (by decide +kernel)
theorem cov237_5 : PA.Covered 5 (OZ.Valid 5 w237.low w237.t w237.y w237.r w237.cap) (P33.root 5) :=
  Night6836Tree.sound w237 pick237 5 t566 _ (by decide +kernel)
theorem cov237_6 : PA.Covered 6 (OZ.Valid 6 w237.low w237.t w237.y w237.r w237.cap) (P33.root 6) :=
  Night6836Tree.sound w237 pick237 6 t567 _ (by decide +kernel)
theorem cov237_7 : PA.Covered 7 (OZ.Valid 7 w237.low w237.t w237.y w237.r w237.cap) (P33.root 7) :=
  Night6836Tree.sound w237 pick237 7 t2134 _ (by decide +kernel)
theorem window237 : P33.WindowCount w237 := by
  apply P33.window_count w237 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov237_1
  · exact cov237_2
  · exact cov237_3
  · exact cov237_4
  · exact cov237_5
  · exact cov237_6
  · exact cov237_7
def w238 : P33.Window := ⟨13,38,5186,4237,244785708913576123,37484,42000,5000000,81920000000⟩
def h238_0 : Height w238 := ⟨37484,42000,by decide +kernel⟩
def h238_1 : Height w238 := ⟨41664,39000,by decide +kernel⟩
def h238_2 : Height w238 := ⟨46616,36000,by decide +kernel⟩
def h238_3 : Height w238 := ⟨52725,33000,by decide +kernel⟩
def h238_4 : Height w238 := ⟨60690,30000,by decide +kernel⟩
def h238_5 : Height w238 := ⟨71905,27000,by decide +kernel⟩
def pick238 (cl : ℕ) : Height w238 := if cl<42 then (if cl<4 then (h238_0) else (if cl<13 then (h238_1) else (h238_2))) else (if cl<177 then (h238_3) else (if cl<853 then (h238_4) else (h238_5)))
private theorem k238_1_0 : check w238 pick238 1 t8615 ⟨1,7,2,16,1,52,1,55⟩ = true := by decide +kernel
private theorem k238_1_1 : check w238 pick238 1 t8616 ⟨1,7,2,16,1,52,56,83⟩ = true := by decide +kernel
private theorem k238_1_2 : check w238 pick238 1 t8617 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w238 pick238 1 ⟨1,7,2,16,1,52,1,83⟩ 3 55 t8615 t8616 k238_1_0 k238_1_1
private theorem k238_1_3 : check w238 pick238 1 t8619 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k238_1_4 : check w238 pick238 1 t7348 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k238_1_5 : check w238 pick238 1 t8620 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w238 pick238 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t8619 t7348 k238_1_3 k238_1_4
private theorem k238_1_6 : check w238 pick238 1 t8621 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w238 pick238 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t8617 t8620 k238_1_2 k238_1_5
private theorem k238_1_7 : check w238 pick238 1 t7386 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k238_1_8 : check w238 pick238 1 t7362 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k238_1_9 : check w238 pick238 1 t7387 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w238 pick238 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7386 t7362 k238_1_7 k238_1_8
private theorem k238_1_10 : check w238 pick238 1 t7368 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k238_1_11 : check w238 pick238 1 t7318 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k238_1_12 : check w238 pick238 1 t7369 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w238 pick238 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7368 t7318 k238_1_10 k238_1_11
private theorem k238_1_13 : check w238 pick238 1 t7388 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w238 pick238 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7387 t7369 k238_1_9 k238_1_12
private theorem k238_1_14 : check w238 pick238 1 t8622 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w238 pick238 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t8621 t7388 k238_1_6 k238_1_13
theorem cov238_1 : PA.Covered 1 (OZ.Valid 1 w238.low w238.t w238.y w238.r w238.cap) (P33.root 1) :=
  Night6836Tree.sound w238 pick238 1 t8622 _ k238_1_14
private theorem k238_2_0 : check w238 pick238 2 t6415 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k238_2_1 : check w238 pick238 2 t8252 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k238_2_2 : check w238 pick238 2 t8623 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w238 pick238 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t6415 t8252 k238_2_0 k238_2_1
theorem cov238_2 : PA.Covered 2 (OZ.Valid 2 w238.low w238.t w238.y w238.r w238.cap) (P33.root 2) :=
  Night6836Tree.sound w238 pick238 2 t8623 _ k238_2_2
theorem cov238_3 : PA.Covered 3 (OZ.Valid 3 w238.low w238.t w238.y w238.r w238.cap) (P33.root 3) :=
  Night6836Tree.sound w238 pick238 3 t564 _ (by decide +kernel)
theorem cov238_4 : PA.Covered 4 (OZ.Valid 4 w238.low w238.t w238.y w238.r w238.cap) (P33.root 4) :=
  Night6836Tree.sound w238 pick238 4 t565 _ (by decide +kernel)
theorem cov238_5 : PA.Covered 5 (OZ.Valid 5 w238.low w238.t w238.y w238.r w238.cap) (P33.root 5) :=
  Night6836Tree.sound w238 pick238 5 t566 _ (by decide +kernel)
theorem cov238_6 : PA.Covered 6 (OZ.Valid 6 w238.low w238.t w238.y w238.r w238.cap) (P33.root 6) :=
  Night6836Tree.sound w238 pick238 6 t567 _ (by decide +kernel)
theorem cov238_7 : PA.Covered 7 (OZ.Valid 7 w238.low w238.t w238.y w238.r w238.cap) (P33.root 7) :=
  Night6836Tree.sound w238 pick238 7 t2134 _ (by decide +kernel)
theorem window238 : P33.WindowCount w238 := by
  apply P33.window_count w238 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov238_1
  · exact cov238_2
  · exact cov238_3
  · exact cov238_4
  · exact cov238_5
  · exact cov238_6
  · exact cov238_7
def w239 : P33.Window := ⟨13,38,6001,5790,246808562656659971,28421,30000,5000000,81920000000⟩
def h239_0 : Height w239 := ⟨28421,30000,by decide +kernel⟩
def h239_1 : Height w239 := ⟨32985,27000,by decide +kernel⟩
def h239_2 : Height w239 := ⟨38976,24000,by decide +kernel⟩
def h239_3 : Height w239 := ⟨47686,21000,by decide +kernel⟩
def h239_4 : Height w239 := ⟨62635,18000,by decide +kernel⟩
def pick239 (cl : ℕ) : Height w239 := if cl<37 then (if cl<6 then (h239_0) else (h239_1)) else (if cl<261 then (h239_2) else (if cl<1002 then (h239_3) else (h239_4)))
private theorem k239_1_0 : check w239 pick239 1 t7651 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k239_1_1 : check w239 pick239 1 t7661 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k239_1_2 : check w239 pick239 1 t7662 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w239 pick239 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t7651 t7661 k239_1_0 k239_1_1
private theorem k239_1_3 : check w239 pick239 1 t7671 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k239_1_4 : check w239 pick239 1 t7623 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k239_1_5 : check w239 pick239 1 t7672 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w239 pick239 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t7671 t7623 k239_1_3 k239_1_4
private theorem k239_1_6 : check w239 pick239 1 t7673 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w239 pick239 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t7662 t7672 k239_1_2 k239_1_5
private theorem k239_1_7 : check w239 pick239 1 t7634 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k239_1_8 : check w239 pick239 1 t7641 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k239_1_9 : check w239 pick239 1 t7642 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w239 pick239 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t7634 t7641 k239_1_7 k239_1_8
private theorem k239_1_10 : check w239 pick239 1 t7647 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k239_1_11 : check w239 pick239 1 t7590 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k239_1_12 : check w239 pick239 1 t7648 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w239 pick239 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t7647 t7590 k239_1_10 k239_1_11
private theorem k239_1_13 : check w239 pick239 1 t7649 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w239 pick239 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t7642 t7648 k239_1_9 k239_1_12
private theorem k239_1_14 : check w239 pick239 1 t7674 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w239 pick239 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t7673 t7649 k239_1_6 k239_1_13
theorem cov239_1 : PA.Covered 1 (OZ.Valid 1 w239.low w239.t w239.y w239.r w239.cap) (P33.root 1) :=
  Night6836Tree.sound w239 pick239 1 t7674 _ k239_1_14
private theorem k239_2_0 : check w239 pick239 2 t8625 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k239_2_1 : check w239 pick239 2 t4008 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k239_2_2 : check w239 pick239 2 t8626 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w239 pick239 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t8625 t4008 k239_2_0 k239_2_1
private theorem k239_2_3 : check w239 pick239 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k239_2_4 : check w239 pick239 2 t3530 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k239_2_5 : check w239 pick239 2 t3531 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w239 pick239 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t3530 k239_2_3 k239_2_4
private theorem k239_2_6 : check w239 pick239 2 t8627 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w239 pick239 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t8626 t3531 k239_2_2 k239_2_5
theorem cov239_2 : PA.Covered 2 (OZ.Valid 2 w239.low w239.t w239.y w239.r w239.cap) (P33.root 2) :=
  Night6836Tree.sound w239 pick239 2 t8627 _ k239_2_6
theorem cov239_3 : PA.Covered 3 (OZ.Valid 3 w239.low w239.t w239.y w239.r w239.cap) (P33.root 3) :=
  Night6836Tree.sound w239 pick239 3 t564 _ (by decide +kernel)
theorem cov239_4 : PA.Covered 4 (OZ.Valid 4 w239.low w239.t w239.y w239.r w239.cap) (P33.root 4) :=
  Night6836Tree.sound w239 pick239 4 t565 _ (by decide +kernel)
theorem cov239_5 : PA.Covered 5 (OZ.Valid 5 w239.low w239.t w239.y w239.r w239.cap) (P33.root 5) :=
  Night6836Tree.sound w239 pick239 5 t566 _ (by decide +kernel)
theorem cov239_6 : PA.Covered 6 (OZ.Valid 6 w239.low w239.t w239.y w239.r w239.cap) (P33.root 6) :=
  Night6836Tree.sound w239 pick239 6 t567 _ (by decide +kernel)
theorem cov239_7 : PA.Covered 7 (OZ.Valid 7 w239.low w239.t w239.y w239.r w239.cap) (P33.root 7) :=
  Night6836Tree.sound w239 pick239 7 t2134 _ (by decide +kernel)
theorem window239 : P33.WindowCount w239 := by
  apply P33.window_count w239 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov239_1
  · exact cov239_2
  · exact cov239_3
  · exact cov239_4
  · exact cov239_5
  · exact cov239_6
  · exact cov239_7
end ProximityPrize.SubmissionLower.Night6836Bank
