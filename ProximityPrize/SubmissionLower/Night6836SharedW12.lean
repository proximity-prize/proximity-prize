/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT03
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w360 : P33.Window := ⟨6,41,7577,7537,238382357149481862,26790,15000,5000000,81920000000⟩
def h360_0 : Height w360 := ⟨26790,15000,by decide +kernel⟩
def h360_1 : Height w360 := ⟨31672,12000,by decide +kernel⟩
def h360_2 : Height w360 := ⟨40569,9000,by decide +kernel⟩
def pick360 (cl : ℕ) : Height w360 := if cl<13 then (h360_0) else (if cl<278 then (h360_1) else (h360_2))
private theorem k360_1_0 : check w360 pick360 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k360_1_1 : check w360 pick360 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k360_1_2 : check w360 pick360 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w360 pick360 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k360_1_0 k360_1_1
private theorem k360_1_3 : check w360 pick360 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k360_1_4 : check w360 pick360 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k360_1_5 : check w360 pick360 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w360 pick360 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k360_1_3 k360_1_4
private theorem k360_1_6 : check w360 pick360 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w360 pick360 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k360_1_2 k360_1_5
private theorem k360_1_7 : check w360 pick360 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k360_1_8 : check w360 pick360 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k360_1_9 : check w360 pick360 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w360 pick360 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k360_1_7 k360_1_8
private theorem k360_1_10 : check w360 pick360 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k360_1_11 : check w360 pick360 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k360_1_12 : check w360 pick360 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w360 pick360 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k360_1_10 k360_1_11
private theorem k360_1_13 : check w360 pick360 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w360 pick360 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k360_1_9 k360_1_12
private theorem k360_1_14 : check w360 pick360 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w360 pick360 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k360_1_6 k360_1_13
theorem cov360_1 : PA.Covered 1 (OZ.Valid 1 w360.low w360.t w360.y w360.r w360.cap) (P33.root 1) :=
  Night6836Tree.sound w360 pick360 1 t9213 _ k360_1_14
private theorem k360_2_0 : check w360 pick360 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k360_2_1 : check w360 pick360 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k360_2_2 : check w360 pick360 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w360 pick360 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k360_2_0 k360_2_1
theorem cov360_2 : PA.Covered 2 (OZ.Valid 2 w360.low w360.t w360.y w360.r w360.cap) (P33.root 2) :=
  Night6836Tree.sound w360 pick360 2 t9134 _ k360_2_2
theorem cov360_3 : PA.Covered 3 (OZ.Valid 3 w360.low w360.t w360.y w360.r w360.cap) (P33.root 3) :=
  Night6836Tree.sound w360 pick360 3 t564 _ (by decide +kernel)
theorem cov360_4 : PA.Covered 4 (OZ.Valid 4 w360.low w360.t w360.y w360.r w360.cap) (P33.root 4) :=
  Night6836Tree.sound w360 pick360 4 t565 _ (by decide +kernel)
theorem cov360_5 : PA.Covered 5 (OZ.Valid 5 w360.low w360.t w360.y w360.r w360.cap) (P33.root 5) :=
  Night6836Tree.sound w360 pick360 5 t566 _ (by decide +kernel)
theorem cov360_6 : PA.Covered 6 (OZ.Valid 6 w360.low w360.t w360.y w360.r w360.cap) (P33.root 6) :=
  Night6836Tree.sound w360 pick360 6 t567 _ (by decide +kernel)
theorem cov360_7 : PA.Covered 7 (OZ.Valid 7 w360.low w360.t w360.y w360.r w360.cap) (P33.root 7) :=
  Night6836Tree.sound w360 pick360 7 t568 _ (by decide +kernel)
theorem window360 : P33.WindowCount w360 := by
  apply P33.window_count w360 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov360_1
  · exact cov360_2
  · exact cov360_3
  · exact cov360_4
  · exact cov360_5
  · exact cov360_6
  · exact cov360_7
def w361 : P33.Window := ⟨6,42,7536,7493,241782219106079807,27972,15000,5000000,81920000000⟩
def h361_0 : Height w361 := ⟨27972,15000,by decide +kernel⟩
def h361_1 : Height w361 := ⟨33001,12000,by decide +kernel⟩
def h361_2 : Height w361 := ⟨42237,9000,by decide +kernel⟩
def pick361 (cl : ℕ) : Height w361 := if cl<14 then (h361_0) else (if cl<302 then (h361_1) else (h361_2))
private theorem k361_1_0 : check w361 pick361 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k361_1_1 : check w361 pick361 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k361_1_2 : check w361 pick361 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w361 pick361 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k361_1_0 k361_1_1
private theorem k361_1_3 : check w361 pick361 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k361_1_4 : check w361 pick361 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k361_1_5 : check w361 pick361 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w361 pick361 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k361_1_3 k361_1_4
private theorem k361_1_6 : check w361 pick361 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w361 pick361 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k361_1_2 k361_1_5
private theorem k361_1_7 : check w361 pick361 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k361_1_8 : check w361 pick361 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k361_1_9 : check w361 pick361 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w361 pick361 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k361_1_7 k361_1_8
private theorem k361_1_10 : check w361 pick361 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k361_1_11 : check w361 pick361 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k361_1_12 : check w361 pick361 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w361 pick361 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k361_1_10 k361_1_11
private theorem k361_1_13 : check w361 pick361 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w361 pick361 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k361_1_9 k361_1_12
private theorem k361_1_14 : check w361 pick361 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w361 pick361 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k361_1_6 k361_1_13
theorem cov361_1 : PA.Covered 1 (OZ.Valid 1 w361.low w361.t w361.y w361.r w361.cap) (P33.root 1) :=
  Night6836Tree.sound w361 pick361 1 t9213 _ k361_1_14
private theorem k361_2_0 : check w361 pick361 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k361_2_1 : check w361 pick361 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k361_2_2 : check w361 pick361 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w361 pick361 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k361_2_0 k361_2_1
theorem cov361_2 : PA.Covered 2 (OZ.Valid 2 w361.low w361.t w361.y w361.r w361.cap) (P33.root 2) :=
  Night6836Tree.sound w361 pick361 2 t9134 _ k361_2_2
theorem cov361_3 : PA.Covered 3 (OZ.Valid 3 w361.low w361.t w361.y w361.r w361.cap) (P33.root 3) :=
  Night6836Tree.sound w361 pick361 3 t564 _ (by decide +kernel)
theorem cov361_4 : PA.Covered 4 (OZ.Valid 4 w361.low w361.t w361.y w361.r w361.cap) (P33.root 4) :=
  Night6836Tree.sound w361 pick361 4 t565 _ (by decide +kernel)
theorem cov361_5 : PA.Covered 5 (OZ.Valid 5 w361.low w361.t w361.y w361.r w361.cap) (P33.root 5) :=
  Night6836Tree.sound w361 pick361 5 t566 _ (by decide +kernel)
theorem cov361_6 : PA.Covered 6 (OZ.Valid 6 w361.low w361.t w361.y w361.r w361.cap) (P33.root 6) :=
  Night6836Tree.sound w361 pick361 6 t567 _ (by decide +kernel)
theorem cov361_7 : PA.Covered 7 (OZ.Valid 7 w361.low w361.t w361.y w361.r w361.cap) (P33.root 7) :=
  Night6836Tree.sound w361 pick361 7 t568 _ (by decide +kernel)
theorem window361 : P33.WindowCount w361 := by
  apply P33.window_count w361 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov361_1
  · exact cov361_2
  · exact cov361_3
  · exact cov361_4
  · exact cov361_5
  · exact cov361_6
  · exact cov361_7
def w362 : P33.Window := ⟨6,43,7492,7446,244534449581558596,29194,15000,5000000,81920000000⟩
def h362_0 : Height w362 := ⟨29194,15000,by decide +kernel⟩
def h362_1 : Height w362 := ⟨34378,12000,by decide +kernel⟩
def h362_2 : Height w362 := ⟨43974,9000,by decide +kernel⟩
def pick362 (cl : ℕ) : Height w362 := if cl<27 then (h362_0) else (if cl<334 then (h362_1) else (h362_2))
private theorem k362_1_0 : check w362 pick362 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k362_1_1 : check w362 pick362 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k362_1_2 : check w362 pick362 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w362 pick362 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k362_1_0 k362_1_1
private theorem k362_1_3 : check w362 pick362 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k362_1_4 : check w362 pick362 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k362_1_5 : check w362 pick362 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w362 pick362 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k362_1_3 k362_1_4
private theorem k362_1_6 : check w362 pick362 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w362 pick362 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k362_1_2 k362_1_5
private theorem k362_1_7 : check w362 pick362 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k362_1_8 : check w362 pick362 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k362_1_9 : check w362 pick362 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w362 pick362 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k362_1_7 k362_1_8
private theorem k362_1_10 : check w362 pick362 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k362_1_11 : check w362 pick362 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k362_1_12 : check w362 pick362 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w362 pick362 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k362_1_10 k362_1_11
private theorem k362_1_13 : check w362 pick362 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w362 pick362 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k362_1_9 k362_1_12
private theorem k362_1_14 : check w362 pick362 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w362 pick362 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k362_1_6 k362_1_13
theorem cov362_1 : PA.Covered 1 (OZ.Valid 1 w362.low w362.t w362.y w362.r w362.cap) (P33.root 1) :=
  Night6836Tree.sound w362 pick362 1 t9213 _ k362_1_14
private theorem k362_2_0 : check w362 pick362 2 t5998 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k362_2_1 : check w362 pick362 2 t9215 ⟨2,7,4,16,2,52,85,450⟩ = true := by decide +kernel
private theorem k362_2_2 : check w362 pick362 2 t9216 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w362 pick362 2 ⟨2,7,4,16,0,52,0,450⟩ 3 84 t5998 t9215 k362_2_0 k362_2_1
theorem cov362_2 : PA.Covered 2 (OZ.Valid 2 w362.low w362.t w362.y w362.r w362.cap) (P33.root 2) :=
  Night6836Tree.sound w362 pick362 2 t9216 _ k362_2_2
theorem cov362_3 : PA.Covered 3 (OZ.Valid 3 w362.low w362.t w362.y w362.r w362.cap) (P33.root 3) :=
  Night6836Tree.sound w362 pick362 3 t564 _ (by decide +kernel)
theorem cov362_4 : PA.Covered 4 (OZ.Valid 4 w362.low w362.t w362.y w362.r w362.cap) (P33.root 4) :=
  Night6836Tree.sound w362 pick362 4 t565 _ (by decide +kernel)
theorem cov362_5 : PA.Covered 5 (OZ.Valid 5 w362.low w362.t w362.y w362.r w362.cap) (P33.root 5) :=
  Night6836Tree.sound w362 pick362 5 t566 _ (by decide +kernel)
theorem cov362_6 : PA.Covered 6 (OZ.Valid 6 w362.low w362.t w362.y w362.r w362.cap) (P33.root 6) :=
  Night6836Tree.sound w362 pick362 6 t567 _ (by decide +kernel)
theorem cov362_7 : PA.Covered 7 (OZ.Valid 7 w362.low w362.t w362.y w362.r w362.cap) (P33.root 7) :=
  Night6836Tree.sound w362 pick362 7 t568 _ (by decide +kernel)
theorem window362 : P33.WindowCount w362 := by
  apply P33.window_count w362 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov362_1
  · exact cov362_2
  · exact cov362_3
  · exact cov362_4
  · exact cov362_5
  · exact cov362_6
  · exact cov362_7
def w363 : P33.Window := ⟨6,44,7445,7398,244630683355784769,30444,15000,5000000,81920000000⟩
def h363_0 : Height w363 := ⟨30444,15000,by decide +kernel⟩
def h363_1 : Height w363 := ⟨35789,12000,by decide +kernel⟩
def h363_2 : Height w363 := ⟨45764,9000,by decide +kernel⟩
def pick363 (cl : ℕ) : Height w363 := if cl<27 then (h363_0) else (if cl<493 then (h363_1) else (h363_2))
private theorem k363_1_0 : check w363 pick363 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k363_1_1 : check w363 pick363 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k363_1_2 : check w363 pick363 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w363 pick363 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k363_1_0 k363_1_1
private theorem k363_1_3 : check w363 pick363 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k363_1_4 : check w363 pick363 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k363_1_5 : check w363 pick363 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w363 pick363 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k363_1_3 k363_1_4
private theorem k363_1_6 : check w363 pick363 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w363 pick363 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k363_1_2 k363_1_5
private theorem k363_1_7 : check w363 pick363 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k363_1_8 : check w363 pick363 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k363_1_9 : check w363 pick363 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w363 pick363 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k363_1_7 k363_1_8
private theorem k363_1_10 : check w363 pick363 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k363_1_11 : check w363 pick363 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k363_1_12 : check w363 pick363 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w363 pick363 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k363_1_10 k363_1_11
private theorem k363_1_13 : check w363 pick363 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w363 pick363 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k363_1_9 k363_1_12
private theorem k363_1_14 : check w363 pick363 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w363 pick363 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k363_1_6 k363_1_13
theorem cov363_1 : PA.Covered 1 (OZ.Valid 1 w363.low w363.t w363.y w363.r w363.cap) (P33.root 1) :=
  Night6836Tree.sound w363 pick363 1 t9213 _ k363_1_14
private theorem k363_2_0 : check w363 pick363 2 t9219 ⟨2,7,4,16,2,52,2,139⟩ = true := by decide +kernel
private theorem k363_2_1 : check w363 pick363 2 t9224 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k363_2_2 : check w363 pick363 2 t9225 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w363 pick363 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9219 t9224 k363_2_0 k363_2_1
theorem cov363_2 : PA.Covered 2 (OZ.Valid 2 w363.low w363.t w363.y w363.r w363.cap) (P33.root 2) :=
  Night6836Tree.sound w363 pick363 2 t9225 _ k363_2_2
theorem cov363_3 : PA.Covered 3 (OZ.Valid 3 w363.low w363.t w363.y w363.r w363.cap) (P33.root 3) :=
  Night6836Tree.sound w363 pick363 3 t564 _ (by decide +kernel)
theorem cov363_4 : PA.Covered 4 (OZ.Valid 4 w363.low w363.t w363.y w363.r w363.cap) (P33.root 4) :=
  Night6836Tree.sound w363 pick363 4 t565 _ (by decide +kernel)
theorem cov363_5 : PA.Covered 5 (OZ.Valid 5 w363.low w363.t w363.y w363.r w363.cap) (P33.root 5) :=
  Night6836Tree.sound w363 pick363 5 t566 _ (by decide +kernel)
theorem cov363_6 : PA.Covered 6 (OZ.Valid 6 w363.low w363.t w363.y w363.r w363.cap) (P33.root 6) :=
  Night6836Tree.sound w363 pick363 6 t567 _ (by decide +kernel)
theorem cov363_7 : PA.Covered 7 (OZ.Valid 7 w363.low w363.t w363.y w363.r w363.cap) (P33.root 7) :=
  Night6836Tree.sound w363 pick363 7 t568 _ (by decide +kernel)
theorem window363 : P33.WindowCount w363 := by
  apply P33.window_count w363 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov363_1
  · exact cov363_2
  · exact cov363_3
  · exact cov363_4
  · exact cov363_5
  · exact cov363_6
  · exact cov363_7
def w364 : P33.Window := ⟨6,45,5944,4945,203590411791369460,46107,23000,5000000,81920000000⟩
def h364_0 : Height w364 := ⟨46107,23000,by decide +kernel⟩
def h364_1 : Height w364 := ⟨52758,19000,by decide +kernel⟩
def h364_2 : Height w364 := ⟨63534,15000,by decide +kernel⟩
def pick364 (cl : ℕ) : Height w364 := if cl<14 then (h364_0) else (if cl<196 then (h364_1) else (h364_2))
private theorem k364_1_0 : check w364 pick364 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k364_1_1 : check w364 pick364 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k364_1_2 : check w364 pick364 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w364 pick364 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k364_1_0 k364_1_1
private theorem k364_1_3 : check w364 pick364 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k364_1_4 : check w364 pick364 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k364_1_5 : check w364 pick364 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w364 pick364 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k364_1_3 k364_1_4
private theorem k364_1_6 : check w364 pick364 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w364 pick364 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k364_1_2 k364_1_5
private theorem k364_1_7 : check w364 pick364 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k364_1_8 : check w364 pick364 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k364_1_9 : check w364 pick364 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w364 pick364 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k364_1_7 k364_1_8
private theorem k364_1_10 : check w364 pick364 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k364_1_11 : check w364 pick364 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k364_1_12 : check w364 pick364 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w364 pick364 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k364_1_10 k364_1_11
private theorem k364_1_13 : check w364 pick364 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w364 pick364 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k364_1_9 k364_1_12
private theorem k364_1_14 : check w364 pick364 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w364 pick364 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k364_1_6 k364_1_13
theorem cov364_1 : PA.Covered 1 (OZ.Valid 1 w364.low w364.t w364.y w364.r w364.cap) (P33.root 1) :=
  Night6836Tree.sound w364 pick364 1 t9213 _ k364_1_14
private theorem k364_2_0 : check w364 pick364 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k364_2_1 : check w364 pick364 2 t9229 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k364_2_2 : check w364 pick364 2 t9230 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w364 pick364 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9229 k364_2_0 k364_2_1
theorem cov364_2 : PA.Covered 2 (OZ.Valid 2 w364.low w364.t w364.y w364.r w364.cap) (P33.root 2) :=
  Night6836Tree.sound w364 pick364 2 t9230 _ k364_2_2
theorem cov364_3 : PA.Covered 3 (OZ.Valid 3 w364.low w364.t w364.y w364.r w364.cap) (P33.root 3) :=
  Night6836Tree.sound w364 pick364 3 t564 _ (by decide +kernel)
theorem cov364_4 : PA.Covered 4 (OZ.Valid 4 w364.low w364.t w364.y w364.r w364.cap) (P33.root 4) :=
  Night6836Tree.sound w364 pick364 4 t565 _ (by decide +kernel)
theorem cov364_5 : PA.Covered 5 (OZ.Valid 5 w364.low w364.t w364.y w364.r w364.cap) (P33.root 5) :=
  Night6836Tree.sound w364 pick364 5 t566 _ (by decide +kernel)
theorem cov364_6 : PA.Covered 6 (OZ.Valid 6 w364.low w364.t w364.y w364.r w364.cap) (P33.root 6) :=
  Night6836Tree.sound w364 pick364 6 t567 _ (by decide +kernel)
theorem cov364_7 : PA.Covered 7 (OZ.Valid 7 w364.low w364.t w364.y w364.r w364.cap) (P33.root 7) :=
  Night6836Tree.sound w364 pick364 7 t2134 _ (by decide +kernel)
theorem window364 : P33.WindowCount w364 := by
  apply P33.window_count w364 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov364_1
  · exact cov364_2
  · exact cov364_3
  · exact cov364_4
  · exact cov364_5
  · exact cov364_6
  · exact cov364_7
def w365 : P33.Window := ⟨6,45,7397,7349,239017958515039072,31723,15000,5000000,81920000000⟩
def h365_0 : Height w365 := ⟨31723,15000,by decide +kernel⟩
def h365_1 : Height w365 := ⟨37237,12000,by decide +kernel⟩
def h365_2 : Height w365 := ⟨47608,9000,by decide +kernel⟩
def pick365 (cl : ℕ) : Height w365 := if cl<25 then (h365_0) else (if cl<644 then (h365_1) else (h365_2))
private theorem k365_1_0 : check w365 pick365 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k365_1_1 : check w365 pick365 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k365_1_2 : check w365 pick365 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w365 pick365 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k365_1_0 k365_1_1
private theorem k365_1_3 : check w365 pick365 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k365_1_4 : check w365 pick365 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k365_1_5 : check w365 pick365 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w365 pick365 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k365_1_3 k365_1_4
private theorem k365_1_6 : check w365 pick365 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w365 pick365 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k365_1_2 k365_1_5
private theorem k365_1_7 : check w365 pick365 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k365_1_8 : check w365 pick365 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k365_1_9 : check w365 pick365 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w365 pick365 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k365_1_7 k365_1_8
private theorem k365_1_10 : check w365 pick365 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k365_1_11 : check w365 pick365 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k365_1_12 : check w365 pick365 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w365 pick365 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k365_1_10 k365_1_11
private theorem k365_1_13 : check w365 pick365 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w365 pick365 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k365_1_9 k365_1_12
private theorem k365_1_14 : check w365 pick365 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w365 pick365 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k365_1_6 k365_1_13
theorem cov365_1 : PA.Covered 1 (OZ.Valid 1 w365.low w365.t w365.y w365.r w365.cap) (P33.root 1) :=
  Night6836Tree.sound w365 pick365 1 t9213 _ k365_1_14
private theorem k365_2_0 : check w365 pick365 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k365_2_1 : check w365 pick365 2 t9249 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k365_2_2 : check w365 pick365 2 t9250 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w365 pick365 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t9239 t9249 k365_2_0 k365_2_1
private theorem k365_2_3 : check w365 pick365 2 t9257 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k365_2_4 : check w365 pick365 2 t9258 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w365 pick365 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t9250 t9257 k365_2_2 k365_2_3
theorem cov365_2 : PA.Covered 2 (OZ.Valid 2 w365.low w365.t w365.y w365.r w365.cap) (P33.root 2) :=
  Night6836Tree.sound w365 pick365 2 t9258 _ k365_2_4
theorem cov365_3 : PA.Covered 3 (OZ.Valid 3 w365.low w365.t w365.y w365.r w365.cap) (P33.root 3) :=
  Night6836Tree.sound w365 pick365 3 t564 _ (by decide +kernel)
theorem cov365_4 : PA.Covered 4 (OZ.Valid 4 w365.low w365.t w365.y w365.r w365.cap) (P33.root 4) :=
  Night6836Tree.sound w365 pick365 4 t565 _ (by decide +kernel)
theorem cov365_5 : PA.Covered 5 (OZ.Valid 5 w365.low w365.t w365.y w365.r w365.cap) (P33.root 5) :=
  Night6836Tree.sound w365 pick365 5 t566 _ (by decide +kernel)
theorem cov365_6 : PA.Covered 6 (OZ.Valid 6 w365.low w365.t w365.y w365.r w365.cap) (P33.root 6) :=
  Night6836Tree.sound w365 pick365 6 t567 _ (by decide +kernel)
theorem cov365_7 : PA.Covered 7 (OZ.Valid 7 w365.low w365.t w365.y w365.r w365.cap) (P33.root 7) :=
  Night6836Tree.sound w365 pick365 7 t568 _ (by decide +kernel)
theorem window365 : P33.WindowCount w365 := by
  apply P33.window_count w365 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov365_1
  · exact cov365_2
  · exact cov365_3
  · exact cov365_4
  · exact cov365_5
  · exact cov365_6
  · exact cov365_7
def w366 : P33.Window := ⟨6,46,5345,4346,203388931724011278,52868,27000,5000000,81920000000⟩
def h366_0 : Height w366 := ⟨52868,27000,by decide +kernel⟩
def h366_1 : Height w366 := ⟨59037,23000,by decide +kernel⟩
def h366_2 : Height w366 := ⟨67937,19000,by decide +kernel⟩
def h366_3 : Height w366 := ⟨83551,15000,by decide +kernel⟩
def pick366 (cl : ℕ) : Height w366 := if cl<70 then (if cl<6 then (h366_0) else (h366_1)) else (if cl<922 then (h366_2) else (h366_3))
private theorem k366_1_0 : check w366 pick366 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k366_1_1 : check w366 pick366 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k366_1_2 : check w366 pick366 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w366 pick366 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k366_1_0 k366_1_1
private theorem k366_1_3 : check w366 pick366 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k366_1_4 : check w366 pick366 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k366_1_5 : check w366 pick366 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w366 pick366 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k366_1_3 k366_1_4
private theorem k366_1_6 : check w366 pick366 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w366 pick366 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k366_1_2 k366_1_5
private theorem k366_1_7 : check w366 pick366 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k366_1_8 : check w366 pick366 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k366_1_9 : check w366 pick366 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w366 pick366 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k366_1_7 k366_1_8
private theorem k366_1_10 : check w366 pick366 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k366_1_11 : check w366 pick366 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k366_1_12 : check w366 pick366 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w366 pick366 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k366_1_10 k366_1_11
private theorem k366_1_13 : check w366 pick366 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w366 pick366 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k366_1_9 k366_1_12
private theorem k366_1_14 : check w366 pick366 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w366 pick366 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k366_1_6 k366_1_13
theorem cov366_1 : PA.Covered 1 (OZ.Valid 1 w366.low w366.t w366.y w366.r w366.cap) (P33.root 1) :=
  Night6836Tree.sound w366 pick366 1 t9130 _ k366_1_14
private theorem k366_2_0 : check w366 pick366 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k366_2_1 : check w366 pick366 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k366_2_2 : check w366 pick366 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w366 pick366 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k366_2_0 k366_2_1
theorem cov366_2 : PA.Covered 2 (OZ.Valid 2 w366.low w366.t w366.y w366.r w366.cap) (P33.root 2) :=
  Night6836Tree.sound w366 pick366 2 t9134 _ k366_2_2
theorem cov366_3 : PA.Covered 3 (OZ.Valid 3 w366.low w366.t w366.y w366.r w366.cap) (P33.root 3) :=
  Night6836Tree.sound w366 pick366 3 t564 _ (by decide +kernel)
theorem cov366_4 : PA.Covered 4 (OZ.Valid 4 w366.low w366.t w366.y w366.r w366.cap) (P33.root 4) :=
  Night6836Tree.sound w366 pick366 4 t565 _ (by decide +kernel)
theorem cov366_5 : PA.Covered 5 (OZ.Valid 5 w366.low w366.t w366.y w366.r w366.cap) (P33.root 5) :=
  Night6836Tree.sound w366 pick366 5 t566 _ (by decide +kernel)
theorem cov366_6 : PA.Covered 6 (OZ.Valid 6 w366.low w366.t w366.y w366.r w366.cap) (P33.root 6) :=
  Night6836Tree.sound w366 pick366 6 t567 _ (by decide +kernel)
theorem cov366_7 : PA.Covered 7 (OZ.Valid 7 w366.low w366.t w366.y w366.r w366.cap) (P33.root 7) :=
  Night6836Tree.sound w366 pick366 7 t2134 _ (by decide +kernel)
theorem window366 : P33.WindowCount w366 := by
  apply P33.window_count w366 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov366_1
  · exact cov366_2
  · exact cov366_3
  · exact cov366_4
  · exact cov366_5
  · exact cov366_6
  · exact cov366_7
def w367 : P33.Window := ⟨6,46,7348,7299,240666320073909936,33033,15000,5000000,81920000000⟩
def h367_0 : Height w367 := ⟨33033,15000,by decide +kernel⟩
def h367_1 : Height w367 := ⟨38724,12000,by decide +kernel⟩
def h367_2 : Height w367 := ⟨49510,9000,by decide +kernel⟩
def pick367 (cl : ℕ) : Height w367 := if cl<28 then (h367_0) else (if cl<922 then (h367_1) else (h367_2))
private theorem k367_1_0 : check w367 pick367 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k367_1_1 : check w367 pick367 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k367_1_2 : check w367 pick367 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w367 pick367 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k367_1_0 k367_1_1
private theorem k367_1_3 : check w367 pick367 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k367_1_4 : check w367 pick367 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k367_1_5 : check w367 pick367 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w367 pick367 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k367_1_3 k367_1_4
private theorem k367_1_6 : check w367 pick367 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w367 pick367 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k367_1_2 k367_1_5
private theorem k367_1_7 : check w367 pick367 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k367_1_8 : check w367 pick367 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k367_1_9 : check w367 pick367 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w367 pick367 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k367_1_7 k367_1_8
private theorem k367_1_10 : check w367 pick367 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k367_1_11 : check w367 pick367 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k367_1_12 : check w367 pick367 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w367 pick367 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k367_1_10 k367_1_11
private theorem k367_1_13 : check w367 pick367 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w367 pick367 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k367_1_9 k367_1_12
private theorem k367_1_14 : check w367 pick367 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w367 pick367 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k367_1_6 k367_1_13
theorem cov367_1 : PA.Covered 1 (OZ.Valid 1 w367.low w367.t w367.y w367.r w367.cap) (P33.root 1) :=
  Night6836Tree.sound w367 pick367 1 t9213 _ k367_1_14
private theorem k367_2_0 : check w367 pick367 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k367_2_1 : check w367 pick367 2 t9249 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k367_2_2 : check w367 pick367 2 t9250 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w367 pick367 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t9239 t9249 k367_2_0 k367_2_1
private theorem k367_2_3 : check w367 pick367 2 t9257 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k367_2_4 : check w367 pick367 2 t9258 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w367 pick367 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t9250 t9257 k367_2_2 k367_2_3
theorem cov367_2 : PA.Covered 2 (OZ.Valid 2 w367.low w367.t w367.y w367.r w367.cap) (P33.root 2) :=
  Night6836Tree.sound w367 pick367 2 t9258 _ k367_2_4
theorem cov367_3 : PA.Covered 3 (OZ.Valid 3 w367.low w367.t w367.y w367.r w367.cap) (P33.root 3) :=
  Night6836Tree.sound w367 pick367 3 t564 _ (by decide +kernel)
theorem cov367_4 : PA.Covered 4 (OZ.Valid 4 w367.low w367.t w367.y w367.r w367.cap) (P33.root 4) :=
  Night6836Tree.sound w367 pick367 4 t565 _ (by decide +kernel)
theorem cov367_5 : PA.Covered 5 (OZ.Valid 5 w367.low w367.t w367.y w367.r w367.cap) (P33.root 5) :=
  Night6836Tree.sound w367 pick367 5 t566 _ (by decide +kernel)
theorem cov367_6 : PA.Covered 6 (OZ.Valid 6 w367.low w367.t w367.y w367.r w367.cap) (P33.root 6) :=
  Night6836Tree.sound w367 pick367 6 t567 _ (by decide +kernel)
theorem cov367_7 : PA.Covered 7 (OZ.Valid 7 w367.low w367.t w367.y w367.r w367.cap) (P33.root 7) :=
  Night6836Tree.sound w367 pick367 7 t568 _ (by decide +kernel)
theorem window367 : P33.WindowCount w367 := by
  apply P33.window_count w367 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov367_1
  · exact cov367_2
  · exact cov367_3
  · exact cov367_4
  · exact cov367_5
  · exact cov367_6
  · exact cov367_7
def w368 : P33.Window := ⟨6,47,5346,4347,203705994013959430,54387,27000,5000000,81920000000⟩
def h368_0 : Height w368 := ⟨54387,27000,by decide +kernel⟩
def h368_1 : Height w368 := ⟨60648,23000,by decide +kernel⟩
def h368_2 : Height w368 := ⟨69702,19000,by decide +kernel⟩
def h368_3 : Height w368 := ⟨85613,15000,by decide +kernel⟩
def pick368 (cl : ℕ) : Height w368 := if cl<83 then (if cl<10 then (h368_0) else (h368_1)) else (if cl<922 then (h368_2) else (h368_3))
private theorem k368_1_0 : check w368 pick368 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k368_1_1 : check w368 pick368 1 t5141 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k368_1_2 : check w368 pick368 1 t9137 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w368 pick368 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t5141 k368_1_0 k368_1_1
private theorem k368_1_3 : check w368 pick368 1 t9261 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k368_1_4 : check w368 pick368 1 t9263 ⟨1,7,2,16,1,52,118,152⟩ = true := by decide +kernel
private theorem k368_1_5 : check w368 pick368 1 t9264 ⟨1,7,2,16,1,52,84,152⟩ = true := glue w368 pick368 1 ⟨1,7,2,16,1,52,84,152⟩ 3 117 t9261 t9263 k368_1_3 k368_1_4
private theorem k368_1_6 : check w368 pick368 1 t9265 ⟨1,7,2,16,1,52,1,152⟩ = true := glue w368 pick368 1 ⟨1,7,2,16,1,52,1,152⟩ 3 83 t9137 t9264 k368_1_2 k368_1_5
private theorem k368_1_7 : check w368 pick368 1 t9266 ⟨1,7,2,16,1,52,153,179⟩ = true := by decide +kernel
private theorem k368_1_8 : check w368 pick368 1 t2374 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k368_1_9 : check w368 pick368 1 t9267 ⟨1,7,2,16,1,52,153,206⟩ = true := glue w368 pick368 1 ⟨1,7,2,16,1,52,153,206⟩ 3 179 t9266 t2374 k368_1_7 k368_1_8
private theorem k368_1_10 : check w368 pick368 1 t2385 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k368_1_11 : check w368 pick368 1 t9150 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k368_1_12 : check w368 pick368 1 t9183 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w368 pick368 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t2385 t9150 k368_1_10 k368_1_11
private theorem k368_1_13 : check w368 pick368 1 t9268 ⟨1,7,2,16,1,52,153,450⟩ = true := glue w368 pick368 1 ⟨1,7,2,16,1,52,153,450⟩ 3 206 t9267 t9183 k368_1_9 k368_1_12
private theorem k368_1_14 : check w368 pick368 1 t9269 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w368 pick368 1 ⟨1,7,2,16,0,52,0,450⟩ 3 152 t9265 t9268 k368_1_6 k368_1_13
theorem cov368_1 : PA.Covered 1 (OZ.Valid 1 w368.low w368.t w368.y w368.r w368.cap) (P33.root 1) :=
  Night6836Tree.sound w368 pick368 1 t9269 _ k368_1_14
private theorem k368_2_0 : check w368 pick368 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k368_2_1 : check w368 pick368 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k368_2_2 : check w368 pick368 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w368 pick368 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k368_2_0 k368_2_1
theorem cov368_2 : PA.Covered 2 (OZ.Valid 2 w368.low w368.t w368.y w368.r w368.cap) (P33.root 2) :=
  Night6836Tree.sound w368 pick368 2 t9134 _ k368_2_2
theorem cov368_3 : PA.Covered 3 (OZ.Valid 3 w368.low w368.t w368.y w368.r w368.cap) (P33.root 3) :=
  Night6836Tree.sound w368 pick368 3 t564 _ (by decide +kernel)
theorem cov368_4 : PA.Covered 4 (OZ.Valid 4 w368.low w368.t w368.y w368.r w368.cap) (P33.root 4) :=
  Night6836Tree.sound w368 pick368 4 t565 _ (by decide +kernel)
theorem cov368_5 : PA.Covered 5 (OZ.Valid 5 w368.low w368.t w368.y w368.r w368.cap) (P33.root 5) :=
  Night6836Tree.sound w368 pick368 5 t566 _ (by decide +kernel)
theorem cov368_6 : PA.Covered 6 (OZ.Valid 6 w368.low w368.t w368.y w368.r w368.cap) (P33.root 6) :=
  Night6836Tree.sound w368 pick368 6 t567 _ (by decide +kernel)
theorem cov368_7 : PA.Covered 7 (OZ.Valid 7 w368.low w368.t w368.y w368.r w368.cap) (P33.root 7) :=
  Night6836Tree.sound w368 pick368 7 t2134 _ (by decide +kernel)
theorem window368 : P33.WindowCount w368 := by
  apply P33.window_count w368 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov368_1
  · exact cov368_2
  · exact cov368_3
  · exact cov368_4
  · exact cov368_5
  · exact cov368_6
  · exact cov368_7
def w369 : P33.Window := ⟨6,47,7298,7248,242237590869695267,30390,18000,5000000,81920000000⟩
def h369_0 : Height w369 := ⟨30390,18000,by decide +kernel⟩
def h369_1 : Height w369 := ⟨34377,15000,by decide +kernel⟩
def h369_2 : Height w369 := ⟨40251,12000,by decide +kernel⟩
def h369_3 : Height w369 := ⟨51474,9000,by decide +kernel⟩
def pick369 (cl : ℕ) : Height w369 := if cl<36 then (if cl<2 then (h369_0) else (h369_1)) else (if cl<922 then (h369_2) else (h369_3))
private theorem k369_1_0 : check w369 pick369 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k369_1_1 : check w369 pick369 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k369_1_2 : check w369 pick369 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w369 pick369 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k369_1_0 k369_1_1
private theorem k369_1_3 : check w369 pick369 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k369_1_4 : check w369 pick369 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k369_1_5 : check w369 pick369 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w369 pick369 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k369_1_3 k369_1_4
private theorem k369_1_6 : check w369 pick369 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w369 pick369 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k369_1_2 k369_1_5
private theorem k369_1_7 : check w369 pick369 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k369_1_8 : check w369 pick369 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k369_1_9 : check w369 pick369 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w369 pick369 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k369_1_7 k369_1_8
private theorem k369_1_10 : check w369 pick369 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k369_1_11 : check w369 pick369 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k369_1_12 : check w369 pick369 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w369 pick369 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k369_1_10 k369_1_11
private theorem k369_1_13 : check w369 pick369 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w369 pick369 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k369_1_9 k369_1_12
private theorem k369_1_14 : check w369 pick369 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w369 pick369 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k369_1_6 k369_1_13
theorem cov369_1 : PA.Covered 1 (OZ.Valid 1 w369.low w369.t w369.y w369.r w369.cap) (P33.root 1) :=
  Night6836Tree.sound w369 pick369 1 t9213 _ k369_1_14
private theorem k369_2_0 : check w369 pick369 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k369_2_1 : check w369 pick369 2 t9249 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k369_2_2 : check w369 pick369 2 t9250 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w369 pick369 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t9239 t9249 k369_2_0 k369_2_1
private theorem k369_2_3 : check w369 pick369 2 t9257 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k369_2_4 : check w369 pick369 2 t9258 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w369 pick369 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t9250 t9257 k369_2_2 k369_2_3
theorem cov369_2 : PA.Covered 2 (OZ.Valid 2 w369.low w369.t w369.y w369.r w369.cap) (P33.root 2) :=
  Night6836Tree.sound w369 pick369 2 t9258 _ k369_2_4
theorem cov369_3 : PA.Covered 3 (OZ.Valid 3 w369.low w369.t w369.y w369.r w369.cap) (P33.root 3) :=
  Night6836Tree.sound w369 pick369 3 t564 _ (by decide +kernel)
theorem cov369_4 : PA.Covered 4 (OZ.Valid 4 w369.low w369.t w369.y w369.r w369.cap) (P33.root 4) :=
  Night6836Tree.sound w369 pick369 4 t565 _ (by decide +kernel)
theorem cov369_5 : PA.Covered 5 (OZ.Valid 5 w369.low w369.t w369.y w369.r w369.cap) (P33.root 5) :=
  Night6836Tree.sound w369 pick369 5 t566 _ (by decide +kernel)
theorem cov369_6 : PA.Covered 6 (OZ.Valid 6 w369.low w369.t w369.y w369.r w369.cap) (P33.root 6) :=
  Night6836Tree.sound w369 pick369 6 t567 _ (by decide +kernel)
theorem cov369_7 : PA.Covered 7 (OZ.Valid 7 w369.low w369.t w369.y w369.r w369.cap) (P33.root 7) :=
  Night6836Tree.sound w369 pick369 7 t568 _ (by decide +kernel)
theorem window369 : P33.WindowCount w369 := by
  apply P33.window_count w369 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov369_1
  · exact cov369_2
  · exact cov369_3
  · exact cov369_4
  · exact cov369_5
  · exact cov369_6
  · exact cov369_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w370 : P33.Window := ⟨6,48,5347,4348,203837465958095553,55905,27000,5000000,81920000000⟩
def h370_0 : Height w370 := ⟨55905,27000,by decide +kernel⟩
def h370_1 : Height w370 := ⟨62259,23000,by decide +kernel⟩
def h370_2 : Height w370 := ⟨71465,19000,by decide +kernel⟩
def h370_3 : Height w370 := ⟨87672,15000,by decide +kernel⟩
def pick370 (cl : ℕ) : Height w370 := if cl<83 then (if cl<10 then (h370_0) else (h370_1)) else (if cl<922 then (h370_2) else (h370_3))
private theorem k370_1_0 : check w370 pick370 1 t9154 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k370_1_1 : check w370 pick370 1 t5141 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k370_1_2 : check w370 pick370 1 t9155 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w370 pick370 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t9154 t5141 k370_1_0 k370_1_1
private theorem k370_1_3 : check w370 pick370 1 t9272 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k370_1_4 : check w370 pick370 1 t9273 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w370 pick370 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9155 t9272 k370_1_2 k370_1_3
private theorem k370_1_5 : check w370 pick370 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k370_1_6 : check w370 pick370 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k370_1_7 : check w370 pick370 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w370 pick370 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k370_1_5 k370_1_6
private theorem k370_1_8 : check w370 pick370 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k370_1_9 : check w370 pick370 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k370_1_10 : check w370 pick370 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w370 pick370 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k370_1_8 k370_1_9
private theorem k370_1_11 : check w370 pick370 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w370 pick370 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k370_1_7 k370_1_10
private theorem k370_1_12 : check w370 pick370 1 t9274 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w370 pick370 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9273 t9212 k370_1_4 k370_1_11
theorem cov370_1 : PA.Covered 1 (OZ.Valid 1 w370.low w370.t w370.y w370.r w370.cap) (P33.root 1) :=
  Night6836Tree.sound w370 pick370 1 t9274 _ k370_1_12
private theorem k370_2_0 : check w370 pick370 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k370_2_1 : check w370 pick370 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k370_2_2 : check w370 pick370 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w370 pick370 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k370_2_0 k370_2_1
theorem cov370_2 : PA.Covered 2 (OZ.Valid 2 w370.low w370.t w370.y w370.r w370.cap) (P33.root 2) :=
  Night6836Tree.sound w370 pick370 2 t9134 _ k370_2_2
theorem cov370_3 : PA.Covered 3 (OZ.Valid 3 w370.low w370.t w370.y w370.r w370.cap) (P33.root 3) :=
  Night6836Tree.sound w370 pick370 3 t564 _ (by decide +kernel)
theorem cov370_4 : PA.Covered 4 (OZ.Valid 4 w370.low w370.t w370.y w370.r w370.cap) (P33.root 4) :=
  Night6836Tree.sound w370 pick370 4 t565 _ (by decide +kernel)
theorem cov370_5 : PA.Covered 5 (OZ.Valid 5 w370.low w370.t w370.y w370.r w370.cap) (P33.root 5) :=
  Night6836Tree.sound w370 pick370 5 t566 _ (by decide +kernel)
theorem cov370_6 : PA.Covered 6 (OZ.Valid 6 w370.low w370.t w370.y w370.r w370.cap) (P33.root 6) :=
  Night6836Tree.sound w370 pick370 6 t567 _ (by decide +kernel)
theorem cov370_7 : PA.Covered 7 (OZ.Valid 7 w370.low w370.t w370.y w370.r w370.cap) (P33.root 7) :=
  Night6836Tree.sound w370 pick370 7 t2134 _ (by decide +kernel)
theorem window370 : P33.WindowCount w370 := by
  apply P33.window_count w370 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov370_1
  · exact cov370_2
  · exact cov370_3
  · exact cov370_4
  · exact cov370_5
  · exact cov370_6
  · exact cov370_7
def w371 : P33.Window := ⟨6,48,7247,6788,243730442312418833,34895,18000,5000000,81920000000⟩
def h371_0 : Height w371 := ⟨34895,18000,by decide +kernel⟩
def h371_1 : Height w371 := ⟨39428,15000,by decide +kernel⟩
def h371_2 : Height w371 := ⟨46348,12000,by decide +kernel⟩
def pick371 (cl : ℕ) : Height w371 := if cl<6 then (h371_0) else (if cl<90 then (h371_1) else (h371_2))
private theorem k371_1_0 : check w371 pick371 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k371_1_1 : check w371 pick371 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k371_1_2 : check w371 pick371 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w371 pick371 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k371_1_0 k371_1_1
private theorem k371_1_3 : check w371 pick371 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k371_1_4 : check w371 pick371 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k371_1_5 : check w371 pick371 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w371 pick371 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k371_1_3 k371_1_4
private theorem k371_1_6 : check w371 pick371 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w371 pick371 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k371_1_2 k371_1_5
private theorem k371_1_7 : check w371 pick371 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k371_1_8 : check w371 pick371 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k371_1_9 : check w371 pick371 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w371 pick371 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k371_1_7 k371_1_8
private theorem k371_1_10 : check w371 pick371 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k371_1_11 : check w371 pick371 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k371_1_12 : check w371 pick371 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w371 pick371 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k371_1_10 k371_1_11
private theorem k371_1_13 : check w371 pick371 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w371 pick371 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k371_1_9 k371_1_12
private theorem k371_1_14 : check w371 pick371 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w371 pick371 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k371_1_6 k371_1_13
theorem cov371_1 : PA.Covered 1 (OZ.Valid 1 w371.low w371.t w371.y w371.r w371.cap) (P33.root 1) :=
  Night6836Tree.sound w371 pick371 1 t9213 _ k371_1_14
private theorem k371_2_0 : check w371 pick371 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k371_2_1 : check w371 pick371 2 t9249 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k371_2_2 : check w371 pick371 2 t9250 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w371 pick371 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t9239 t9249 k371_2_0 k371_2_1
private theorem k371_2_3 : check w371 pick371 2 t9257 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k371_2_4 : check w371 pick371 2 t9258 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w371 pick371 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t9250 t9257 k371_2_2 k371_2_3
theorem cov371_2 : PA.Covered 2 (OZ.Valid 2 w371.low w371.t w371.y w371.r w371.cap) (P33.root 2) :=
  Night6836Tree.sound w371 pick371 2 t9258 _ k371_2_4
theorem cov371_3 : PA.Covered 3 (OZ.Valid 3 w371.low w371.t w371.y w371.r w371.cap) (P33.root 3) :=
  Night6836Tree.sound w371 pick371 3 t564 _ (by decide +kernel)
theorem cov371_4 : PA.Covered 4 (OZ.Valid 4 w371.low w371.t w371.y w371.r w371.cap) (P33.root 4) :=
  Night6836Tree.sound w371 pick371 4 t565 _ (by decide +kernel)
theorem cov371_5 : PA.Covered 5 (OZ.Valid 5 w371.low w371.t w371.y w371.r w371.cap) (P33.root 5) :=
  Night6836Tree.sound w371 pick371 5 t566 _ (by decide +kernel)
theorem cov371_6 : PA.Covered 6 (OZ.Valid 6 w371.low w371.t w371.y w371.r w371.cap) (P33.root 6) :=
  Night6836Tree.sound w371 pick371 6 t567 _ (by decide +kernel)
theorem cov371_7 : PA.Covered 7 (OZ.Valid 7 w371.low w371.t w371.y w371.r w371.cap) (P33.root 7) :=
  Night6836Tree.sound w371 pick371 7 t568 _ (by decide +kernel)
theorem window371 : P33.WindowCount w371 := by
  apply P33.window_count w371 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov371_1
  · exact cov371_2
  · exact cov371_3
  · exact cov371_4
  · exact cov371_5
  · exact cov371_6
  · exact cov371_7
def w372 : P33.Window := ⟨6,49,4448,3449,200333695066832548,71073,35000,5000000,81920000000⟩
def h372_0 : Height w372 := ⟨71073,35000,by decide +kernel⟩
def h372_1 : Height w372 := ⟨76965,31000,by decide +kernel⟩
def h372_2 : Height w372 := ⟨84540,27000,by decide +kernel⟩
def h372_3 : Height w372 := ⟨95193,23000,by decide +kernel⟩
def pick372 (cl : ℕ) : Height w372 := if cl<32 then (if cl<5 then (h372_0) else (h372_1)) else (if cl<182 then (h372_2) else (h372_3))
private theorem k372_1_0 : check w372 pick372 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k372_1_1 : check w372 pick372 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k372_1_2 : check w372 pick372 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w372 pick372 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k372_1_0 k372_1_1
private theorem k372_1_3 : check w372 pick372 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k372_1_4 : check w372 pick372 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k372_1_5 : check w372 pick372 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w372 pick372 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k372_1_3 k372_1_4
private theorem k372_1_6 : check w372 pick372 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w372 pick372 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k372_1_2 k372_1_5
private theorem k372_1_7 : check w372 pick372 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k372_1_8 : check w372 pick372 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k372_1_9 : check w372 pick372 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w372 pick372 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k372_1_7 k372_1_8
private theorem k372_1_10 : check w372 pick372 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k372_1_11 : check w372 pick372 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k372_1_12 : check w372 pick372 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w372 pick372 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k372_1_10 k372_1_11
private theorem k372_1_13 : check w372 pick372 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w372 pick372 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k372_1_9 k372_1_12
private theorem k372_1_14 : check w372 pick372 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w372 pick372 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k372_1_6 k372_1_13
theorem cov372_1 : PA.Covered 1 (OZ.Valid 1 w372.low w372.t w372.y w372.r w372.cap) (P33.root 1) :=
  Night6836Tree.sound w372 pick372 1 t9130 _ k372_1_14
theorem cov372_2 : PA.Covered 2 (OZ.Valid 2 w372.low w372.t w372.y w372.r w372.cap) (P33.root 2) :=
  Night6836Tree.sound w372 pick372 2 t9276 _ (by decide +kernel)
theorem cov372_3 : PA.Covered 3 (OZ.Valid 3 w372.low w372.t w372.y w372.r w372.cap) (P33.root 3) :=
  Night6836Tree.sound w372 pick372 3 t564 _ (by decide +kernel)
theorem cov372_4 : PA.Covered 4 (OZ.Valid 4 w372.low w372.t w372.y w372.r w372.cap) (P33.root 4) :=
  Night6836Tree.sound w372 pick372 4 t565 _ (by decide +kernel)
theorem cov372_5 : PA.Covered 5 (OZ.Valid 5 w372.low w372.t w372.y w372.r w372.cap) (P33.root 5) :=
  Night6836Tree.sound w372 pick372 5 t566 _ (by decide +kernel)
theorem cov372_6 : PA.Covered 6 (OZ.Valid 6 w372.low w372.t w372.y w372.r w372.cap) (P33.root 6) :=
  Night6836Tree.sound w372 pick372 6 t567 _ (by decide +kernel)
theorem cov372_7 : PA.Covered 7 (OZ.Valid 7 w372.low w372.t w372.y w372.r w372.cap) (P33.root 7) :=
  Night6836Tree.sound w372 pick372 7 t2134 _ (by decide +kernel)
theorem window372 : P33.WindowCount w372 := by
  apply P33.window_count w372 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov372_1
  · exact cov372_2
  · exact cov372_3
  · exact cov372_4
  · exact cov372_5
  · exact cov372_6
  · exact cov372_7
def w373 : P33.Window := ⟨6,49,5348,4349,203990063567842382,57421,27000,5000000,81920000000⟩
def h373_0 : Height w373 := ⟨57421,27000,by decide +kernel⟩
def h373_1 : Height w373 := ⟨63868,23000,by decide +kernel⟩
def h373_2 : Height w373 := ⟨73226,19000,by decide +kernel⟩
def pick373 (cl : ℕ) : Height w373 := if cl<10 then (h373_0) else (if cl<95 then (h373_1) else (h373_2))
private theorem k373_1_0 : check w373 pick373 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k373_1_1 : check w373 pick373 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k373_1_2 : check w373 pick373 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w373 pick373 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k373_1_0 k373_1_1
private theorem k373_1_3 : check w373 pick373 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k373_1_4 : check w373 pick373 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k373_1_5 : check w373 pick373 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w373 pick373 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k373_1_3 k373_1_4
private theorem k373_1_6 : check w373 pick373 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w373 pick373 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k373_1_2 k373_1_5
private theorem k373_1_7 : check w373 pick373 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k373_1_8 : check w373 pick373 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k373_1_9 : check w373 pick373 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w373 pick373 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k373_1_7 k373_1_8
private theorem k373_1_10 : check w373 pick373 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k373_1_11 : check w373 pick373 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k373_1_12 : check w373 pick373 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w373 pick373 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k373_1_10 k373_1_11
private theorem k373_1_13 : check w373 pick373 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w373 pick373 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k373_1_9 k373_1_12
private theorem k373_1_14 : check w373 pick373 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w373 pick373 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k373_1_6 k373_1_13
theorem cov373_1 : PA.Covered 1 (OZ.Valid 1 w373.low w373.t w373.y w373.r w373.cap) (P33.root 1) :=
  Night6836Tree.sound w373 pick373 1 t9213 _ k373_1_14
private theorem k373_2_0 : check w373 pick373 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k373_2_1 : check w373 pick373 2 t9278 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k373_2_2 : check w373 pick373 2 t9279 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w373 pick373 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9278 k373_2_0 k373_2_1
theorem cov373_2 : PA.Covered 2 (OZ.Valid 2 w373.low w373.t w373.y w373.r w373.cap) (P33.root 2) :=
  Night6836Tree.sound w373 pick373 2 t9279 _ k373_2_2
theorem cov373_3 : PA.Covered 3 (OZ.Valid 3 w373.low w373.t w373.y w373.r w373.cap) (P33.root 3) :=
  Night6836Tree.sound w373 pick373 3 t564 _ (by decide +kernel)
theorem cov373_4 : PA.Covered 4 (OZ.Valid 4 w373.low w373.t w373.y w373.r w373.cap) (P33.root 4) :=
  Night6836Tree.sound w373 pick373 4 t565 _ (by decide +kernel)
theorem cov373_5 : PA.Covered 5 (OZ.Valid 5 w373.low w373.t w373.y w373.r w373.cap) (P33.root 5) :=
  Night6836Tree.sound w373 pick373 5 t566 _ (by decide +kernel)
theorem cov373_6 : PA.Covered 6 (OZ.Valid 6 w373.low w373.t w373.y w373.r w373.cap) (P33.root 6) :=
  Night6836Tree.sound w373 pick373 6 t567 _ (by decide +kernel)
theorem cov373_7 : PA.Covered 7 (OZ.Valid 7 w373.low w373.t w373.y w373.r w373.cap) (P33.root 7) :=
  Night6836Tree.sound w373 pick373 7 t2134 _ (by decide +kernel)
theorem window373 : P33.WindowCount w373 := by
  apply P33.window_count w373 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov373_1
  · exact cov373_2
  · exact cov373_3
  · exact cov373_4
  · exact cov373_5
  · exact cov373_6
  · exact cov373_7
def w374 : P33.Window := ⟨6,49,7196,7144,245177678836750885,32959,18000,5000000,81920000000⟩
def h374_0 : Height w374 := ⟨32959,18000,by decide +kernel⟩
def h374_1 : Height w374 := ⟨37159,15000,by decide +kernel⟩
def h374_2 : Height w374 := ⟨43426,12000,by decide +kernel⟩
def h374_3 : Height w374 := ⟨55588,9000,by decide +kernel⟩
def pick374 (cl : ℕ) : Height w374 := if cl<46 then (if cl<4 then (h374_0) else (h374_1)) else (if cl<922 then (h374_2) else (h374_3))
private theorem k374_1_0 : check w374 pick374 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k374_1_1 : check w374 pick374 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k374_1_2 : check w374 pick374 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w374 pick374 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k374_1_0 k374_1_1
private theorem k374_1_3 : check w374 pick374 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k374_1_4 : check w374 pick374 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k374_1_5 : check w374 pick374 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w374 pick374 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k374_1_3 k374_1_4
private theorem k374_1_6 : check w374 pick374 1 t9208 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w374 pick374 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9207 k374_1_2 k374_1_5
private theorem k374_1_7 : check w374 pick374 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k374_1_8 : check w374 pick374 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k374_1_9 : check w374 pick374 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w374 pick374 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k374_1_7 k374_1_8
private theorem k374_1_10 : check w374 pick374 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k374_1_11 : check w374 pick374 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k374_1_12 : check w374 pick374 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w374 pick374 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k374_1_10 k374_1_11
private theorem k374_1_13 : check w374 pick374 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w374 pick374 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k374_1_9 k374_1_12
private theorem k374_1_14 : check w374 pick374 1 t9213 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w374 pick374 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9208 t9212 k374_1_6 k374_1_13
theorem cov374_1 : PA.Covered 1 (OZ.Valid 1 w374.low w374.t w374.y w374.r w374.cap) (P33.root 1) :=
  Night6836Tree.sound w374 pick374 1 t9213 _ k374_1_14
private theorem k374_2_0 : check w374 pick374 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k374_2_1 : check w374 pick374 2 t9249 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k374_2_2 : check w374 pick374 2 t9250 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w374 pick374 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t9239 t9249 k374_2_0 k374_2_1
private theorem k374_2_3 : check w374 pick374 2 t9254 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k374_2_4 : check w374 pick374 2 t9280 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k374_2_5 : check w374 pick374 2 t9281 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w374 pick374 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t9254 t9280 k374_2_3 k374_2_4
private theorem k374_2_6 : check w374 pick374 2 t9282 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w374 pick374 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t9250 t9281 k374_2_2 k374_2_5
theorem cov374_2 : PA.Covered 2 (OZ.Valid 2 w374.low w374.t w374.y w374.r w374.cap) (P33.root 2) :=
  Night6836Tree.sound w374 pick374 2 t9282 _ k374_2_6
theorem cov374_3 : PA.Covered 3 (OZ.Valid 3 w374.low w374.t w374.y w374.r w374.cap) (P33.root 3) :=
  Night6836Tree.sound w374 pick374 3 t564 _ (by decide +kernel)
theorem cov374_4 : PA.Covered 4 (OZ.Valid 4 w374.low w374.t w374.y w374.r w374.cap) (P33.root 4) :=
  Night6836Tree.sound w374 pick374 4 t565 _ (by decide +kernel)
theorem cov374_5 : PA.Covered 5 (OZ.Valid 5 w374.low w374.t w374.y w374.r w374.cap) (P33.root 5) :=
  Night6836Tree.sound w374 pick374 5 t566 _ (by decide +kernel)
theorem cov374_6 : PA.Covered 6 (OZ.Valid 6 w374.low w374.t w374.y w374.r w374.cap) (P33.root 6) :=
  Night6836Tree.sound w374 pick374 6 t567 _ (by decide +kernel)
theorem cov374_7 : PA.Covered 7 (OZ.Valid 7 w374.low w374.t w374.y w374.r w374.cap) (P33.root 7) :=
  Night6836Tree.sound w374 pick374 7 t568 _ (by decide +kernel)
theorem window374 : P33.WindowCount w374 := by
  apply P33.window_count w374 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov374_1
  · exact cov374_2
  · exact cov374_3
  · exact cov374_4
  · exact cov374_5
  · exact cov374_6
  · exact cov374_7
def w375 : P33.Window := ⟨6,50,4449,3450,203164428774112259,72958,35000,5000000,81920000000⟩
def h375_0 : Height w375 := ⟨72958,35000,by decide +kernel⟩
def h375_1 : Height w375 := ⟨78930,31000,by decide +kernel⟩
def h375_2 : Height w375 := ⟨86619,27000,by decide +kernel⟩
def h375_3 : Height w375 := ⟨97447,23000,by decide +kernel⟩
def pick375 (cl : ℕ) : Height w375 := if cl<32 then (if cl<5 then (h375_0) else (h375_1)) else (if cl<197 then (h375_2) else (h375_3))
private theorem k375_1_0 : check w375 pick375 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k375_1_1 : check w375 pick375 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k375_1_2 : check w375 pick375 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w375 pick375 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k375_1_0 k375_1_1
private theorem k375_1_3 : check w375 pick375 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k375_1_4 : check w375 pick375 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k375_1_5 : check w375 pick375 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w375 pick375 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k375_1_3 k375_1_4
private theorem k375_1_6 : check w375 pick375 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w375 pick375 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k375_1_2 k375_1_5
private theorem k375_1_7 : check w375 pick375 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k375_1_8 : check w375 pick375 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k375_1_9 : check w375 pick375 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w375 pick375 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k375_1_7 k375_1_8
private theorem k375_1_10 : check w375 pick375 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k375_1_11 : check w375 pick375 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k375_1_12 : check w375 pick375 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w375 pick375 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k375_1_10 k375_1_11
private theorem k375_1_13 : check w375 pick375 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w375 pick375 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k375_1_9 k375_1_12
private theorem k375_1_14 : check w375 pick375 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w375 pick375 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k375_1_6 k375_1_13
theorem cov375_1 : PA.Covered 1 (OZ.Valid 1 w375.low w375.t w375.y w375.r w375.cap) (P33.root 1) :=
  Night6836Tree.sound w375 pick375 1 t9130 _ k375_1_14
theorem cov375_2 : PA.Covered 2 (OZ.Valid 2 w375.low w375.t w375.y w375.r w375.cap) (P33.root 2) :=
  Night6836Tree.sound w375 pick375 2 t9276 _ (by decide +kernel)
theorem cov375_3 : PA.Covered 3 (OZ.Valid 3 w375.low w375.t w375.y w375.r w375.cap) (P33.root 3) :=
  Night6836Tree.sound w375 pick375 3 t564 _ (by decide +kernel)
theorem cov375_4 : PA.Covered 4 (OZ.Valid 4 w375.low w375.t w375.y w375.r w375.cap) (P33.root 4) :=
  Night6836Tree.sound w375 pick375 4 t565 _ (by decide +kernel)
theorem cov375_5 : PA.Covered 5 (OZ.Valid 5 w375.low w375.t w375.y w375.r w375.cap) (P33.root 5) :=
  Night6836Tree.sound w375 pick375 5 t566 _ (by decide +kernel)
theorem cov375_6 : PA.Covered 6 (OZ.Valid 6 w375.low w375.t w375.y w375.r w375.cap) (P33.root 6) :=
  Night6836Tree.sound w375 pick375 6 t567 _ (by decide +kernel)
theorem cov375_7 : PA.Covered 7 (OZ.Valid 7 w375.low w375.t w375.y w375.r w375.cap) (P33.root 7) :=
  Night6836Tree.sound w375 pick375 7 t2134 _ (by decide +kernel)
theorem window375 : P33.WindowCount w375 := by
  apply P33.window_count w375 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov375_1
  · exact cov375_2
  · exact cov375_3
  · exact cov375_4
  · exact cov375_5
  · exact cov375_6
  · exact cov375_7
def w376 : P33.Window := ⟨6,50,7143,7090,244770683081042711,34296,18000,5000000,81920000000⟩
def h376_0 : Height w376 := ⟨34296,18000,by decide +kernel⟩
def h376_1 : Height w376 := ⟨38611,15000,by decide +kernel⟩
def h376_2 : Height w376 := ⟨45088,12000,by decide +kernel⟩
def h376_3 : Height w376 := ⟨57760,9000,by decide +kernel⟩
def pick376 (cl : ℕ) : Height w376 := if cl<60 then (if cl<4 then (h376_0) else (h376_1)) else (if cl<989 then (h376_2) else (h376_3))
private theorem k376_1_0 : check w376 pick376 1 t9283 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k376_1_1 : check w376 pick376 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k376_1_2 : check w376 pick376 1 t9284 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w376 pick376 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9283 t9190 k376_1_0 k376_1_1
private theorem k376_1_3 : check w376 pick376 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k376_1_4 : check w376 pick376 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k376_1_5 : check w376 pick376 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w376 pick376 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k376_1_3 k376_1_4
private theorem k376_1_6 : check w376 pick376 1 t9285 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w376 pick376 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9284 t9207 k376_1_2 k376_1_5
private theorem k376_1_7 : check w376 pick376 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k376_1_8 : check w376 pick376 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k376_1_9 : check w376 pick376 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w376 pick376 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k376_1_7 k376_1_8
private theorem k376_1_10 : check w376 pick376 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k376_1_11 : check w376 pick376 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k376_1_12 : check w376 pick376 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w376 pick376 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k376_1_10 k376_1_11
private theorem k376_1_13 : check w376 pick376 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w376 pick376 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k376_1_9 k376_1_12
private theorem k376_1_14 : check w376 pick376 1 t9286 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w376 pick376 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9285 t9212 k376_1_6 k376_1_13
theorem cov376_1 : PA.Covered 1 (OZ.Valid 1 w376.low w376.t w376.y w376.r w376.cap) (P33.root 1) :=
  Night6836Tree.sound w376 pick376 1 t9286 _ k376_1_14
private theorem k376_2_0 : check w376 pick376 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k376_2_1 : check w376 pick376 2 t9249 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k376_2_2 : check w376 pick376 2 t9250 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w376 pick376 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t9239 t9249 k376_2_0 k376_2_1
private theorem k376_2_3 : check w376 pick376 2 t9288 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k376_2_4 : check w376 pick376 2 t4902 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k376_2_5 : check w376 pick376 2 t9289 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w376 pick376 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t9288 t4902 k376_2_3 k376_2_4
private theorem k376_2_6 : check w376 pick376 2 t9290 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w376 pick376 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t9250 t9289 k376_2_2 k376_2_5
theorem cov376_2 : PA.Covered 2 (OZ.Valid 2 w376.low w376.t w376.y w376.r w376.cap) (P33.root 2) :=
  Night6836Tree.sound w376 pick376 2 t9290 _ k376_2_6
theorem cov376_3 : PA.Covered 3 (OZ.Valid 3 w376.low w376.t w376.y w376.r w376.cap) (P33.root 3) :=
  Night6836Tree.sound w376 pick376 3 t564 _ (by decide +kernel)
theorem cov376_4 : PA.Covered 4 (OZ.Valid 4 w376.low w376.t w376.y w376.r w376.cap) (P33.root 4) :=
  Night6836Tree.sound w376 pick376 4 t565 _ (by decide +kernel)
theorem cov376_5 : PA.Covered 5 (OZ.Valid 5 w376.low w376.t w376.y w376.r w376.cap) (P33.root 5) :=
  Night6836Tree.sound w376 pick376 5 t566 _ (by decide +kernel)
theorem cov376_6 : PA.Covered 6 (OZ.Valid 6 w376.low w376.t w376.y w376.r w376.cap) (P33.root 6) :=
  Night6836Tree.sound w376 pick376 6 t567 _ (by decide +kernel)
theorem cov376_7 : PA.Covered 7 (OZ.Valid 7 w376.low w376.t w376.y w376.r w376.cap) (P33.root 7) :=
  Night6836Tree.sound w376 pick376 7 t568 _ (by decide +kernel)
theorem window376 : P33.WindowCount w376 := by
  apply P33.window_count w376 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov376_1
  · exact cov376_2
  · exact cov376_3
  · exact cov376_4
  · exact cov376_5
  · exact cov376_6
  · exact cov376_7
def w377 : P33.Window := ⟨6,51,4450,3451,191875571105497452,74842,35000,5000000,81920000000⟩
def h377_0 : Height w377 := ⟨74842,35000,by decide +kernel⟩
def h377_1 : Height w377 := ⟨80893,31000,by decide +kernel⟩
def h377_2 : Height w377 := ⟨88696,27000,by decide +kernel⟩
def h377_3 : Height w377 := ⟨99699,23000,by decide +kernel⟩
def pick377 (cl : ℕ) : Height w377 := if cl<36 then (if cl<6 then (h377_0) else (h377_1)) else (if cl<213 then (h377_2) else (h377_3))
private theorem k377_1_0 : check w377 pick377 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k377_1_1 : check w377 pick377 1 t4249 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k377_1_2 : check w377 pick377 1 t4250 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w377 pick377 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t4249 k377_1_0 k377_1_1
private theorem k377_1_3 : check w377 pick377 1 t2812 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k377_1_4 : check w377 pick377 1 t6577 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k377_1_5 : check w377 pick377 1 t9127 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w377 pick377 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t2812 t6577 k377_1_3 k377_1_4
private theorem k377_1_6 : check w377 pick377 1 t9128 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w377 pick377 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t4250 t9127 k377_1_2 k377_1_5
private theorem k377_1_7 : check w377 pick377 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k377_1_8 : check w377 pick377 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k377_1_9 : check w377 pick377 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w377 pick377 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k377_1_7 k377_1_8
private theorem k377_1_10 : check w377 pick377 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k377_1_11 : check w377 pick377 1 t9083 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k377_1_12 : check w377 pick377 1 t9084 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w377 pick377 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t9083 k377_1_10 k377_1_11
private theorem k377_1_13 : check w377 pick377 1 t9097 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w377 pick377 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t9084 k377_1_9 k377_1_12
private theorem k377_1_14 : check w377 pick377 1 t9130 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w377 pick377 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9128 t9097 k377_1_6 k377_1_13
theorem cov377_1 : PA.Covered 1 (OZ.Valid 1 w377.low w377.t w377.y w377.r w377.cap) (P33.root 1) :=
  Night6836Tree.sound w377 pick377 1 t9130 _ k377_1_14
theorem cov377_2 : PA.Covered 2 (OZ.Valid 2 w377.low w377.t w377.y w377.r w377.cap) (P33.root 2) :=
  Night6836Tree.sound w377 pick377 2 t9132 _ (by decide +kernel)
theorem cov377_3 : PA.Covered 3 (OZ.Valid 3 w377.low w377.t w377.y w377.r w377.cap) (P33.root 3) :=
  Night6836Tree.sound w377 pick377 3 t564 _ (by decide +kernel)
theorem cov377_4 : PA.Covered 4 (OZ.Valid 4 w377.low w377.t w377.y w377.r w377.cap) (P33.root 4) :=
  Night6836Tree.sound w377 pick377 4 t565 _ (by decide +kernel)
theorem cov377_5 : PA.Covered 5 (OZ.Valid 5 w377.low w377.t w377.y w377.r w377.cap) (P33.root 5) :=
  Night6836Tree.sound w377 pick377 5 t566 _ (by decide +kernel)
theorem cov377_6 : PA.Covered 6 (OZ.Valid 6 w377.low w377.t w377.y w377.r w377.cap) (P33.root 6) :=
  Night6836Tree.sound w377 pick377 6 t567 _ (by decide +kernel)
theorem cov377_7 : PA.Covered 7 (OZ.Valid 7 w377.low w377.t w377.y w377.r w377.cap) (P33.root 7) :=
  Night6836Tree.sound w377 pick377 7 t2134 _ (by decide +kernel)
theorem window377 : P33.WindowCount w377 := by
  apply P33.window_count w377 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov377_1
  · exact cov377_2
  · exact cov377_3
  · exact cov377_4
  · exact cov377_5
  · exact cov377_6
  · exact cov377_7
def w378 : P33.Window := ⟨6,51,7089,6856,245431256859150057,37205,18000,5000000,81920000000⟩
def h378_0 : Height w378 := ⟨37205,18000,by decide +kernel⟩
def h378_1 : Height w378 := ⟨41852,15000,by decide +kernel⟩
def h378_2 : Height w378 := ⟨48960,12000,by decide +kernel⟩
def h378_3 : Height w378 := ⟨63253,9000,by decide +kernel⟩
def pick378 (cl : ℕ) : Height w378 := if cl<100 then (if cl<6 then (h378_0) else (h378_1)) else (if cl<989 then (h378_2) else (h378_3))
private theorem k378_1_0 : check w378 pick378 1 t9283 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k378_1_1 : check w378 pick378 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k378_1_2 : check w378 pick378 1 t9284 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w378 pick378 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9283 t9190 k378_1_0 k378_1_1
private theorem k378_1_3 : check w378 pick378 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k378_1_4 : check w378 pick378 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k378_1_5 : check w378 pick378 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w378 pick378 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k378_1_3 k378_1_4
private theorem k378_1_6 : check w378 pick378 1 t9285 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w378 pick378 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9284 t9207 k378_1_2 k378_1_5
private theorem k378_1_7 : check w378 pick378 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k378_1_8 : check w378 pick378 1 t9299 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k378_1_9 : check w378 pick378 1 t9300 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w378 pick378 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t9299 k378_1_7 k378_1_8
private theorem k378_1_10 : check w378 pick378 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k378_1_11 : check w378 pick378 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k378_1_12 : check w378 pick378 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w378 pick378 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k378_1_10 k378_1_11
private theorem k378_1_13 : check w378 pick378 1 t9301 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w378 pick378 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9300 t9211 k378_1_9 k378_1_12
private theorem k378_1_14 : check w378 pick378 1 t9302 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w378 pick378 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9285 t9301 k378_1_6 k378_1_13
theorem cov378_1 : PA.Covered 1 (OZ.Valid 1 w378.low w378.t w378.y w378.r w378.cap) (P33.root 1) :=
  Night6836Tree.sound w378 pick378 1 t9302 _ k378_1_14
private theorem k378_2_0 : check w378 pick378 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k378_2_1 : check w378 pick378 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k378_2_2 : check w378 pick378 2 t9322 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w378 pick378 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9239 t9321 k378_2_0 k378_2_1
private theorem k378_2_3 : check w378 pick378 2 t9330 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k378_2_4 : check w378 pick378 2 t9331 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w378 pick378 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9322 t9330 k378_2_2 k378_2_3
theorem cov378_2 : PA.Covered 2 (OZ.Valid 2 w378.low w378.t w378.y w378.r w378.cap) (P33.root 2) :=
  Night6836Tree.sound w378 pick378 2 t9331 _ k378_2_4
theorem cov378_3 : PA.Covered 3 (OZ.Valid 3 w378.low w378.t w378.y w378.r w378.cap) (P33.root 3) :=
  Night6836Tree.sound w378 pick378 3 t564 _ (by decide +kernel)
theorem cov378_4 : PA.Covered 4 (OZ.Valid 4 w378.low w378.t w378.y w378.r w378.cap) (P33.root 4) :=
  Night6836Tree.sound w378 pick378 4 t565 _ (by decide +kernel)
theorem cov378_5 : PA.Covered 5 (OZ.Valid 5 w378.low w378.t w378.y w378.r w378.cap) (P33.root 5) :=
  Night6836Tree.sound w378 pick378 5 t566 _ (by decide +kernel)
theorem cov378_6 : PA.Covered 6 (OZ.Valid 6 w378.low w378.t w378.y w378.r w378.cap) (P33.root 6) :=
  Night6836Tree.sound w378 pick378 6 t567 _ (by decide +kernel)
theorem cov378_7 : PA.Covered 7 (OZ.Valid 7 w378.low w378.t w378.y w378.r w378.cap) (P33.root 7) :=
  Night6836Tree.sound w378 pick378 7 t568 _ (by decide +kernel)
theorem window378 : P33.WindowCount w378 := by
  apply P33.window_count w378 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov378_1
  · exact cov378_2
  · exact cov378_3
  · exact cov378_4
  · exact cov378_5
  · exact cov378_6
  · exact cov378_7
def w379 : P33.Window := ⟨6,52,7026,6963,245973851970968079,37216,18000,5000000,81920000000⟩
def h379_0 : Height w379 := ⟨37216,18000,by decide +kernel⟩
def h379_1 : Height w379 := ⟨41796,15000,by decide +kernel⟩
def h379_2 : Height w379 := ⟨48763,12000,by decide +kernel⟩
def h379_3 : Height w379 := ⟨62640,9000,by decide +kernel⟩
def pick379 (cl : ℕ) : Height w379 := if cl<90 then (if cl<6 then (h379_0) else (h379_1)) else (if cl<989 then (h379_2) else (h379_3))
private theorem k379_1_0 : check w379 pick379 1 t9283 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k379_1_1 : check w379 pick379 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k379_1_2 : check w379 pick379 1 t9284 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w379 pick379 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9283 t9190 k379_1_0 k379_1_1
private theorem k379_1_3 : check w379 pick379 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k379_1_4 : check w379 pick379 1 t9206 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k379_1_5 : check w379 pick379 1 t9207 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w379 pick379 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9206 k379_1_3 k379_1_4
private theorem k379_1_6 : check w379 pick379 1 t9285 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w379 pick379 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9284 t9207 k379_1_2 k379_1_5
private theorem k379_1_7 : check w379 pick379 1 t9336 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k379_1_8 : check w379 pick379 1 t9341 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k379_1_9 : check w379 pick379 1 t9342 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w379 pick379 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t9336 t9341 k379_1_7 k379_1_8
private theorem k379_1_10 : check w379 pick379 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k379_1_11 : check w379 pick379 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k379_1_12 : check w379 pick379 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w379 pick379 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k379_1_10 k379_1_11
private theorem k379_1_13 : check w379 pick379 1 t9343 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w379 pick379 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9342 t9211 k379_1_9 k379_1_12
private theorem k379_1_14 : check w379 pick379 1 t9344 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w379 pick379 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9285 t9343 k379_1_6 k379_1_13
theorem cov379_1 : PA.Covered 1 (OZ.Valid 1 w379.low w379.t w379.y w379.r w379.cap) (P33.root 1) :=
  Night6836Tree.sound w379 pick379 1 t9344 _ k379_1_14
private theorem k379_2_0 : check w379 pick379 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k379_2_1 : check w379 pick379 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k379_2_2 : check w379 pick379 2 t9322 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w379 pick379 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9239 t9321 k379_2_0 k379_2_1
private theorem k379_2_3 : check w379 pick379 2 t9356 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k379_2_4 : check w379 pick379 2 t9357 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w379 pick379 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9322 t9356 k379_2_2 k379_2_3
theorem cov379_2 : PA.Covered 2 (OZ.Valid 2 w379.low w379.t w379.y w379.r w379.cap) (P33.root 2) :=
  Night6836Tree.sound w379 pick379 2 t9357 _ k379_2_4
theorem cov379_3 : PA.Covered 3 (OZ.Valid 3 w379.low w379.t w379.y w379.r w379.cap) (P33.root 3) :=
  Night6836Tree.sound w379 pick379 3 t564 _ (by decide +kernel)
theorem cov379_4 : PA.Covered 4 (OZ.Valid 4 w379.low w379.t w379.y w379.r w379.cap) (P33.root 4) :=
  Night6836Tree.sound w379 pick379 4 t565 _ (by decide +kernel)
theorem cov379_5 : PA.Covered 5 (OZ.Valid 5 w379.low w379.t w379.y w379.r w379.cap) (P33.root 5) :=
  Night6836Tree.sound w379 pick379 5 t566 _ (by decide +kernel)
theorem cov379_6 : PA.Covered 6 (OZ.Valid 6 w379.low w379.t w379.y w379.r w379.cap) (P33.root 6) :=
  Night6836Tree.sound w379 pick379 6 t567 _ (by decide +kernel)
theorem cov379_7 : PA.Covered 7 (OZ.Valid 7 w379.low w379.t w379.y w379.r w379.cap) (P33.root 7) :=
  Night6836Tree.sound w379 pick379 7 t568 _ (by decide +kernel)
theorem window379 : P33.WindowCount w379 := by
  apply P33.window_count w379 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov379_1
  · exact cov379_2
  · exact cov379_3
  · exact cov379_4
  · exact cov379_5
  · exact cov379_6
  · exact cov379_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w380 : P33.Window := ⟨6,53,6962,6897,245949227684474813,38751,18000,5000000,81920000000⟩
def h380_0 : Height w380 := ⟨38751,18000,by decide +kernel⟩
def h380_1 : Height w380 := ⟨43475,15000,by decide +kernel⟩
def h380_2 : Height w380 := ⟨50712,12000,by decide +kernel⟩
def h380_3 : Height w380 := ⟨65255,9000,by decide +kernel⟩
def pick380 (cl : ℕ) : Height w380 := if cl<107 then (if cl<10 then (h380_0) else (h380_1)) else (if cl<993 then (h380_2) else (h380_3))
private theorem k380_1_0 : check w380 pick380 1 t9283 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k380_1_1 : check w380 pick380 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k380_1_2 : check w380 pick380 1 t9284 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w380 pick380 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9283 t9190 k380_1_0 k380_1_1
private theorem k380_1_3 : check w380 pick380 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k380_1_4 : check w380 pick380 1 t9361 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k380_1_5 : check w380 pick380 1 t9362 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w380 pick380 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9361 k380_1_3 k380_1_4
private theorem k380_1_6 : check w380 pick380 1 t9363 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w380 pick380 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9284 t9362 k380_1_2 k380_1_5
private theorem k380_1_7 : check w380 pick380 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k380_1_8 : check w380 pick380 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k380_1_9 : check w380 pick380 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w380 pick380 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k380_1_7 k380_1_8
private theorem k380_1_10 : check w380 pick380 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k380_1_11 : check w380 pick380 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k380_1_12 : check w380 pick380 1 t9364 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w380 pick380 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t9210 k380_1_10 k380_1_11
private theorem k380_1_13 : check w380 pick380 1 t9365 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w380 pick380 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t9364 k380_1_9 k380_1_12
private theorem k380_1_14 : check w380 pick380 1 t9366 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w380 pick380 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9363 t9365 k380_1_6 k380_1_13
theorem cov380_1 : PA.Covered 1 (OZ.Valid 1 w380.low w380.t w380.y w380.r w380.cap) (P33.root 1) :=
  Night6836Tree.sound w380 pick380 1 t9366 _ k380_1_14
private theorem k380_2_0 : check w380 pick380 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k380_2_1 : check w380 pick380 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k380_2_2 : check w380 pick380 2 t9322 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w380 pick380 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9239 t9321 k380_2_0 k380_2_1
private theorem k380_2_3 : check w380 pick380 2 t9374 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k380_2_4 : check w380 pick380 2 t9377 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k380_2_5 : check w380 pick380 2 t9378 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w380 pick380 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t9374 t9377 k380_2_3 k380_2_4
private theorem k380_2_6 : check w380 pick380 2 t9379 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w380 pick380 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9322 t9378 k380_2_2 k380_2_5
theorem cov380_2 : PA.Covered 2 (OZ.Valid 2 w380.low w380.t w380.y w380.r w380.cap) (P33.root 2) :=
  Night6836Tree.sound w380 pick380 2 t9379 _ k380_2_6
theorem cov380_3 : PA.Covered 3 (OZ.Valid 3 w380.low w380.t w380.y w380.r w380.cap) (P33.root 3) :=
  Night6836Tree.sound w380 pick380 3 t564 _ (by decide +kernel)
theorem cov380_4 : PA.Covered 4 (OZ.Valid 4 w380.low w380.t w380.y w380.r w380.cap) (P33.root 4) :=
  Night6836Tree.sound w380 pick380 4 t565 _ (by decide +kernel)
theorem cov380_5 : PA.Covered 5 (OZ.Valid 5 w380.low w380.t w380.y w380.r w380.cap) (P33.root 5) :=
  Night6836Tree.sound w380 pick380 5 t566 _ (by decide +kernel)
theorem cov380_6 : PA.Covered 6 (OZ.Valid 6 w380.low w380.t w380.y w380.r w380.cap) (P33.root 6) :=
  Night6836Tree.sound w380 pick380 6 t567 _ (by decide +kernel)
theorem cov380_7 : PA.Covered 7 (OZ.Valid 7 w380.low w380.t w380.y w380.r w380.cap) (P33.root 7) :=
  Night6836Tree.sound w380 pick380 7 t568 _ (by decide +kernel)
theorem window380 : P33.WindowCount w380 := by
  apply P33.window_count w380 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov380_1
  · exact cov380_2
  · exact cov380_3
  · exact cov380_4
  · exact cov380_5
  · exact cov380_6
  · exact cov380_7
def w381 : P33.Window := ⟨6,54,6669,5720,244515523352579231,48842,21000,5000000,81920000000⟩
def h381_0 : Height w381 := ⟨48842,21000,by decide +kernel⟩
def h381_1 : Height w381 := ⟨53793,18000,by decide +kernel⟩
def h381_2 : Height w381 := ⟨60850,15000,by decide +kernel⟩
def h381_3 : Height w381 := ⟨72782,12000,by decide +kernel⟩
def pick381 (cl : ℕ) : Height w381 := if cl<97 then (if cl<13 then (h381_0) else (h381_1)) else (if cl<922 then (h381_2) else (h381_3))
private theorem k381_1_0 : check w381 pick381 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k381_1_1 : check w381 pick381 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k381_1_2 : check w381 pick381 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w381 pick381 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k381_1_0 k381_1_1
private theorem k381_1_3 : check w381 pick381 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k381_1_4 : check w381 pick381 1 t9361 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k381_1_5 : check w381 pick381 1 t9362 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w381 pick381 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9361 k381_1_3 k381_1_4
private theorem k381_1_6 : check w381 pick381 1 t9380 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w381 pick381 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9362 k381_1_2 k381_1_5
private theorem k381_1_7 : check w381 pick381 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k381_1_8 : check w381 pick381 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k381_1_9 : check w381 pick381 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w381 pick381 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k381_1_7 k381_1_8
private theorem k381_1_10 : check w381 pick381 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k381_1_11 : check w381 pick381 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k381_1_12 : check w381 pick381 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w381 pick381 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k381_1_10 k381_1_11
private theorem k381_1_13 : check w381 pick381 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w381 pick381 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k381_1_9 k381_1_12
private theorem k381_1_14 : check w381 pick381 1 t9381 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w381 pick381 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9380 t9212 k381_1_6 k381_1_13
theorem cov381_1 : PA.Covered 1 (OZ.Valid 1 w381.low w381.t w381.y w381.r w381.cap) (P33.root 1) :=
  Night6836Tree.sound w381 pick381 1 t9381 _ k381_1_14
private theorem k381_2_0 : check w381 pick381 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k381_2_1 : check w381 pick381 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k381_2_2 : check w381 pick381 2 t9322 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w381 pick381 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9239 t9321 k381_2_0 k381_2_1
private theorem k381_2_3 : check w381 pick381 2 t9383 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k381_2_4 : check w381 pick381 2 t9384 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w381 pick381 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9322 t9383 k381_2_2 k381_2_3
theorem cov381_2 : PA.Covered 2 (OZ.Valid 2 w381.low w381.t w381.y w381.r w381.cap) (P33.root 2) :=
  Night6836Tree.sound w381 pick381 2 t9384 _ k381_2_4
theorem cov381_3 : PA.Covered 3 (OZ.Valid 3 w381.low w381.t w381.y w381.r w381.cap) (P33.root 3) :=
  Night6836Tree.sound w381 pick381 3 t564 _ (by decide +kernel)
theorem cov381_4 : PA.Covered 4 (OZ.Valid 4 w381.low w381.t w381.y w381.r w381.cap) (P33.root 4) :=
  Night6836Tree.sound w381 pick381 4 t565 _ (by decide +kernel)
theorem cov381_5 : PA.Covered 5 (OZ.Valid 5 w381.low w381.t w381.y w381.r w381.cap) (P33.root 5) :=
  Night6836Tree.sound w381 pick381 5 t566 _ (by decide +kernel)
theorem cov381_6 : PA.Covered 6 (OZ.Valid 6 w381.low w381.t w381.y w381.r w381.cap) (P33.root 6) :=
  Night6836Tree.sound w381 pick381 6 t567 _ (by decide +kernel)
theorem cov381_7 : PA.Covered 7 (OZ.Valid 7 w381.low w381.t w381.y w381.r w381.cap) (P33.root 7) :=
  Night6836Tree.sound w381 pick381 7 t568 _ (by decide +kernel)
theorem window381 : P33.WindowCount w381 := by
  apply P33.window_count w381 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov381_1
  · exact cov381_2
  · exact cov381_3
  · exact cov381_4
  · exact cov381_5
  · exact cov381_6
  · exact cov381_7
def w382 : P33.Window := ⟨6,54,6896,6827,245984111406994826,40364,18000,5000000,81920000000⟩
def h382_0 : Height w382 := ⟨40364,18000,by decide +kernel⟩
def h382_1 : Height w382 := ⟨45244,15000,by decide +kernel⟩
def h382_2 : Height w382 := ⟨52772,12000,by decide +kernel⟩
def h382_3 : Height w382 := ⟨68048,9000,by decide +kernel⟩
def pick382 (cl : ℕ) : Height w382 := if cl<135 then (if cl<13 then (h382_0) else (h382_1)) else (if cl<1021 then (h382_2) else (h382_3))
private theorem k382_1_0 : check w382 pick382 1 t9283 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k382_1_1 : check w382 pick382 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k382_1_2 : check w382 pick382 1 t9284 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w382 pick382 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9283 t9190 k382_1_0 k382_1_1
private theorem k382_1_3 : check w382 pick382 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k382_1_4 : check w382 pick382 1 t9390 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k382_1_5 : check w382 pick382 1 t9391 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w382 pick382 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9390 k382_1_3 k382_1_4
private theorem k382_1_6 : check w382 pick382 1 t9392 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w382 pick382 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9284 t9391 k382_1_2 k382_1_5
private theorem k382_1_7 : check w382 pick382 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k382_1_8 : check w382 pick382 1 t3123 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k382_1_9 : check w382 pick382 1 t3200 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w382 pick382 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t3123 k382_1_7 k382_1_8
private theorem k382_1_10 : check w382 pick382 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k382_1_11 : check w382 pick382 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k382_1_12 : check w382 pick382 1 t9398 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w382 pick382 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t9397 k382_1_10 k382_1_11
private theorem k382_1_13 : check w382 pick382 1 t9399 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w382 pick382 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t3200 t9398 k382_1_9 k382_1_12
private theorem k382_1_14 : check w382 pick382 1 t9400 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w382 pick382 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9392 t9399 k382_1_6 k382_1_13
theorem cov382_1 : PA.Covered 1 (OZ.Valid 1 w382.low w382.t w382.y w382.r w382.cap) (P33.root 1) :=
  Night6836Tree.sound w382 pick382 1 t9400 _ k382_1_14
private theorem k382_2_0 : check w382 pick382 2 t9401 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k382_2_1 : check w382 pick382 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k382_2_2 : check w382 pick382 2 t9402 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w382 pick382 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9401 t9321 k382_2_0 k382_2_1
private theorem k382_2_3 : check w382 pick382 2 t9407 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k382_2_4 : check w382 pick382 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k382_2_5 : check w382 pick382 2 t9412 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w382 pick382 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t9407 t9411 k382_2_3 k382_2_4
private theorem k382_2_6 : check w382 pick382 2 t9413 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w382 pick382 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9402 t9412 k382_2_2 k382_2_5
theorem cov382_2 : PA.Covered 2 (OZ.Valid 2 w382.low w382.t w382.y w382.r w382.cap) (P33.root 2) :=
  Night6836Tree.sound w382 pick382 2 t9413 _ k382_2_6
theorem cov382_3 : PA.Covered 3 (OZ.Valid 3 w382.low w382.t w382.y w382.r w382.cap) (P33.root 3) :=
  Night6836Tree.sound w382 pick382 3 t564 _ (by decide +kernel)
theorem cov382_4 : PA.Covered 4 (OZ.Valid 4 w382.low w382.t w382.y w382.r w382.cap) (P33.root 4) :=
  Night6836Tree.sound w382 pick382 4 t565 _ (by decide +kernel)
theorem cov382_5 : PA.Covered 5 (OZ.Valid 5 w382.low w382.t w382.y w382.r w382.cap) (P33.root 5) :=
  Night6836Tree.sound w382 pick382 5 t566 _ (by decide +kernel)
theorem cov382_6 : PA.Covered 6 (OZ.Valid 6 w382.low w382.t w382.y w382.r w382.cap) (P33.root 6) :=
  Night6836Tree.sound w382 pick382 6 t567 _ (by decide +kernel)
theorem cov382_7 : PA.Covered 7 (OZ.Valid 7 w382.low w382.t w382.y w382.r w382.cap) (P33.root 7) :=
  Night6836Tree.sound w382 pick382 7 t568 _ (by decide +kernel)
theorem window382 : P33.WindowCount w382 := by
  apply P33.window_count w382 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov382_1
  · exact cov382_2
  · exact cov382_3
  · exact cov382_4
  · exact cov382_5
  · exact cov382_6
  · exact cov382_7
def w383 : P33.Window := ⟨6,55,6826,6744,245831304673149819,42150,18000,5000000,81920000000⟩
def h383_0 : Height w383 := ⟨42150,18000,by decide +kernel⟩
def h383_1 : Height w383 := ⟨47213,15000,by decide +kernel⟩
def h383_2 : Height w383 := ⟨55085,12000,by decide +kernel⟩
def h383_3 : Height w383 := ⟨71236,9000,by decide +kernel⟩
def pick383 (cl : ℕ) : Height w383 := if cl<163 then (if cl<16 then (h383_0) else (h383_1)) else (if cl<1021 then (h383_2) else (h383_3))
private theorem k383_1_0 : check w383 pick383 1 t5078 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k383_1_1 : check w383 pick383 1 t5105 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k383_1_2 : check w383 pick383 1 t5106 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w383 pick383 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5078 t5105 k383_1_0 k383_1_1
private theorem k383_1_3 : check w383 pick383 1 t9414 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k383_1_4 : check w383 pick383 1 t9416 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k383_1_5 : check w383 pick383 1 t9417 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w383 pick383 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t9414 t9416 k383_1_3 k383_1_4
private theorem k383_1_6 : check w383 pick383 1 t9418 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w383 pick383 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t5106 t9417 k383_1_2 k383_1_5
private theorem k383_1_7 : check w383 pick383 1 t9428 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k383_1_8 : check w383 pick383 1 t9431 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k383_1_9 : check w383 pick383 1 t9432 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w383 pick383 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t9428 t9431 k383_1_7 k383_1_8
private theorem k383_1_10 : check w383 pick383 1 t1662 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k383_1_11 : check w383 pick383 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k383_1_12 : check w383 pick383 1 t9433 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w383 pick383 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t1662 t9397 k383_1_10 k383_1_11
private theorem k383_1_13 : check w383 pick383 1 t9434 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w383 pick383 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t9432 t9433 k383_1_9 k383_1_12
private theorem k383_1_14 : check w383 pick383 1 t9435 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w383 pick383 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9418 t9434 k383_1_6 k383_1_13
theorem cov383_1 : PA.Covered 1 (OZ.Valid 1 w383.low w383.t w383.y w383.r w383.cap) (P33.root 1) :=
  Night6836Tree.sound w383 pick383 1 t9435 _ k383_1_14
private theorem k383_2_0 : check w383 pick383 2 t9401 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k383_2_1 : check w383 pick383 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k383_2_2 : check w383 pick383 2 t9402 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w383 pick383 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9401 t9321 k383_2_0 k383_2_1
private theorem k383_2_3 : check w383 pick383 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k383_2_4 : check w383 pick383 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k383_2_5 : check w383 pick383 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w383 pick383 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k383_2_3 k383_2_4
private theorem k383_2_6 : check w383 pick383 2 t9437 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w383 pick383 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9402 t9436 k383_2_2 k383_2_5
theorem cov383_2 : PA.Covered 2 (OZ.Valid 2 w383.low w383.t w383.y w383.r w383.cap) (P33.root 2) :=
  Night6836Tree.sound w383 pick383 2 t9437 _ k383_2_6
theorem cov383_3 : PA.Covered 3 (OZ.Valid 3 w383.low w383.t w383.y w383.r w383.cap) (P33.root 3) :=
  Night6836Tree.sound w383 pick383 3 t564 _ (by decide +kernel)
theorem cov383_4 : PA.Covered 4 (OZ.Valid 4 w383.low w383.t w383.y w383.r w383.cap) (P33.root 4) :=
  Night6836Tree.sound w383 pick383 4 t565 _ (by decide +kernel)
theorem cov383_5 : PA.Covered 5 (OZ.Valid 5 w383.low w383.t w383.y w383.r w383.cap) (P33.root 5) :=
  Night6836Tree.sound w383 pick383 5 t566 _ (by decide +kernel)
theorem cov383_6 : PA.Covered 6 (OZ.Valid 6 w383.low w383.t w383.y w383.r w383.cap) (P33.root 6) :=
  Night6836Tree.sound w383 pick383 6 t567 _ (by decide +kernel)
theorem cov383_7 : PA.Covered 7 (OZ.Valid 7 w383.low w383.t w383.y w383.r w383.cap) (P33.root 7) :=
  Night6836Tree.sound w383 pick383 7 t568 _ (by decide +kernel)
theorem window383 : P33.WindowCount w383 := by
  apply P33.window_count w383 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov383_1
  · exact cov383_2
  · exact cov383_3
  · exact cov383_4
  · exact cov383_5
  · exact cov383_6
  · exact cov383_7
def w384 : P33.Window := ⟨6,56,6743,6648,245931956579943435,40228,21000,5000000,81920000000⟩
def h384_0 : Height w384 := ⟨40228,21000,by decide +kernel⟩
def h384_1 : Height w384 := ⟨44134,18000,by decide +kernel⟩
def h384_2 : Height w384 := ⟨49410,15000,by decide +kernel⟩
def h384_3 : Height w384 := ⟨57686,12000,by decide +kernel⟩
def pick384 (cl : ℕ) : Height w384 := if cl<25 then (if cl<2 then (h384_0) else (h384_1)) else (if cl<210 then (h384_2) else (h384_3))
private theorem k384_1_0 : check w384 pick384 1 t5078 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k384_1_1 : check w384 pick384 1 t5105 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k384_1_2 : check w384 pick384 1 t5106 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w384 pick384 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5078 t5105 k384_1_0 k384_1_1
private theorem k384_1_3 : check w384 pick384 1 t9414 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k384_1_4 : check w384 pick384 1 t9438 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k384_1_5 : check w384 pick384 1 t9439 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w384 pick384 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t9414 t9438 k384_1_3 k384_1_4
private theorem k384_1_6 : check w384 pick384 1 t9440 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w384 pick384 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t5106 t9439 k384_1_2 k384_1_5
private theorem k384_1_7 : check w384 pick384 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k384_1_8 : check w384 pick384 1 t1828 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k384_1_9 : check w384 pick384 1 t9441 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w384 pick384 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t3199 t1828 k384_1_7 k384_1_8
private theorem k384_1_10 : check w384 pick384 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k384_1_11 : check w384 pick384 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k384_1_12 : check w384 pick384 1 t9442 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w384 pick384 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t9397 k384_1_10 k384_1_11
private theorem k384_1_13 : check w384 pick384 1 t9443 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w384 pick384 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t9441 t9442 k384_1_9 k384_1_12
private theorem k384_1_14 : check w384 pick384 1 t9444 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w384 pick384 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9440 t9443 k384_1_6 k384_1_13
theorem cov384_1 : PA.Covered 1 (OZ.Valid 1 w384.low w384.t w384.y w384.r w384.cap) (P33.root 1) :=
  Night6836Tree.sound w384 pick384 1 t9444 _ k384_1_14
private theorem k384_2_0 : check w384 pick384 2 t9401 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k384_2_1 : check w384 pick384 2 t9449 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k384_2_2 : check w384 pick384 2 t9450 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w384 pick384 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9401 t9449 k384_2_0 k384_2_1
private theorem k384_2_3 : check w384 pick384 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k384_2_4 : check w384 pick384 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k384_2_5 : check w384 pick384 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w384 pick384 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k384_2_3 k384_2_4
private theorem k384_2_6 : check w384 pick384 2 t9451 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w384 pick384 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9450 t9436 k384_2_2 k384_2_5
theorem cov384_2 : PA.Covered 2 (OZ.Valid 2 w384.low w384.t w384.y w384.r w384.cap) (P33.root 2) :=
  Night6836Tree.sound w384 pick384 2 t9451 _ k384_2_6
theorem cov384_3 : PA.Covered 3 (OZ.Valid 3 w384.low w384.t w384.y w384.r w384.cap) (P33.root 3) :=
  Night6836Tree.sound w384 pick384 3 t564 _ (by decide +kernel)
theorem cov384_4 : PA.Covered 4 (OZ.Valid 4 w384.low w384.t w384.y w384.r w384.cap) (P33.root 4) :=
  Night6836Tree.sound w384 pick384 4 t565 _ (by decide +kernel)
theorem cov384_5 : PA.Covered 5 (OZ.Valid 5 w384.low w384.t w384.y w384.r w384.cap) (P33.root 5) :=
  Night6836Tree.sound w384 pick384 5 t566 _ (by decide +kernel)
theorem cov384_6 : PA.Covered 6 (OZ.Valid 6 w384.low w384.t w384.y w384.r w384.cap) (P33.root 6) :=
  Night6836Tree.sound w384 pick384 6 t567 _ (by decide +kernel)
theorem cov384_7 : PA.Covered 7 (OZ.Valid 7 w384.low w384.t w384.y w384.r w384.cap) (P33.root 7) :=
  Night6836Tree.sound w384 pick384 7 t568 _ (by decide +kernel)
theorem window384 : P33.WindowCount w384 := by
  apply P33.window_count w384 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov384_1
  · exact cov384_2
  · exact cov384_3
  · exact cov384_4
  · exact cov384_5
  · exact cov384_6
  · exact cov384_7
def w385 : P33.Window := ⟨6,57,6647,6312,245840035342764693,44731,21000,5000000,81920000000⟩
def h385_0 : Height w385 := ⟨44731,21000,by decide +kernel⟩
def h385_1 : Height w385 := ⟨49037,18000,by decide +kernel⟩
def h385_2 : Height w385 := ⟨54977,15000,by decide +kernel⟩
def h385_3 : Height w385 := ⟨64556,12000,by decide +kernel⟩
def pick385 (cl : ℕ) : Height w385 := if cl<36 then (if cl<4 then (h385_0) else (h385_1)) else (if cl<331 then (h385_2) else (h385_3))
private theorem k385_1_0 : check w385 pick385 1 t5078 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k385_1_1 : check w385 pick385 1 t5105 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k385_1_2 : check w385 pick385 1 t5106 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w385 pick385 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5078 t5105 k385_1_0 k385_1_1
private theorem k385_1_3 : check w385 pick385 1 t9457 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k385_1_4 : check w385 pick385 1 t9472 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k385_1_5 : check w385 pick385 1 t9473 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w385 pick385 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t9457 t9472 k385_1_3 k385_1_4
private theorem k385_1_6 : check w385 pick385 1 t9474 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w385 pick385 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t5106 t9473 k385_1_2 k385_1_5
private theorem k385_1_7 : check w385 pick385 1 t9487 ⟨1,7,2,16,1,52,146,172⟩ = true := by decide +kernel
private theorem k385_1_8 : check w385 pick385 1 t9493 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k385_1_9 : check w385 pick385 1 t9494 ⟨1,7,2,16,1,52,146,199⟩ = true := glue w385 pick385 1 ⟨1,7,2,16,1,52,146,199⟩ 3 172 t9487 t9493 k385_1_7 k385_1_8
private theorem k385_1_10 : check w385 pick385 1 t1662 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k385_1_11 : check w385 pick385 1 t9397 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k385_1_12 : check w385 pick385 1 t9433 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w385 pick385 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t1662 t9397 k385_1_10 k385_1_11
private theorem k385_1_13 : check w385 pick385 1 t9495 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w385 pick385 1 ⟨1,7,2,16,1,52,146,450⟩ 3 199 t9494 t9433 k385_1_9 k385_1_12
private theorem k385_1_14 : check w385 pick385 1 t9496 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w385 pick385 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t9474 t9495 k385_1_6 k385_1_13
theorem cov385_1 : PA.Covered 1 (OZ.Valid 1 w385.low w385.t w385.y w385.r w385.cap) (P33.root 1) :=
  Night6836Tree.sound w385 pick385 1 t9496 _ k385_1_14
private theorem k385_2_0 : check w385 pick385 2 t9498 ⟨2,7,4,16,2,52,2,84⟩ = true := by decide +kernel
private theorem k385_2_1 : check w385 pick385 2 t9500 ⟨2,7,4,16,2,52,85,139⟩ = true := by decide +kernel
private theorem k385_2_2 : check w385 pick385 2 t9501 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w385 pick385 2 ⟨2,7,4,16,2,52,2,139⟩ 3 84 t9498 t9500 k385_2_0 k385_2_1
private theorem k385_2_3 : check w385 pick385 2 t4224 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k385_2_4 : check w385 pick385 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k385_2_5 : check w385 pick385 2 t9436 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w385 pick385 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t4224 t9411 k385_2_3 k385_2_4
private theorem k385_2_6 : check w385 pick385 2 t9502 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w385 pick385 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9501 t9436 k385_2_2 k385_2_5
theorem cov385_2 : PA.Covered 2 (OZ.Valid 2 w385.low w385.t w385.y w385.r w385.cap) (P33.root 2) :=
  Night6836Tree.sound w385 pick385 2 t9502 _ k385_2_6
theorem cov385_3 : PA.Covered 3 (OZ.Valid 3 w385.low w385.t w385.y w385.r w385.cap) (P33.root 3) :=
  Night6836Tree.sound w385 pick385 3 t564 _ (by decide +kernel)
theorem cov385_4 : PA.Covered 4 (OZ.Valid 4 w385.low w385.t w385.y w385.r w385.cap) (P33.root 4) :=
  Night6836Tree.sound w385 pick385 4 t565 _ (by decide +kernel)
theorem cov385_5 : PA.Covered 5 (OZ.Valid 5 w385.low w385.t w385.y w385.r w385.cap) (P33.root 5) :=
  Night6836Tree.sound w385 pick385 5 t566 _ (by decide +kernel)
theorem cov385_6 : PA.Covered 6 (OZ.Valid 6 w385.low w385.t w385.y w385.r w385.cap) (P33.root 6) :=
  Night6836Tree.sound w385 pick385 6 t567 _ (by decide +kernel)
theorem cov385_7 : PA.Covered 7 (OZ.Valid 7 w385.low w385.t w385.y w385.r w385.cap) (P33.root 7) :=
  Night6836Tree.sound w385 pick385 7 t568 _ (by decide +kernel)
theorem window385 : P33.WindowCount w385 := by
  apply P33.window_count w385 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov385_1
  · exact cov385_2
  · exact cov385_3
  · exact cov385_4
  · exact cov385_5
  · exact cov385_6
  · exact cov385_7
def w386 : P33.Window := ⟨6,58,6311,5951,241677146333965963,50229,21000,5000000,81920000000⟩
def h386_0 : Height w386 := ⟨50229,21000,by decide +kernel⟩
def h386_1 : Height w386 := ⟨55070,18000,by decide +kernel⟩
def h386_2 : Height w386 := ⟨61909,15000,by decide +kernel⟩
def h386_3 : Height w386 := ⟨73299,12000,by decide +kernel⟩
def pick386 (cl : ℕ) : Height w386 := if cl<82 then (if cl<13 then (h386_0) else (h386_1)) else (if cl<922 then (h386_2) else (h386_3))
private theorem k386_1_0 : check w386 pick386 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k386_1_1 : check w386 pick386 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k386_1_2 : check w386 pick386 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w386 pick386 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k386_1_0 k386_1_1
private theorem k386_1_3 : check w386 pick386 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k386_1_4 : check w386 pick386 1 t9361 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k386_1_5 : check w386 pick386 1 t9362 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w386 pick386 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9361 k386_1_3 k386_1_4
private theorem k386_1_6 : check w386 pick386 1 t9380 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w386 pick386 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9362 k386_1_2 k386_1_5
private theorem k386_1_7 : check w386 pick386 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k386_1_8 : check w386 pick386 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k386_1_9 : check w386 pick386 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w386 pick386 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k386_1_7 k386_1_8
private theorem k386_1_10 : check w386 pick386 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k386_1_11 : check w386 pick386 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k386_1_12 : check w386 pick386 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w386 pick386 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k386_1_10 k386_1_11
private theorem k386_1_13 : check w386 pick386 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w386 pick386 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k386_1_9 k386_1_12
private theorem k386_1_14 : check w386 pick386 1 t9381 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w386 pick386 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9380 t9212 k386_1_6 k386_1_13
theorem cov386_1 : PA.Covered 1 (OZ.Valid 1 w386.low w386.t w386.y w386.r w386.cap) (P33.root 1) :=
  Night6836Tree.sound w386 pick386 1 t9381 _ k386_1_14
private theorem k386_2_0 : check w386 pick386 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k386_2_1 : check w386 pick386 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k386_2_2 : check w386 pick386 2 t9322 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w386 pick386 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9239 t9321 k386_2_0 k386_2_1
private theorem k386_2_3 : check w386 pick386 2 t3520 ⟨2,7,4,16,2,52,140,220⟩ = true := by decide +kernel
private theorem k386_2_4 : check w386 pick386 2 t9382 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k386_2_5 : check w386 pick386 2 t9503 ⟨2,7,4,16,2,52,140,450⟩ = true := glue w386 pick386 2 ⟨2,7,4,16,2,52,140,450⟩ 3 220 t3520 t9382 k386_2_3 k386_2_4
private theorem k386_2_6 : check w386 pick386 2 t9504 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w386 pick386 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9322 t9503 k386_2_2 k386_2_5
theorem cov386_2 : PA.Covered 2 (OZ.Valid 2 w386.low w386.t w386.y w386.r w386.cap) (P33.root 2) :=
  Night6836Tree.sound w386 pick386 2 t9504 _ k386_2_6
theorem cov386_3 : PA.Covered 3 (OZ.Valid 3 w386.low w386.t w386.y w386.r w386.cap) (P33.root 3) :=
  Night6836Tree.sound w386 pick386 3 t564 _ (by decide +kernel)
theorem cov386_4 : PA.Covered 4 (OZ.Valid 4 w386.low w386.t w386.y w386.r w386.cap) (P33.root 4) :=
  Night6836Tree.sound w386 pick386 4 t565 _ (by decide +kernel)
theorem cov386_5 : PA.Covered 5 (OZ.Valid 5 w386.low w386.t w386.y w386.r w386.cap) (P33.root 5) :=
  Night6836Tree.sound w386 pick386 5 t566 _ (by decide +kernel)
theorem cov386_6 : PA.Covered 6 (OZ.Valid 6 w386.low w386.t w386.y w386.r w386.cap) (P33.root 6) :=
  Night6836Tree.sound w386 pick386 6 t567 _ (by decide +kernel)
theorem cov386_7 : PA.Covered 7 (OZ.Valid 7 w386.low w386.t w386.y w386.r w386.cap) (P33.root 7) :=
  Night6836Tree.sound w386 pick386 7 t2134 _ (by decide +kernel)
theorem window386 : P33.WindowCount w386 := by
  apply P33.window_count w386 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov386_1
  · exact cov386_2
  · exact cov386_3
  · exact cov386_4
  · exact cov386_5
  · exact cov386_6
  · exact cov386_7
def w387 : P33.Window := ⟨6,59,5950,5574,245262501146785048,52675,24000,5000000,81920000000⟩
def h387_0 : Height w387 := ⟨52675,24000,by decide +kernel⟩
def h387_1 : Height w387 := ⟨56933,21000,by decide +kernel⟩
def h387_2 : Height w387 := ⟨62494,18000,by decide +kernel⟩
def h387_3 : Height w387 := ⟨70566,15000,by decide +kernel⟩
def h387_4 : Height w387 := ⟨84507,12000,by decide +kernel⟩
def pick387 (cl : ℕ) : Height w387 := if cl<27 then (if cl<4 then (h387_0) else (h387_1)) else (if cl<194 then (h387_2) else (if cl<989 then (h387_3) else (h387_4)))
private theorem k387_1_0 : check w387 pick387 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k387_1_1 : check w387 pick387 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k387_1_2 : check w387 pick387 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w387 pick387 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k387_1_0 k387_1_1
private theorem k387_1_3 : check w387 pick387 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k387_1_4 : check w387 pick387 1 t9361 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k387_1_5 : check w387 pick387 1 t9362 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w387 pick387 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9361 k387_1_3 k387_1_4
private theorem k387_1_6 : check w387 pick387 1 t9380 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w387 pick387 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9362 k387_1_2 k387_1_5
private theorem k387_1_7 : check w387 pick387 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k387_1_8 : check w387 pick387 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k387_1_9 : check w387 pick387 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w387 pick387 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k387_1_7 k387_1_8
private theorem k387_1_10 : check w387 pick387 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k387_1_11 : check w387 pick387 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k387_1_12 : check w387 pick387 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w387 pick387 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k387_1_10 k387_1_11
private theorem k387_1_13 : check w387 pick387 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w387 pick387 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k387_1_9 k387_1_12
private theorem k387_1_14 : check w387 pick387 1 t9381 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w387 pick387 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9380 t9212 k387_1_6 k387_1_13
theorem cov387_1 : PA.Covered 1 (OZ.Valid 1 w387.low w387.t w387.y w387.r w387.cap) (P33.root 1) :=
  Night6836Tree.sound w387 pick387 1 t9381 _ k387_1_14
private theorem k387_2_0 : check w387 pick387 2 t9239 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k387_2_1 : check w387 pick387 2 t9321 ⟨2,7,4,16,2,52,71,139⟩ = true := by decide +kernel
private theorem k387_2_2 : check w387 pick387 2 t9322 ⟨2,7,4,16,2,52,2,139⟩ = true := glue w387 pick387 2 ⟨2,7,4,16,2,52,2,139⟩ 3 70 t9239 t9321 k387_2_0 k387_2_1
private theorem k387_2_3 : check w387 pick387 2 t9506 ⟨2,7,4,16,2,52,140,450⟩ = true := by decide +kernel
private theorem k387_2_4 : check w387 pick387 2 t9507 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w387 pick387 2 ⟨2,7,4,16,0,52,0,450⟩ 3 139 t9322 t9506 k387_2_2 k387_2_3
theorem cov387_2 : PA.Covered 2 (OZ.Valid 2 w387.low w387.t w387.y w387.r w387.cap) (P33.root 2) :=
  Night6836Tree.sound w387 pick387 2 t9507 _ k387_2_4
theorem cov387_3 : PA.Covered 3 (OZ.Valid 3 w387.low w387.t w387.y w387.r w387.cap) (P33.root 3) :=
  Night6836Tree.sound w387 pick387 3 t564 _ (by decide +kernel)
theorem cov387_4 : PA.Covered 4 (OZ.Valid 4 w387.low w387.t w387.y w387.r w387.cap) (P33.root 4) :=
  Night6836Tree.sound w387 pick387 4 t565 _ (by decide +kernel)
theorem cov387_5 : PA.Covered 5 (OZ.Valid 5 w387.low w387.t w387.y w387.r w387.cap) (P33.root 5) :=
  Night6836Tree.sound w387 pick387 5 t566 _ (by decide +kernel)
theorem cov387_6 : PA.Covered 6 (OZ.Valid 6 w387.low w387.t w387.y w387.r w387.cap) (P33.root 6) :=
  Night6836Tree.sound w387 pick387 6 t567 _ (by decide +kernel)
theorem cov387_7 : PA.Covered 7 (OZ.Valid 7 w387.low w387.t w387.y w387.r w387.cap) (P33.root 7) :=
  Night6836Tree.sound w387 pick387 7 t2134 _ (by decide +kernel)
theorem window387 : P33.WindowCount w387 := by
  apply P33.window_count w387 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov387_1
  · exact cov387_2
  · exact cov387_3
  · exact cov387_4
  · exact cov387_5
  · exact cov387_6
  · exact cov387_7
def w388 : P33.Window := ⟨6,60,5573,5182,244341411825721144,56423,27000,5000000,81920000000⟩
def h388_0 : Height w388 := ⟨56423,27000,by decide +kernel⟩
def h388_1 : Height w388 := ⟨60367,24000,by decide +kernel⟩
def h388_2 : Height w388 := ⟨65269,21000,by decide +kernel⟩
def h388_3 : Height w388 := ⟨71830,18000,by decide +kernel⟩
def h388_4 : Height w388 := ⟨81648,15000,by decide +kernel⟩
def pick388 (cl : ℕ) : Height w388 := if cl<13 then (if cl<2 then (h388_0) else (h388_1)) else (if cl<62 then (h388_2) else (if cl<413 then (h388_3) else (h388_4)))
private theorem k388_1_0 : check w388 pick388 1 t9186 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k388_1_1 : check w388 pick388 1 t9190 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k388_1_2 : check w388 pick388 1 t9191 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w388 pick388 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t9186 t9190 k388_1_0 k388_1_1
private theorem k388_1_3 : check w388 pick388 1 t9203 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k388_1_4 : check w388 pick388 1 t9361 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k388_1_5 : check w388 pick388 1 t9362 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w388 pick388 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t9203 t9361 k388_1_3 k388_1_4
private theorem k388_1_6 : check w388 pick388 1 t9380 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w388 pick388 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t9191 t9362 k388_1_2 k388_1_5
private theorem k388_1_7 : check w388 pick388 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k388_1_8 : check w388 pick388 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k388_1_9 : check w388 pick388 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w388 pick388 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k388_1_7 k388_1_8
private theorem k388_1_10 : check w388 pick388 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k388_1_11 : check w388 pick388 1 t9210 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k388_1_12 : check w388 pick388 1 t9211 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w388 pick388 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t9210 k388_1_10 k388_1_11
private theorem k388_1_13 : check w388 pick388 1 t9212 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w388 pick388 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t9211 k388_1_9 k388_1_12
private theorem k388_1_14 : check w388 pick388 1 t9381 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w388 pick388 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9380 t9212 k388_1_6 k388_1_13
theorem cov388_1 : PA.Covered 1 (OZ.Valid 1 w388.low w388.t w388.y w388.r w388.cap) (P33.root 1) :=
  Night6836Tree.sound w388 pick388 1 t9381 _ k388_1_14
private theorem k388_2_0 : check w388 pick388 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k388_2_1 : check w388 pick388 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k388_2_2 : check w388 pick388 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w388 pick388 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k388_2_0 k388_2_1
theorem cov388_2 : PA.Covered 2 (OZ.Valid 2 w388.low w388.t w388.y w388.r w388.cap) (P33.root 2) :=
  Night6836Tree.sound w388 pick388 2 t9134 _ k388_2_2
theorem cov388_3 : PA.Covered 3 (OZ.Valid 3 w388.low w388.t w388.y w388.r w388.cap) (P33.root 3) :=
  Night6836Tree.sound w388 pick388 3 t564 _ (by decide +kernel)
theorem cov388_4 : PA.Covered 4 (OZ.Valid 4 w388.low w388.t w388.y w388.r w388.cap) (P33.root 4) :=
  Night6836Tree.sound w388 pick388 4 t565 _ (by decide +kernel)
theorem cov388_5 : PA.Covered 5 (OZ.Valid 5 w388.low w388.t w388.y w388.r w388.cap) (P33.root 5) :=
  Night6836Tree.sound w388 pick388 5 t566 _ (by decide +kernel)
theorem cov388_6 : PA.Covered 6 (OZ.Valid 6 w388.low w388.t w388.y w388.r w388.cap) (P33.root 6) :=
  Night6836Tree.sound w388 pick388 6 t567 _ (by decide +kernel)
theorem cov388_7 : PA.Covered 7 (OZ.Valid 7 w388.low w388.t w388.y w388.r w388.cap) (P33.root 7) :=
  Night6836Tree.sound w388 pick388 7 t2134 _ (by decide +kernel)
theorem window388 : P33.WindowCount w388 := by
  apply P33.window_count w388 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov388_1
  · exact cov388_2
  · exact cov388_3
  · exact cov388_4
  · exact cov388_5
  · exact cov388_6
  · exact cov388_7
def w389 : P33.Window := ⟨6,61,5181,4774,244754034815807579,65543,27000,5000000,81920000000⟩
def h389_0 : Height w389 := ⟨65543,27000,by decide +kernel⟩
def h389_1 : Height w389 := ⟨70119,24000,by decide +kernel⟩
def h389_2 : Height w389 := ⟨75940,21000,by decide +kernel⟩
def h389_3 : Height w389 := ⟨83950,18000,by decide +kernel⟩
def pick389 (cl : ℕ) : Height w389 := if cl<32 then (if cl<6 then (h389_0) else (h389_1)) else (if cl<183 then (h389_2) else (h389_3))
private theorem k389_1_0 : check w389 pick389 1 t5132 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k389_1_1 : check w389 pick389 1 t5141 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k389_1_2 : check w389 pick389 1 t5142 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w389 pick389 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5132 t5141 k389_1_0 k389_1_1
private theorem k389_1_3 : check w389 pick389 1 t9162 ⟨1,7,2,16,1,52,84,117⟩ = true := by decide +kernel
private theorem k389_1_4 : check w389 pick389 1 t9512 ⟨1,7,2,16,1,52,118,145⟩ = true := by decide +kernel
private theorem k389_1_5 : check w389 pick389 1 t9513 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w389 pick389 1 ⟨1,7,2,16,1,52,84,145⟩ 3 117 t9162 t9512 k389_1_3 k389_1_4
private theorem k389_1_6 : check w389 pick389 1 t9514 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w389 pick389 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t5142 t9513 k389_1_2 k389_1_5
private theorem k389_1_7 : check w389 pick389 1 t5178 ⟨1,7,2,16,1,52,146,179⟩ = true := by decide +kernel
private theorem k389_1_8 : check w389 pick389 1 t2374 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k389_1_9 : check w389 pick389 1 t5179 ⟨1,7,2,16,1,52,146,206⟩ = true := glue w389 pick389 1 ⟨1,7,2,16,1,52,146,206⟩ 3 179 t5178 t2374 k389_1_7 k389_1_8
private theorem k389_1_10 : check w389 pick389 1 t2385 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k389_1_11 : check w389 pick389 1 t9150 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k389_1_12 : check w389 pick389 1 t9183 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w389 pick389 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t2385 t9150 k389_1_10 k389_1_11
private theorem k389_1_13 : check w389 pick389 1 t9184 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w389 pick389 1 ⟨1,7,2,16,1,52,146,450⟩ 3 206 t5179 t9183 k389_1_9 k389_1_12
private theorem k389_1_14 : check w389 pick389 1 t9515 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w389 pick389 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t9514 t9184 k389_1_6 k389_1_13
theorem cov389_1 : PA.Covered 1 (OZ.Valid 1 w389.low w389.t w389.y w389.r w389.cap) (P33.root 1) :=
  Night6836Tree.sound w389 pick389 1 t9515 _ k389_1_14
private theorem k389_2_0 : check w389 pick389 2 t5460 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k389_2_1 : check w389 pick389 2 t9133 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k389_2_2 : check w389 pick389 2 t9134 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w389 pick389 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t5460 t9133 k389_2_0 k389_2_1
theorem cov389_2 : PA.Covered 2 (OZ.Valid 2 w389.low w389.t w389.y w389.r w389.cap) (P33.root 2) :=
  Night6836Tree.sound w389 pick389 2 t9134 _ k389_2_2
theorem cov389_3 : PA.Covered 3 (OZ.Valid 3 w389.low w389.t w389.y w389.r w389.cap) (P33.root 3) :=
  Night6836Tree.sound w389 pick389 3 t564 _ (by decide +kernel)
theorem cov389_4 : PA.Covered 4 (OZ.Valid 4 w389.low w389.t w389.y w389.r w389.cap) (P33.root 4) :=
  Night6836Tree.sound w389 pick389 4 t565 _ (by decide +kernel)
theorem cov389_5 : PA.Covered 5 (OZ.Valid 5 w389.low w389.t w389.y w389.r w389.cap) (P33.root 5) :=
  Night6836Tree.sound w389 pick389 5 t566 _ (by decide +kernel)
theorem cov389_6 : PA.Covered 6 (OZ.Valid 6 w389.low w389.t w389.y w389.r w389.cap) (P33.root 6) :=
  Night6836Tree.sound w389 pick389 6 t567 _ (by decide +kernel)
theorem cov389_7 : PA.Covered 7 (OZ.Valid 7 w389.low w389.t w389.y w389.r w389.cap) (P33.root 7) :=
  Night6836Tree.sound w389 pick389 7 t2134 _ (by decide +kernel)
theorem window389 : P33.WindowCount w389 := by
  apply P33.window_count w389 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov389_1
  · exact cov389_2
  · exact cov389_3
  · exact cov389_4
  · exact cov389_5
  · exact cov389_6
  · exact cov389_7
end ProximityPrize.SubmissionLower.Night6836Bank
