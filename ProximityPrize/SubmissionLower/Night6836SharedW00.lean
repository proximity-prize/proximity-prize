/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w0 : P33.Window := ⟨5,35,8054,8041,235167741864259710,0,50000,5000000,81920000000⟩
def h0_0 : Height w0 := ⟨0,50000,by decide +kernel⟩
def pick0 (cl : ℕ) : Height w0 := h0_0
private theorem k0_1_0 : check w0 pick0 1 t52 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k0_1_1 : check w0 pick0 1 t125 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k0_1_2 : check w0 pick0 1 t126 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w0 pick0 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t52 t125 k0_1_0 k0_1_1
private theorem k0_1_3 : check w0 pick0 1 t186 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k0_1_4 : check w0 pick0 1 t253 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k0_1_5 : check w0 pick0 1 t254 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w0 pick0 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t186 t253 k0_1_3 k0_1_4
private theorem k0_1_6 : check w0 pick0 1 t255 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w0 pick0 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t126 t254 k0_1_2 k0_1_5
private theorem k0_1_7 : check w0 pick0 1 t325 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k0_1_8 : check w0 pick0 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k0_1_9 : check w0 pick0 1 t383 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w0 pick0 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t325 t382 k0_1_7 k0_1_8
private theorem k0_1_10 : check w0 pick0 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k0_1_11 : check w0 pick0 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k0_1_12 : check w0 pick0 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w0 pick0 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k0_1_10 k0_1_11
private theorem k0_1_13 : check w0 pick0 1 t500 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w0 pick0 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t383 t499 k0_1_9 k0_1_12
private theorem k0_1_14 : check w0 pick0 1 t501 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w0 pick0 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t255 t500 k0_1_6 k0_1_13
theorem cov0_1 : PA.Covered 1 (OZ.Valid 1 w0.low w0.t w0.y w0.r w0.cap) (P33.root 1) :=
  Night6836Tree.sound w0 pick0 1 t501 _ k0_1_14
theorem cov0_2 : PA.Covered 2 (OZ.Valid 2 w0.low w0.t w0.y w0.r w0.cap) (P33.root 2) :=
  Night6836Tree.sound w0 pick0 2 t563 _ (by decide +kernel)
theorem cov0_3 : PA.Covered 3 (OZ.Valid 3 w0.low w0.t w0.y w0.r w0.cap) (P33.root 3) :=
  Night6836Tree.sound w0 pick0 3 t564 _ (by decide +kernel)
theorem cov0_4 : PA.Covered 4 (OZ.Valid 4 w0.low w0.t w0.y w0.r w0.cap) (P33.root 4) :=
  Night6836Tree.sound w0 pick0 4 t565 _ (by decide +kernel)
theorem cov0_5 : PA.Covered 5 (OZ.Valid 5 w0.low w0.t w0.y w0.r w0.cap) (P33.root 5) :=
  Night6836Tree.sound w0 pick0 5 t566 _ (by decide +kernel)
theorem cov0_6 : PA.Covered 6 (OZ.Valid 6 w0.low w0.t w0.y w0.r w0.cap) (P33.root 6) :=
  Night6836Tree.sound w0 pick0 6 t567 _ (by decide +kernel)
theorem cov0_7 : PA.Covered 7 (OZ.Valid 7 w0.low w0.t w0.y w0.r w0.cap) (P33.root 7) :=
  Night6836Tree.sound w0 pick0 7 t568 _ (by decide +kernel)
theorem window0 : P33.WindowCount w0 := by
  apply P33.window_count w0 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov0_1
  · exact cov0_2
  · exact cov0_3
  · exact cov0_4
  · exact cov0_5
  · exact cov0_6
  · exact cov0_7
def w1 : P33.Window := ⟨5,36,8016,7979,235603271018978793,0,50000,5000000,81920000000⟩
def h1_0 : Height w1 := ⟨0,50000,by decide +kernel⟩
def pick1 (cl : ℕ) : Height w1 := h1_0
private theorem k1_1_0 : check w1 pick1 1 t52 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k1_1_1 : check w1 pick1 1 t575 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k1_1_2 : check w1 pick1 1 t576 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w1 pick1 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t52 t575 k1_1_0 k1_1_1
private theorem k1_1_3 : check w1 pick1 1 t186 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k1_1_4 : check w1 pick1 1 t253 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k1_1_5 : check w1 pick1 1 t254 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w1 pick1 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t186 t253 k1_1_3 k1_1_4
private theorem k1_1_6 : check w1 pick1 1 t577 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w1 pick1 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t576 t254 k1_1_2 k1_1_5
private theorem k1_1_7 : check w1 pick1 1 t325 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k1_1_8 : check w1 pick1 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k1_1_9 : check w1 pick1 1 t383 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w1 pick1 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t325 t382 k1_1_7 k1_1_8
private theorem k1_1_10 : check w1 pick1 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k1_1_11 : check w1 pick1 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k1_1_12 : check w1 pick1 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w1 pick1 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k1_1_10 k1_1_11
private theorem k1_1_13 : check w1 pick1 1 t500 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w1 pick1 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t383 t499 k1_1_9 k1_1_12
private theorem k1_1_14 : check w1 pick1 1 t578 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w1 pick1 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t577 t500 k1_1_6 k1_1_13
theorem cov1_1 : PA.Covered 1 (OZ.Valid 1 w1.low w1.t w1.y w1.r w1.cap) (P33.root 1) :=
  Night6836Tree.sound w1 pick1 1 t578 _ k1_1_14
theorem cov1_2 : PA.Covered 2 (OZ.Valid 2 w1.low w1.t w1.y w1.r w1.cap) (P33.root 2) :=
  Night6836Tree.sound w1 pick1 2 t563 _ (by decide +kernel)
theorem cov1_3 : PA.Covered 3 (OZ.Valid 3 w1.low w1.t w1.y w1.r w1.cap) (P33.root 3) :=
  Night6836Tree.sound w1 pick1 3 t564 _ (by decide +kernel)
theorem cov1_4 : PA.Covered 4 (OZ.Valid 4 w1.low w1.t w1.y w1.r w1.cap) (P33.root 4) :=
  Night6836Tree.sound w1 pick1 4 t565 _ (by decide +kernel)
theorem cov1_5 : PA.Covered 5 (OZ.Valid 5 w1.low w1.t w1.y w1.r w1.cap) (P33.root 5) :=
  Night6836Tree.sound w1 pick1 5 t566 _ (by decide +kernel)
theorem cov1_6 : PA.Covered 6 (OZ.Valid 6 w1.low w1.t w1.y w1.r w1.cap) (P33.root 6) :=
  Night6836Tree.sound w1 pick1 6 t567 _ (by decide +kernel)
theorem cov1_7 : PA.Covered 7 (OZ.Valid 7 w1.low w1.t w1.y w1.r w1.cap) (P33.root 7) :=
  Night6836Tree.sound w1 pick1 7 t568 _ (by decide +kernel)
theorem window1 : P33.WindowCount w1 := by
  apply P33.window_count w1 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov1_1
  · exact cov1_2
  · exact cov1_3
  · exact cov1_4
  · exact cov1_5
  · exact cov1_6
  · exact cov1_7
def w2 : P33.Window := ⟨5,37,7978,7941,236031741393475939,0,50000,5000000,81920000000⟩
def h2_0 : Height w2 := ⟨0,50000,by decide +kernel⟩
def pick2 (cl : ℕ) : Height w2 := h2_0
private theorem k2_1_0 : check w2 pick2 1 t52 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k2_1_1 : check w2 pick2 1 t575 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k2_1_2 : check w2 pick2 1 t576 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w2 pick2 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t52 t575 k2_1_0 k2_1_1
private theorem k2_1_3 : check w2 pick2 1 t186 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k2_1_4 : check w2 pick2 1 t253 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k2_1_5 : check w2 pick2 1 t254 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w2 pick2 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t186 t253 k2_1_3 k2_1_4
private theorem k2_1_6 : check w2 pick2 1 t577 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w2 pick2 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t576 t254 k2_1_2 k2_1_5
private theorem k2_1_7 : check w2 pick2 1 t325 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k2_1_8 : check w2 pick2 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k2_1_9 : check w2 pick2 1 t383 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w2 pick2 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t325 t382 k2_1_7 k2_1_8
private theorem k2_1_10 : check w2 pick2 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k2_1_11 : check w2 pick2 1 t498 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k2_1_12 : check w2 pick2 1 t499 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w2 pick2 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t498 k2_1_10 k2_1_11
private theorem k2_1_13 : check w2 pick2 1 t500 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w2 pick2 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t383 t499 k2_1_9 k2_1_12
private theorem k2_1_14 : check w2 pick2 1 t578 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w2 pick2 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t577 t500 k2_1_6 k2_1_13
theorem cov2_1 : PA.Covered 1 (OZ.Valid 1 w2.low w2.t w2.y w2.r w2.cap) (P33.root 1) :=
  Night6836Tree.sound w2 pick2 1 t578 _ k2_1_14
theorem cov2_2 : PA.Covered 2 (OZ.Valid 2 w2.low w2.t w2.y w2.r w2.cap) (P33.root 2) :=
  Night6836Tree.sound w2 pick2 2 t563 _ (by decide +kernel)
theorem cov2_3 : PA.Covered 3 (OZ.Valid 3 w2.low w2.t w2.y w2.r w2.cap) (P33.root 3) :=
  Night6836Tree.sound w2 pick2 3 t564 _ (by decide +kernel)
theorem cov2_4 : PA.Covered 4 (OZ.Valid 4 w2.low w2.t w2.y w2.r w2.cap) (P33.root 4) :=
  Night6836Tree.sound w2 pick2 4 t565 _ (by decide +kernel)
theorem cov2_5 : PA.Covered 5 (OZ.Valid 5 w2.low w2.t w2.y w2.r w2.cap) (P33.root 5) :=
  Night6836Tree.sound w2 pick2 5 t566 _ (by decide +kernel)
theorem cov2_6 : PA.Covered 6 (OZ.Valid 6 w2.low w2.t w2.y w2.r w2.cap) (P33.root 6) :=
  Night6836Tree.sound w2 pick2 6 t567 _ (by decide +kernel)
theorem cov2_7 : PA.Covered 7 (OZ.Valid 7 w2.low w2.t w2.y w2.r w2.cap) (P33.root 7) :=
  Night6836Tree.sound w2 pick2 7 t568 _ (by decide +kernel)
theorem window2 : P33.WindowCount w2 := by
  apply P33.window_count w2 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov2_1
  · exact cov2_2
  · exact cov2_3
  · exact cov2_4
  · exact cov2_5
  · exact cov2_6
  · exact cov2_7
def w3 : P33.Window := ⟨5,38,7940,7863,237444094761085132,0,50000,5000000,81920000000⟩
def h3_0 : Height w3 := ⟨0,50000,by decide +kernel⟩
def pick3 (cl : ℕ) : Height w3 := h3_0
private theorem k3_1_0 : check w3 pick3 1 t52 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k3_1_1 : check w3 pick3 1 t575 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k3_1_2 : check w3 pick3 1 t576 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w3 pick3 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t52 t575 k3_1_0 k3_1_1
private theorem k3_1_3 : check w3 pick3 1 t186 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k3_1_4 : check w3 pick3 1 t253 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k3_1_5 : check w3 pick3 1 t254 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w3 pick3 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t186 t253 k3_1_3 k3_1_4
private theorem k3_1_6 : check w3 pick3 1 t577 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w3 pick3 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t576 t254 k3_1_2 k3_1_5
private theorem k3_1_7 : check w3 pick3 1 t325 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k3_1_8 : check w3 pick3 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k3_1_9 : check w3 pick3 1 t383 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w3 pick3 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t325 t382 k3_1_7 k3_1_8
private theorem k3_1_10 : check w3 pick3 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k3_1_11 : check w3 pick3 1 t588 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k3_1_12 : check w3 pick3 1 t589 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w3 pick3 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t588 k3_1_10 k3_1_11
private theorem k3_1_13 : check w3 pick3 1 t590 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w3 pick3 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t383 t589 k3_1_9 k3_1_12
private theorem k3_1_14 : check w3 pick3 1 t591 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w3 pick3 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t577 t590 k3_1_6 k3_1_13
theorem cov3_1 : PA.Covered 1 (OZ.Valid 1 w3.low w3.t w3.y w3.r w3.cap) (P33.root 1) :=
  Night6836Tree.sound w3 pick3 1 t591 _ k3_1_14
theorem cov3_2 : PA.Covered 2 (OZ.Valid 2 w3.low w3.t w3.y w3.r w3.cap) (P33.root 2) :=
  Night6836Tree.sound w3 pick3 2 t563 _ (by decide +kernel)
theorem cov3_3 : PA.Covered 3 (OZ.Valid 3 w3.low w3.t w3.y w3.r w3.cap) (P33.root 3) :=
  Night6836Tree.sound w3 pick3 3 t564 _ (by decide +kernel)
theorem cov3_4 : PA.Covered 4 (OZ.Valid 4 w3.low w3.t w3.y w3.r w3.cap) (P33.root 4) :=
  Night6836Tree.sound w3 pick3 4 t565 _ (by decide +kernel)
theorem cov3_5 : PA.Covered 5 (OZ.Valid 5 w3.low w3.t w3.y w3.r w3.cap) (P33.root 5) :=
  Night6836Tree.sound w3 pick3 5 t566 _ (by decide +kernel)
theorem cov3_6 : PA.Covered 6 (OZ.Valid 6 w3.low w3.t w3.y w3.r w3.cap) (P33.root 6) :=
  Night6836Tree.sound w3 pick3 6 t567 _ (by decide +kernel)
theorem cov3_7 : PA.Covered 7 (OZ.Valid 7 w3.low w3.t w3.y w3.r w3.cap) (P33.root 7) :=
  Night6836Tree.sound w3 pick3 7 t568 _ (by decide +kernel)
theorem window3 : P33.WindowCount w3 := by
  apply P33.window_count w3 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov3_1
  · exact cov3_2
  · exact cov3_3
  · exact cov3_4
  · exact cov3_5
  · exact cov3_6
  · exact cov3_7
def w4 : P33.Window := ⟨5,39,7901,7863,237570459425997778,0,50000,5000000,81920000000⟩
def h4_0 : Height w4 := ⟨0,50000,by decide +kernel⟩
def pick4 (cl : ℕ) : Height w4 := h4_0
private theorem k4_1_0 : check w4 pick4 1 t606 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k4_1_1 : check w4 pick4 1 t575 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k4_1_2 : check w4 pick4 1 t607 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w4 pick4 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t606 t575 k4_1_0 k4_1_1
private theorem k4_1_3 : check w4 pick4 1 t622 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k4_1_4 : check w4 pick4 1 t642 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k4_1_5 : check w4 pick4 1 t643 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w4 pick4 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t622 t642 k4_1_3 k4_1_4
private theorem k4_1_6 : check w4 pick4 1 t644 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w4 pick4 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t607 t643 k4_1_2 k4_1_5
private theorem k4_1_7 : check w4 pick4 1 t696 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k4_1_8 : check w4 pick4 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k4_1_9 : check w4 pick4 1 t737 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w4 pick4 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t696 t736 k4_1_7 k4_1_8
private theorem k4_1_10 : check w4 pick4 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k4_1_11 : check w4 pick4 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k4_1_12 : check w4 pick4 1 t787 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w4 pick4 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t786 k4_1_10 k4_1_11
private theorem k4_1_13 : check w4 pick4 1 t788 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w4 pick4 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t737 t787 k4_1_9 k4_1_12
private theorem k4_1_14 : check w4 pick4 1 t789 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w4 pick4 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t644 t788 k4_1_6 k4_1_13
theorem cov4_1 : PA.Covered 1 (OZ.Valid 1 w4.low w4.t w4.y w4.r w4.cap) (P33.root 1) :=
  Night6836Tree.sound w4 pick4 1 t789 _ k4_1_14
theorem cov4_2 : PA.Covered 2 (OZ.Valid 2 w4.low w4.t w4.y w4.r w4.cap) (P33.root 2) :=
  Night6836Tree.sound w4 pick4 2 t563 _ (by decide +kernel)
theorem cov4_3 : PA.Covered 3 (OZ.Valid 3 w4.low w4.t w4.y w4.r w4.cap) (P33.root 3) :=
  Night6836Tree.sound w4 pick4 3 t564 _ (by decide +kernel)
theorem cov4_4 : PA.Covered 4 (OZ.Valid 4 w4.low w4.t w4.y w4.r w4.cap) (P33.root 4) :=
  Night6836Tree.sound w4 pick4 4 t565 _ (by decide +kernel)
theorem cov4_5 : PA.Covered 5 (OZ.Valid 5 w4.low w4.t w4.y w4.r w4.cap) (P33.root 5) :=
  Night6836Tree.sound w4 pick4 5 t566 _ (by decide +kernel)
theorem cov4_6 : PA.Covered 6 (OZ.Valid 6 w4.low w4.t w4.y w4.r w4.cap) (P33.root 6) :=
  Night6836Tree.sound w4 pick4 6 t567 _ (by decide +kernel)
theorem cov4_7 : PA.Covered 7 (OZ.Valid 7 w4.low w4.t w4.y w4.r w4.cap) (P33.root 7) :=
  Night6836Tree.sound w4 pick4 7 t568 _ (by decide +kernel)
theorem window4 : P33.WindowCount w4 := by
  apply P33.window_count w4 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov4_1
  · exact cov4_2
  · exact cov4_3
  · exact cov4_4
  · exact cov4_5
  · exact cov4_6
  · exact cov4_7
def w5 : P33.Window := ⟨5,40,7862,7823,236488634591415209,605,50000,5000000,81920000000⟩
def h5_0 : Height w5 := ⟨605,50000,by decide +kernel⟩
def pick5 (cl : ℕ) : Height w5 := h5_0
private theorem k5_1_0 : check w5 pick5 1 t801 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k5_1_1 : check w5 pick5 1 t834 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k5_1_2 : check w5 pick5 1 t835 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w5 pick5 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t801 t834 k5_1_0 k5_1_1
private theorem k5_1_3 : check w5 pick5 1 t873 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k5_1_4 : check w5 pick5 1 t900 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k5_1_5 : check w5 pick5 1 t901 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w5 pick5 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t873 t900 k5_1_3 k5_1_4
private theorem k5_1_6 : check w5 pick5 1 t902 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w5 pick5 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t835 t901 k5_1_2 k5_1_5
private theorem k5_1_7 : check w5 pick5 1 t696 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k5_1_8 : check w5 pick5 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k5_1_9 : check w5 pick5 1 t737 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w5 pick5 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t696 t736 k5_1_7 k5_1_8
private theorem k5_1_10 : check w5 pick5 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k5_1_11 : check w5 pick5 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k5_1_12 : check w5 pick5 1 t787 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w5 pick5 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t786 k5_1_10 k5_1_11
private theorem k5_1_13 : check w5 pick5 1 t788 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w5 pick5 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t737 t787 k5_1_9 k5_1_12
private theorem k5_1_14 : check w5 pick5 1 t903 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w5 pick5 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t902 t788 k5_1_6 k5_1_13
theorem cov5_1 : PA.Covered 1 (OZ.Valid 1 w5.low w5.t w5.y w5.r w5.cap) (P33.root 1) :=
  Night6836Tree.sound w5 pick5 1 t903 _ k5_1_14
theorem cov5_2 : PA.Covered 2 (OZ.Valid 2 w5.low w5.t w5.y w5.r w5.cap) (P33.root 2) :=
  Night6836Tree.sound w5 pick5 2 t563 _ (by decide +kernel)
theorem cov5_3 : PA.Covered 3 (OZ.Valid 3 w5.low w5.t w5.y w5.r w5.cap) (P33.root 3) :=
  Night6836Tree.sound w5 pick5 3 t564 _ (by decide +kernel)
theorem cov5_4 : PA.Covered 4 (OZ.Valid 4 w5.low w5.t w5.y w5.r w5.cap) (P33.root 4) :=
  Night6836Tree.sound w5 pick5 4 t565 _ (by decide +kernel)
theorem cov5_5 : PA.Covered 5 (OZ.Valid 5 w5.low w5.t w5.y w5.r w5.cap) (P33.root 5) :=
  Night6836Tree.sound w5 pick5 5 t566 _ (by decide +kernel)
theorem cov5_6 : PA.Covered 6 (OZ.Valid 6 w5.low w5.t w5.y w5.r w5.cap) (P33.root 6) :=
  Night6836Tree.sound w5 pick5 6 t567 _ (by decide +kernel)
theorem cov5_7 : PA.Covered 7 (OZ.Valid 7 w5.low w5.t w5.y w5.r w5.cap) (P33.root 7) :=
  Night6836Tree.sound w5 pick5 7 t568 _ (by decide +kernel)
theorem window5 : P33.WindowCount w5 := by
  apply P33.window_count w5 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov5_1
  · exact cov5_2
  · exact cov5_3
  · exact cov5_4
  · exact cov5_5
  · exact cov5_6
  · exact cov5_7
def w6 : P33.Window := ⟨5,41,7822,7658,232351156167436127,1894,50000,5000000,81920000000⟩
def h6_0 : Height w6 := ⟨1894,50000,by decide +kernel⟩
def pick6 (cl : ℕ) : Height w6 := h6_0
private theorem k6_1_0 : check w6 pick6 1 t801 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k6_1_1 : check w6 pick6 1 t834 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k6_1_2 : check w6 pick6 1 t835 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w6 pick6 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t801 t834 k6_1_0 k6_1_1
private theorem k6_1_3 : check w6 pick6 1 t911 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k6_1_4 : check w6 pick6 1 t923 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k6_1_5 : check w6 pick6 1 t924 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w6 pick6 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t911 t923 k6_1_3 k6_1_4
private theorem k6_1_6 : check w6 pick6 1 t925 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w6 pick6 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t835 t924 k6_1_2 k6_1_5
private theorem k6_1_7 : check w6 pick6 1 t696 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k6_1_8 : check w6 pick6 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k6_1_9 : check w6 pick6 1 t737 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w6 pick6 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t696 t736 k6_1_7 k6_1_8
private theorem k6_1_10 : check w6 pick6 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k6_1_11 : check w6 pick6 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k6_1_12 : check w6 pick6 1 t787 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w6 pick6 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t786 k6_1_10 k6_1_11
private theorem k6_1_13 : check w6 pick6 1 t788 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w6 pick6 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t737 t787 k6_1_9 k6_1_12
private theorem k6_1_14 : check w6 pick6 1 t926 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w6 pick6 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t925 t788 k6_1_6 k6_1_13
theorem cov6_1 : PA.Covered 1 (OZ.Valid 1 w6.low w6.t w6.y w6.r w6.cap) (P33.root 1) :=
  Night6836Tree.sound w6 pick6 1 t926 _ k6_1_14
theorem cov6_2 : PA.Covered 2 (OZ.Valid 2 w6.low w6.t w6.y w6.r w6.cap) (P33.root 2) :=
  Night6836Tree.sound w6 pick6 2 t563 _ (by decide +kernel)
theorem cov6_3 : PA.Covered 3 (OZ.Valid 3 w6.low w6.t w6.y w6.r w6.cap) (P33.root 3) :=
  Night6836Tree.sound w6 pick6 3 t564 _ (by decide +kernel)
theorem cov6_4 : PA.Covered 4 (OZ.Valid 4 w6.low w6.t w6.y w6.r w6.cap) (P33.root 4) :=
  Night6836Tree.sound w6 pick6 4 t565 _ (by decide +kernel)
theorem cov6_5 : PA.Covered 5 (OZ.Valid 5 w6.low w6.t w6.y w6.r w6.cap) (P33.root 5) :=
  Night6836Tree.sound w6 pick6 5 t566 _ (by decide +kernel)
theorem cov6_6 : PA.Covered 6 (OZ.Valid 6 w6.low w6.t w6.y w6.r w6.cap) (P33.root 6) :=
  Night6836Tree.sound w6 pick6 6 t567 _ (by decide +kernel)
theorem cov6_7 : PA.Covered 7 (OZ.Valid 7 w6.low w6.t w6.y w6.r w6.cap) (P33.root 7) :=
  Night6836Tree.sound w6 pick6 7 t568 _ (by decide +kernel)
theorem window6 : P33.WindowCount w6 := by
  apply P33.window_count w6 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov6_1
  · exact cov6_2
  · exact cov6_3
  · exact cov6_4
  · exact cov6_5
  · exact cov6_6
  · exact cov6_7
def w7 : P33.Window := ⟨5,42,7781,7742,234253621714541943,2272,50000,5000000,81920000000⟩
def h7_0 : Height w7 := ⟨2272,50000,by decide +kernel⟩
def pick7 (cl : ℕ) : Height w7 := h7_0
private theorem k7_1_0 : check w7 pick7 1 t801 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k7_1_1 : check w7 pick7 1 t834 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k7_1_2 : check w7 pick7 1 t835 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w7 pick7 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t801 t834 k7_1_0 k7_1_1
private theorem k7_1_3 : check w7 pick7 1 t911 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k7_1_4 : check w7 pick7 1 t923 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k7_1_5 : check w7 pick7 1 t924 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w7 pick7 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t911 t923 k7_1_3 k7_1_4
private theorem k7_1_6 : check w7 pick7 1 t925 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w7 pick7 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t835 t924 k7_1_2 k7_1_5
private theorem k7_1_7 : check w7 pick7 1 t696 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k7_1_8 : check w7 pick7 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k7_1_9 : check w7 pick7 1 t737 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w7 pick7 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t696 t736 k7_1_7 k7_1_8
private theorem k7_1_10 : check w7 pick7 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k7_1_11 : check w7 pick7 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k7_1_12 : check w7 pick7 1 t787 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w7 pick7 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t786 k7_1_10 k7_1_11
private theorem k7_1_13 : check w7 pick7 1 t788 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w7 pick7 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t737 t787 k7_1_9 k7_1_12
private theorem k7_1_14 : check w7 pick7 1 t926 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w7 pick7 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t925 t788 k7_1_6 k7_1_13
theorem cov7_1 : PA.Covered 1 (OZ.Valid 1 w7.low w7.t w7.y w7.r w7.cap) (P33.root 1) :=
  Night6836Tree.sound w7 pick7 1 t926 _ k7_1_14
theorem cov7_2 : PA.Covered 2 (OZ.Valid 2 w7.low w7.t w7.y w7.r w7.cap) (P33.root 2) :=
  Night6836Tree.sound w7 pick7 2 t563 _ (by decide +kernel)
theorem cov7_3 : PA.Covered 3 (OZ.Valid 3 w7.low w7.t w7.y w7.r w7.cap) (P33.root 3) :=
  Night6836Tree.sound w7 pick7 3 t564 _ (by decide +kernel)
theorem cov7_4 : PA.Covered 4 (OZ.Valid 4 w7.low w7.t w7.y w7.r w7.cap) (P33.root 4) :=
  Night6836Tree.sound w7 pick7 4 t565 _ (by decide +kernel)
theorem cov7_5 : PA.Covered 5 (OZ.Valid 5 w7.low w7.t w7.y w7.r w7.cap) (P33.root 5) :=
  Night6836Tree.sound w7 pick7 5 t566 _ (by decide +kernel)
theorem cov7_6 : PA.Covered 6 (OZ.Valid 6 w7.low w7.t w7.y w7.r w7.cap) (P33.root 6) :=
  Night6836Tree.sound w7 pick7 6 t567 _ (by decide +kernel)
theorem cov7_7 : PA.Covered 7 (OZ.Valid 7 w7.low w7.t w7.y w7.r w7.cap) (P33.root 7) :=
  Night6836Tree.sound w7 pick7 7 t568 _ (by decide +kernel)
theorem window7 : P33.WindowCount w7 := by
  apply P33.window_count w7 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov7_1
  · exact cov7_2
  · exact cov7_3
  · exact cov7_4
  · exact cov7_5
  · exact cov7_6
  · exact cov7_7
def w8 : P33.Window := ⟨5,43,7741,7700,237096322464774735,3126,50000,5000000,81920000000⟩
def h8_0 : Height w8 := ⟨3126,50000,by decide +kernel⟩
def pick8 (cl : ℕ) : Height w8 := h8_0
private theorem k8_1_0 : check w8 pick8 1 t801 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k8_1_1 : check w8 pick8 1 t834 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k8_1_2 : check w8 pick8 1 t835 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w8 pick8 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t801 t834 k8_1_0 k8_1_1
private theorem k8_1_3 : check w8 pick8 1 t911 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k8_1_4 : check w8 pick8 1 t923 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k8_1_5 : check w8 pick8 1 t924 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w8 pick8 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t911 t923 k8_1_3 k8_1_4
private theorem k8_1_6 : check w8 pick8 1 t925 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w8 pick8 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t835 t924 k8_1_2 k8_1_5
private theorem k8_1_7 : check w8 pick8 1 t696 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k8_1_8 : check w8 pick8 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k8_1_9 : check w8 pick8 1 t737 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w8 pick8 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t696 t736 k8_1_7 k8_1_8
private theorem k8_1_10 : check w8 pick8 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k8_1_11 : check w8 pick8 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k8_1_12 : check w8 pick8 1 t787 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w8 pick8 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t786 k8_1_10 k8_1_11
private theorem k8_1_13 : check w8 pick8 1 t788 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w8 pick8 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t737 t787 k8_1_9 k8_1_12
private theorem k8_1_14 : check w8 pick8 1 t926 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w8 pick8 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t925 t788 k8_1_6 k8_1_13
theorem cov8_1 : PA.Covered 1 (OZ.Valid 1 w8.low w8.t w8.y w8.r w8.cap) (P33.root 1) :=
  Night6836Tree.sound w8 pick8 1 t926 _ k8_1_14
theorem cov8_2 : PA.Covered 2 (OZ.Valid 2 w8.low w8.t w8.y w8.r w8.cap) (P33.root 2) :=
  Night6836Tree.sound w8 pick8 2 t563 _ (by decide +kernel)
theorem cov8_3 : PA.Covered 3 (OZ.Valid 3 w8.low w8.t w8.y w8.r w8.cap) (P33.root 3) :=
  Night6836Tree.sound w8 pick8 3 t564 _ (by decide +kernel)
theorem cov8_4 : PA.Covered 4 (OZ.Valid 4 w8.low w8.t w8.y w8.r w8.cap) (P33.root 4) :=
  Night6836Tree.sound w8 pick8 4 t565 _ (by decide +kernel)
theorem cov8_5 : PA.Covered 5 (OZ.Valid 5 w8.low w8.t w8.y w8.r w8.cap) (P33.root 5) :=
  Night6836Tree.sound w8 pick8 5 t566 _ (by decide +kernel)
theorem cov8_6 : PA.Covered 6 (OZ.Valid 6 w8.low w8.t w8.y w8.r w8.cap) (P33.root 6) :=
  Night6836Tree.sound w8 pick8 6 t567 _ (by decide +kernel)
theorem cov8_7 : PA.Covered 7 (OZ.Valid 7 w8.low w8.t w8.y w8.r w8.cap) (P33.root 7) :=
  Night6836Tree.sound w8 pick8 7 t568 _ (by decide +kernel)
theorem window8 : P33.WindowCount w8 := by
  apply P33.window_count w8 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov8_1
  · exact cov8_2
  · exact cov8_3
  · exact cov8_4
  · exact cov8_5
  · exact cov8_6
  · exact cov8_7
def w9 : P33.Window := ⟨5,44,7699,7658,237688411614930534,3989,50000,5000000,81920000000⟩
def h9_0 : Height w9 := ⟨3989,50000,by decide +kernel⟩
def pick9 (cl : ℕ) : Height w9 := h9_0
private theorem k9_1_0 : check w9 pick9 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k9_1_1 : check w9 pick9 1 t976 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k9_1_2 : check w9 pick9 1 t977 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w9 pick9 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t950 t976 k9_1_0 k9_1_1
private theorem k9_1_3 : check w9 pick9 1 t1011 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k9_1_4 : check w9 pick9 1 t1028 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k9_1_5 : check w9 pick9 1 t1029 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w9 pick9 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t1011 t1028 k9_1_3 k9_1_4
private theorem k9_1_6 : check w9 pick9 1 t1030 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w9 pick9 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t977 t1029 k9_1_2 k9_1_5
private theorem k9_1_7 : check w9 pick9 1 t1054 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k9_1_8 : check w9 pick9 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k9_1_9 : check w9 pick9 1 t1067 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w9 pick9 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1054 t1066 k9_1_7 k9_1_8
private theorem k9_1_10 : check w9 pick9 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k9_1_11 : check w9 pick9 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k9_1_12 : check w9 pick9 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w9 pick9 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k9_1_10 k9_1_11
private theorem k9_1_13 : check w9 pick9 1 t1080 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w9 pick9 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1067 t1079 k9_1_9 k9_1_12
private theorem k9_1_14 : check w9 pick9 1 t1081 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w9 pick9 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1030 t1080 k9_1_6 k9_1_13
theorem cov9_1 : PA.Covered 1 (OZ.Valid 1 w9.low w9.t w9.y w9.r w9.cap) (P33.root 1) :=
  Night6836Tree.sound w9 pick9 1 t1081 _ k9_1_14
theorem cov9_2 : PA.Covered 2 (OZ.Valid 2 w9.low w9.t w9.y w9.r w9.cap) (P33.root 2) :=
  Night6836Tree.sound w9 pick9 2 t1129 _ (by decide +kernel)
theorem cov9_3 : PA.Covered 3 (OZ.Valid 3 w9.low w9.t w9.y w9.r w9.cap) (P33.root 3) :=
  Night6836Tree.sound w9 pick9 3 t564 _ (by decide +kernel)
theorem cov9_4 : PA.Covered 4 (OZ.Valid 4 w9.low w9.t w9.y w9.r w9.cap) (P33.root 4) :=
  Night6836Tree.sound w9 pick9 4 t565 _ (by decide +kernel)
theorem cov9_5 : PA.Covered 5 (OZ.Valid 5 w9.low w9.t w9.y w9.r w9.cap) (P33.root 5) :=
  Night6836Tree.sound w9 pick9 5 t566 _ (by decide +kernel)
theorem cov9_6 : PA.Covered 6 (OZ.Valid 6 w9.low w9.t w9.y w9.r w9.cap) (P33.root 6) :=
  Night6836Tree.sound w9 pick9 6 t567 _ (by decide +kernel)
theorem cov9_7 : PA.Covered 7 (OZ.Valid 7 w9.low w9.t w9.y w9.r w9.cap) (P33.root 7) :=
  Night6836Tree.sound w9 pick9 7 t568 _ (by decide +kernel)
theorem window9 : P33.WindowCount w9 := by
  apply P33.window_count w9 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov9_1
  · exact cov9_2
  · exact cov9_3
  · exact cov9_4
  · exact cov9_5
  · exact cov9_6
  · exact cov9_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w10 : P33.Window := ⟨5,45,7657,7616,236299827436981578,4863,50000,5000000,81920000000⟩
def h10_0 : Height w10 := ⟨4863,50000,by decide +kernel⟩
def pick10 (cl : ℕ) : Height w10 := h10_0
private theorem k10_1_0 : check w10 pick10 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k10_1_1 : check w10 pick10 1 t976 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k10_1_2 : check w10 pick10 1 t977 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w10 pick10 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t950 t976 k10_1_0 k10_1_1
private theorem k10_1_3 : check w10 pick10 1 t1011 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k10_1_4 : check w10 pick10 1 t1028 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k10_1_5 : check w10 pick10 1 t1029 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w10 pick10 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t1011 t1028 k10_1_3 k10_1_4
private theorem k10_1_6 : check w10 pick10 1 t1030 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w10 pick10 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t977 t1029 k10_1_2 k10_1_5
private theorem k10_1_7 : check w10 pick10 1 t1054 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k10_1_8 : check w10 pick10 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k10_1_9 : check w10 pick10 1 t1067 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w10 pick10 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1054 t1066 k10_1_7 k10_1_8
private theorem k10_1_10 : check w10 pick10 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k10_1_11 : check w10 pick10 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k10_1_12 : check w10 pick10 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w10 pick10 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k10_1_10 k10_1_11
private theorem k10_1_13 : check w10 pick10 1 t1080 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w10 pick10 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1067 t1079 k10_1_9 k10_1_12
private theorem k10_1_14 : check w10 pick10 1 t1081 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w10 pick10 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1030 t1080 k10_1_6 k10_1_13
theorem cov10_1 : PA.Covered 1 (OZ.Valid 1 w10.low w10.t w10.y w10.r w10.cap) (P33.root 1) :=
  Night6836Tree.sound w10 pick10 1 t1081 _ k10_1_14
private theorem k10_2_0 : check w10 pick10 2 t1172 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k10_2_1 : check w10 pick10 2 t1198 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k10_2_2 : check w10 pick10 2 t1199 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w10 pick10 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t1172 t1198 k10_2_0 k10_2_1
theorem cov10_2 : PA.Covered 2 (OZ.Valid 2 w10.low w10.t w10.y w10.r w10.cap) (P33.root 2) :=
  Night6836Tree.sound w10 pick10 2 t1199 _ k10_2_2
theorem cov10_3 : PA.Covered 3 (OZ.Valid 3 w10.low w10.t w10.y w10.r w10.cap) (P33.root 3) :=
  Night6836Tree.sound w10 pick10 3 t564 _ (by decide +kernel)
theorem cov10_4 : PA.Covered 4 (OZ.Valid 4 w10.low w10.t w10.y w10.r w10.cap) (P33.root 4) :=
  Night6836Tree.sound w10 pick10 4 t565 _ (by decide +kernel)
theorem cov10_5 : PA.Covered 5 (OZ.Valid 5 w10.low w10.t w10.y w10.r w10.cap) (P33.root 5) :=
  Night6836Tree.sound w10 pick10 5 t566 _ (by decide +kernel)
theorem cov10_6 : PA.Covered 6 (OZ.Valid 6 w10.low w10.t w10.y w10.r w10.cap) (P33.root 6) :=
  Night6836Tree.sound w10 pick10 6 t567 _ (by decide +kernel)
theorem cov10_7 : PA.Covered 7 (OZ.Valid 7 w10.low w10.t w10.y w10.r w10.cap) (P33.root 7) :=
  Night6836Tree.sound w10 pick10 7 t568 _ (by decide +kernel)
theorem window10 : P33.WindowCount w10 := by
  apply P33.window_count w10 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov10_1
  · exact cov10_2
  · exact cov10_3
  · exact cov10_4
  · exact cov10_5
  · exact cov10_6
  · exact cov10_7
def w11 : P33.Window := ⟨5,46,7615,7573,237359167171700812,5751,50000,5000000,81920000000⟩
def h11_0 : Height w11 := ⟨5751,50000,by decide +kernel⟩
def pick11 (cl : ℕ) : Height w11 := h11_0
private theorem k11_1_0 : check w11 pick11 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k11_1_1 : check w11 pick11 1 t976 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k11_1_2 : check w11 pick11 1 t977 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w11 pick11 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t950 t976 k11_1_0 k11_1_1
private theorem k11_1_3 : check w11 pick11 1 t1011 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k11_1_4 : check w11 pick11 1 t1028 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k11_1_5 : check w11 pick11 1 t1029 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w11 pick11 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t1011 t1028 k11_1_3 k11_1_4
private theorem k11_1_6 : check w11 pick11 1 t1030 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w11 pick11 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t977 t1029 k11_1_2 k11_1_5
private theorem k11_1_7 : check w11 pick11 1 t1054 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k11_1_8 : check w11 pick11 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k11_1_9 : check w11 pick11 1 t1067 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w11 pick11 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1054 t1066 k11_1_7 k11_1_8
private theorem k11_1_10 : check w11 pick11 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k11_1_11 : check w11 pick11 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k11_1_12 : check w11 pick11 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w11 pick11 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k11_1_10 k11_1_11
private theorem k11_1_13 : check w11 pick11 1 t1080 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w11 pick11 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1067 t1079 k11_1_9 k11_1_12
private theorem k11_1_14 : check w11 pick11 1 t1081 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w11 pick11 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1030 t1080 k11_1_6 k11_1_13
theorem cov11_1 : PA.Covered 1 (OZ.Valid 1 w11.low w11.t w11.y w11.r w11.cap) (P33.root 1) :=
  Night6836Tree.sound w11 pick11 1 t1081 _ k11_1_14
private theorem k11_2_0 : check w11 pick11 2 t1172 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k11_2_1 : check w11 pick11 2 t1198 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k11_2_2 : check w11 pick11 2 t1199 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w11 pick11 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t1172 t1198 k11_2_0 k11_2_1
theorem cov11_2 : PA.Covered 2 (OZ.Valid 2 w11.low w11.t w11.y w11.r w11.cap) (P33.root 2) :=
  Night6836Tree.sound w11 pick11 2 t1199 _ k11_2_2
theorem cov11_3 : PA.Covered 3 (OZ.Valid 3 w11.low w11.t w11.y w11.r w11.cap) (P33.root 3) :=
  Night6836Tree.sound w11 pick11 3 t564 _ (by decide +kernel)
theorem cov11_4 : PA.Covered 4 (OZ.Valid 4 w11.low w11.t w11.y w11.r w11.cap) (P33.root 4) :=
  Night6836Tree.sound w11 pick11 4 t565 _ (by decide +kernel)
theorem cov11_5 : PA.Covered 5 (OZ.Valid 5 w11.low w11.t w11.y w11.r w11.cap) (P33.root 5) :=
  Night6836Tree.sound w11 pick11 5 t566 _ (by decide +kernel)
theorem cov11_6 : PA.Covered 6 (OZ.Valid 6 w11.low w11.t w11.y w11.r w11.cap) (P33.root 6) :=
  Night6836Tree.sound w11 pick11 6 t567 _ (by decide +kernel)
theorem cov11_7 : PA.Covered 7 (OZ.Valid 7 w11.low w11.t w11.y w11.r w11.cap) (P33.root 7) :=
  Night6836Tree.sound w11 pick11 7 t568 _ (by decide +kernel)
theorem window11 : P33.WindowCount w11 := by
  apply P33.window_count w11 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov11_1
  · exact cov11_2
  · exact cov11_3
  · exact cov11_4
  · exact cov11_5
  · exact cov11_6
  · exact cov11_7
def w12 : P33.Window := ⟨5,47,7572,7526,237215962847034778,6669,50000,5000000,81920000000⟩
def h12_0 : Height w12 := ⟨6669,50000,by decide +kernel⟩
def pick12 (cl : ℕ) : Height w12 := h12_0
private theorem k12_1_0 : check w12 pick12 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k12_1_1 : check w12 pick12 1 t976 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k12_1_2 : check w12 pick12 1 t977 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w12 pick12 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t950 t976 k12_1_0 k12_1_1
private theorem k12_1_3 : check w12 pick12 1 t1011 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k12_1_4 : check w12 pick12 1 t1213 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k12_1_5 : check w12 pick12 1 t1214 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w12 pick12 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t1011 t1213 k12_1_3 k12_1_4
private theorem k12_1_6 : check w12 pick12 1 t1215 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w12 pick12 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t977 t1214 k12_1_2 k12_1_5
private theorem k12_1_7 : check w12 pick12 1 t1218 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k12_1_8 : check w12 pick12 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k12_1_9 : check w12 pick12 1 t1219 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w12 pick12 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1218 t1066 k12_1_7 k12_1_8
private theorem k12_1_10 : check w12 pick12 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k12_1_11 : check w12 pick12 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k12_1_12 : check w12 pick12 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w12 pick12 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k12_1_10 k12_1_11
private theorem k12_1_13 : check w12 pick12 1 t1220 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w12 pick12 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1219 t1079 k12_1_9 k12_1_12
private theorem k12_1_14 : check w12 pick12 1 t1221 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w12 pick12 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1215 t1220 k12_1_6 k12_1_13
theorem cov12_1 : PA.Covered 1 (OZ.Valid 1 w12.low w12.t w12.y w12.r w12.cap) (P33.root 1) :=
  Night6836Tree.sound w12 pick12 1 t1221 _ k12_1_14
private theorem k12_2_0 : check w12 pick12 2 t1172 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k12_2_1 : check w12 pick12 2 t1198 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k12_2_2 : check w12 pick12 2 t1199 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w12 pick12 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t1172 t1198 k12_2_0 k12_2_1
theorem cov12_2 : PA.Covered 2 (OZ.Valid 2 w12.low w12.t w12.y w12.r w12.cap) (P33.root 2) :=
  Night6836Tree.sound w12 pick12 2 t1199 _ k12_2_2
theorem cov12_3 : PA.Covered 3 (OZ.Valid 3 w12.low w12.t w12.y w12.r w12.cap) (P33.root 3) :=
  Night6836Tree.sound w12 pick12 3 t564 _ (by decide +kernel)
theorem cov12_4 : PA.Covered 4 (OZ.Valid 4 w12.low w12.t w12.y w12.r w12.cap) (P33.root 4) :=
  Night6836Tree.sound w12 pick12 4 t565 _ (by decide +kernel)
theorem cov12_5 : PA.Covered 5 (OZ.Valid 5 w12.low w12.t w12.y w12.r w12.cap) (P33.root 5) :=
  Night6836Tree.sound w12 pick12 5 t566 _ (by decide +kernel)
theorem cov12_6 : PA.Covered 6 (OZ.Valid 6 w12.low w12.t w12.y w12.r w12.cap) (P33.root 6) :=
  Night6836Tree.sound w12 pick12 6 t567 _ (by decide +kernel)
theorem cov12_7 : PA.Covered 7 (OZ.Valid 7 w12.low w12.t w12.y w12.r w12.cap) (P33.root 7) :=
  Night6836Tree.sound w12 pick12 7 t568 _ (by decide +kernel)
theorem window12 : P33.WindowCount w12 := by
  apply P33.window_count w12 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov12_1
  · exact cov12_2
  · exact cov12_3
  · exact cov12_4
  · exact cov12_5
  · exact cov12_6
  · exact cov12_7
def w13 : P33.Window := ⟨5,48,7525,7505,237552302502953548,7477,50000,5000000,81920000000⟩
def h13_0 : Height w13 := ⟨7477,50000,by decide +kernel⟩
def pick13 (cl : ℕ) : Height w13 := h13_0
private theorem k13_1_0 : check w13 pick13 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k13_1_1 : check w13 pick13 1 t1233 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k13_1_2 : check w13 pick13 1 t1234 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w13 pick13 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t950 t1233 k13_1_0 k13_1_1
private theorem k13_1_3 : check w13 pick13 1 t1243 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k13_1_4 : check w13 pick13 1 t1213 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k13_1_5 : check w13 pick13 1 t1244 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w13 pick13 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t1243 t1213 k13_1_3 k13_1_4
private theorem k13_1_6 : check w13 pick13 1 t1245 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w13 pick13 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t1234 t1244 k13_1_2 k13_1_5
private theorem k13_1_7 : check w13 pick13 1 t1251 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k13_1_8 : check w13 pick13 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k13_1_9 : check w13 pick13 1 t1252 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w13 pick13 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1251 t1066 k13_1_7 k13_1_8
private theorem k13_1_10 : check w13 pick13 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k13_1_11 : check w13 pick13 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k13_1_12 : check w13 pick13 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w13 pick13 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k13_1_10 k13_1_11
private theorem k13_1_13 : check w13 pick13 1 t1253 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w13 pick13 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1252 t1079 k13_1_9 k13_1_12
private theorem k13_1_14 : check w13 pick13 1 t1254 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w13 pick13 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1245 t1253 k13_1_6 k13_1_13
theorem cov13_1 : PA.Covered 1 (OZ.Valid 1 w13.low w13.t w13.y w13.r w13.cap) (P33.root 1) :=
  Night6836Tree.sound w13 pick13 1 t1254 _ k13_1_14
private theorem k13_2_0 : check w13 pick13 2 t1172 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k13_2_1 : check w13 pick13 2 t1198 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k13_2_2 : check w13 pick13 2 t1199 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w13 pick13 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t1172 t1198 k13_2_0 k13_2_1
theorem cov13_2 : PA.Covered 2 (OZ.Valid 2 w13.low w13.t w13.y w13.r w13.cap) (P33.root 2) :=
  Night6836Tree.sound w13 pick13 2 t1199 _ k13_2_2
theorem cov13_3 : PA.Covered 3 (OZ.Valid 3 w13.low w13.t w13.y w13.r w13.cap) (P33.root 3) :=
  Night6836Tree.sound w13 pick13 3 t564 _ (by decide +kernel)
theorem cov13_4 : PA.Covered 4 (OZ.Valid 4 w13.low w13.t w13.y w13.r w13.cap) (P33.root 4) :=
  Night6836Tree.sound w13 pick13 4 t565 _ (by decide +kernel)
theorem cov13_5 : PA.Covered 5 (OZ.Valid 5 w13.low w13.t w13.y w13.r w13.cap) (P33.root 5) :=
  Night6836Tree.sound w13 pick13 5 t566 _ (by decide +kernel)
theorem cov13_6 : PA.Covered 6 (OZ.Valid 6 w13.low w13.t w13.y w13.r w13.cap) (P33.root 6) :=
  Night6836Tree.sound w13 pick13 6 t567 _ (by decide +kernel)
theorem cov13_7 : PA.Covered 7 (OZ.Valid 7 w13.low w13.t w13.y w13.r w13.cap) (P33.root 7) :=
  Night6836Tree.sound w13 pick13 7 t568 _ (by decide +kernel)
theorem window13 : P33.WindowCount w13 := by
  apply P33.window_count w13 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov13_1
  · exact cov13_2
  · exact cov13_3
  · exact cov13_4
  · exact cov13_5
  · exact cov13_6
  · exact cov13_7
def w14 : P33.Window := ⟨5,49,7145,5646,237692176335110675,20177,50000,5000000,81920000000⟩
def h14_0 : Height w14 := ⟨20177,50000,by decide +kernel⟩
def pick14 (cl : ℕ) : Height w14 := h14_0
private theorem k14_1_0 : check w14 pick14 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k14_1_1 : check w14 pick14 1 t1266 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k14_1_2 : check w14 pick14 1 t1267 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w14 pick14 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t950 t1266 k14_1_0 k14_1_1
private theorem k14_1_3 : check w14 pick14 1 t1290 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k14_1_4 : check w14 pick14 1 t1320 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k14_1_5 : check w14 pick14 1 t1321 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w14 pick14 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t1290 t1320 k14_1_3 k14_1_4
private theorem k14_1_6 : check w14 pick14 1 t1322 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w14 pick14 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1267 t1321 k14_1_2 k14_1_5
private theorem k14_1_7 : check w14 pick14 1 t1327 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k14_1_8 : check w14 pick14 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k14_1_9 : check w14 pick14 1 t1328 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w14 pick14 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1327 t1066 k14_1_7 k14_1_8
private theorem k14_1_10 : check w14 pick14 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k14_1_11 : check w14 pick14 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k14_1_12 : check w14 pick14 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w14 pick14 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k14_1_10 k14_1_11
private theorem k14_1_13 : check w14 pick14 1 t1329 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w14 pick14 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1328 t1079 k14_1_9 k14_1_12
private theorem k14_1_14 : check w14 pick14 1 t1330 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w14 pick14 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1322 t1329 k14_1_6 k14_1_13
theorem cov14_1 : PA.Covered 1 (OZ.Valid 1 w14.low w14.t w14.y w14.r w14.cap) (P33.root 1) :=
  Night6836Tree.sound w14 pick14 1 t1330 _ k14_1_14
private theorem k14_2_0 : check w14 pick14 2 t1337 ⟨2,7,4,16,2,52,2,220⟩ = true := by decide +kernel
private theorem k14_2_1 : check w14 pick14 2 t1338 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k14_2_2 : check w14 pick14 2 t1339 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w14 pick14 2 ⟨2,7,4,16,0,52,0,450⟩ 3 220 t1337 t1338 k14_2_0 k14_2_1
theorem cov14_2 : PA.Covered 2 (OZ.Valid 2 w14.low w14.t w14.y w14.r w14.cap) (P33.root 2) :=
  Night6836Tree.sound w14 pick14 2 t1339 _ k14_2_2
theorem cov14_3 : PA.Covered 3 (OZ.Valid 3 w14.low w14.t w14.y w14.r w14.cap) (P33.root 3) :=
  Night6836Tree.sound w14 pick14 3 t564 _ (by decide +kernel)
theorem cov14_4 : PA.Covered 4 (OZ.Valid 4 w14.low w14.t w14.y w14.r w14.cap) (P33.root 4) :=
  Night6836Tree.sound w14 pick14 4 t565 _ (by decide +kernel)
theorem cov14_5 : PA.Covered 5 (OZ.Valid 5 w14.low w14.t w14.y w14.r w14.cap) (P33.root 5) :=
  Night6836Tree.sound w14 pick14 5 t566 _ (by decide +kernel)
theorem cov14_6 : PA.Covered 6 (OZ.Valid 6 w14.low w14.t w14.y w14.r w14.cap) (P33.root 6) :=
  Night6836Tree.sound w14 pick14 6 t567 _ (by decide +kernel)
theorem cov14_7 : PA.Covered 7 (OZ.Valid 7 w14.low w14.t w14.y w14.r w14.cap) (P33.root 7) :=
  Night6836Tree.sound w14 pick14 7 t568 _ (by decide +kernel)
theorem window14 : P33.WindowCount w14 := by
  apply P33.window_count w14 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov14_1
  · exact cov14_2
  · exact cov14_3
  · exact cov14_4
  · exact cov14_5
  · exact cov14_6
  · exact cov14_7
def w15 : P33.Window := ⟨5,51,7504,7452,237232950058738067,9882,50000,5000000,81920000000⟩
def h15_0 : Height w15 := ⟨9882,50000,by decide +kernel⟩
def pick15 (cl : ℕ) : Height w15 := h15_0
private theorem k15_1_0 : check w15 pick15 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k15_1_1 : check w15 pick15 1 t1266 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k15_1_2 : check w15 pick15 1 t1267 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w15 pick15 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t950 t1266 k15_1_0 k15_1_1
private theorem k15_1_3 : check w15 pick15 1 t1290 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k15_1_4 : check w15 pick15 1 t1320 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k15_1_5 : check w15 pick15 1 t1321 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w15 pick15 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t1290 t1320 k15_1_3 k15_1_4
private theorem k15_1_6 : check w15 pick15 1 t1322 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w15 pick15 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1267 t1321 k15_1_2 k15_1_5
private theorem k15_1_7 : check w15 pick15 1 t1327 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k15_1_8 : check w15 pick15 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k15_1_9 : check w15 pick15 1 t1328 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w15 pick15 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1327 t1066 k15_1_7 k15_1_8
private theorem k15_1_10 : check w15 pick15 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k15_1_11 : check w15 pick15 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k15_1_12 : check w15 pick15 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w15 pick15 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k15_1_10 k15_1_11
private theorem k15_1_13 : check w15 pick15 1 t1329 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w15 pick15 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1328 t1079 k15_1_9 k15_1_12
private theorem k15_1_14 : check w15 pick15 1 t1330 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w15 pick15 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1322 t1329 k15_1_6 k15_1_13
theorem cov15_1 : PA.Covered 1 (OZ.Valid 1 w15.low w15.t w15.y w15.r w15.cap) (P33.root 1) :=
  Night6836Tree.sound w15 pick15 1 t1330 _ k15_1_14
private theorem k15_2_0 : check w15 pick15 2 t1340 ⟨2,7,4,16,2,52,2,220⟩ = true := by decide +kernel
private theorem k15_2_1 : check w15 pick15 2 t1350 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k15_2_2 : check w15 pick15 2 t1351 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w15 pick15 2 ⟨2,7,4,16,0,52,0,450⟩ 3 220 t1340 t1350 k15_2_0 k15_2_1
theorem cov15_2 : PA.Covered 2 (OZ.Valid 2 w15.low w15.t w15.y w15.r w15.cap) (P33.root 2) :=
  Night6836Tree.sound w15 pick15 2 t1351 _ k15_2_2
theorem cov15_3 : PA.Covered 3 (OZ.Valid 3 w15.low w15.t w15.y w15.r w15.cap) (P33.root 3) :=
  Night6836Tree.sound w15 pick15 3 t564 _ (by decide +kernel)
theorem cov15_4 : PA.Covered 4 (OZ.Valid 4 w15.low w15.t w15.y w15.r w15.cap) (P33.root 4) :=
  Night6836Tree.sound w15 pick15 4 t565 _ (by decide +kernel)
theorem cov15_5 : PA.Covered 5 (OZ.Valid 5 w15.low w15.t w15.y w15.r w15.cap) (P33.root 5) :=
  Night6836Tree.sound w15 pick15 5 t566 _ (by decide +kernel)
theorem cov15_6 : PA.Covered 6 (OZ.Valid 6 w15.low w15.t w15.y w15.r w15.cap) (P33.root 6) :=
  Night6836Tree.sound w15 pick15 6 t567 _ (by decide +kernel)
theorem cov15_7 : PA.Covered 7 (OZ.Valid 7 w15.low w15.t w15.y w15.r w15.cap) (P33.root 7) :=
  Night6836Tree.sound w15 pick15 7 t568 _ (by decide +kernel)
theorem window15 : P33.WindowCount w15 := by
  apply P33.window_count w15 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov15_1
  · exact cov15_2
  · exact cov15_3
  · exact cov15_4
  · exact cov15_5
  · exact cov15_6
  · exact cov15_7
def w16 : P33.Window := ⟨5,52,7451,7304,237340708596852533,11375,50000,5000000,81920000000⟩
def h16_0 : Height w16 := ⟨11375,50000,by decide +kernel⟩
def pick16 (cl : ℕ) : Height w16 := h16_0
private theorem k16_1_0 : check w16 pick16 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k16_1_1 : check w16 pick16 1 t1266 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k16_1_2 : check w16 pick16 1 t1267 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w16 pick16 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t950 t1266 k16_1_0 k16_1_1
private theorem k16_1_3 : check w16 pick16 1 t1366 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k16_1_4 : check w16 pick16 1 t1372 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k16_1_5 : check w16 pick16 1 t1373 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w16 pick16 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t1366 t1372 k16_1_3 k16_1_4
private theorem k16_1_6 : check w16 pick16 1 t1374 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w16 pick16 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1267 t1373 k16_1_2 k16_1_5
private theorem k16_1_7 : check w16 pick16 1 t1327 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k16_1_8 : check w16 pick16 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k16_1_9 : check w16 pick16 1 t1328 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w16 pick16 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1327 t1066 k16_1_7 k16_1_8
private theorem k16_1_10 : check w16 pick16 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k16_1_11 : check w16 pick16 1 t1387 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k16_1_12 : check w16 pick16 1 t1388 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w16 pick16 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t1387 k16_1_10 k16_1_11
private theorem k16_1_13 : check w16 pick16 1 t1389 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w16 pick16 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1328 t1388 k16_1_9 k16_1_12
private theorem k16_1_14 : check w16 pick16 1 t1390 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w16 pick16 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1374 t1389 k16_1_6 k16_1_13
theorem cov16_1 : PA.Covered 1 (OZ.Valid 1 w16.low w16.t w16.y w16.r w16.cap) (P33.root 1) :=
  Night6836Tree.sound w16 pick16 1 t1390 _ k16_1_14
private theorem k16_2_0 : check w16 pick16 2 t1400 ⟨2,7,4,16,2,52,2,220⟩ = true := by decide +kernel
private theorem k16_2_1 : check w16 pick16 2 t1439 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k16_2_2 : check w16 pick16 2 t1440 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w16 pick16 2 ⟨2,7,4,16,0,52,0,450⟩ 3 220 t1400 t1439 k16_2_0 k16_2_1
theorem cov16_2 : PA.Covered 2 (OZ.Valid 2 w16.low w16.t w16.y w16.r w16.cap) (P33.root 2) :=
  Night6836Tree.sound w16 pick16 2 t1440 _ k16_2_2
theorem cov16_3 : PA.Covered 3 (OZ.Valid 3 w16.low w16.t w16.y w16.r w16.cap) (P33.root 3) :=
  Night6836Tree.sound w16 pick16 3 t564 _ (by decide +kernel)
theorem cov16_4 : PA.Covered 4 (OZ.Valid 4 w16.low w16.t w16.y w16.r w16.cap) (P33.root 4) :=
  Night6836Tree.sound w16 pick16 4 t565 _ (by decide +kernel)
theorem cov16_5 : PA.Covered 5 (OZ.Valid 5 w16.low w16.t w16.y w16.r w16.cap) (P33.root 5) :=
  Night6836Tree.sound w16 pick16 5 t566 _ (by decide +kernel)
theorem cov16_6 : PA.Covered 6 (OZ.Valid 6 w16.low w16.t w16.y w16.r w16.cap) (P33.root 6) :=
  Night6836Tree.sound w16 pick16 6 t567 _ (by decide +kernel)
theorem cov16_7 : PA.Covered 7 (OZ.Valid 7 w16.low w16.t w16.y w16.r w16.cap) (P33.root 7) :=
  Night6836Tree.sound w16 pick16 7 t568 _ (by decide +kernel)
theorem window16 : P33.WindowCount w16 := by
  apply P33.window_count w16 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov16_1
  · exact cov16_2
  · exact cov16_3
  · exact cov16_4
  · exact cov16_5
  · exact cov16_6
  · exact cov16_7
def w17 : P33.Window := ⟨5,53,7398,7345,237574821700014704,11888,50000,5000000,81920000000⟩
def h17_0 : Height w17 := ⟨11888,50000,by decide +kernel⟩
def pick17 (cl : ℕ) : Height w17 := h17_0
private theorem k17_1_0 : check w17 pick17 1 t1447 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k17_1_1 : check w17 pick17 1 t1266 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k17_1_2 : check w17 pick17 1 t1448 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w17 pick17 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t1447 t1266 k17_1_0 k17_1_1
private theorem k17_1_3 : check w17 pick17 1 t1366 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k17_1_4 : check w17 pick17 1 t1372 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k17_1_5 : check w17 pick17 1 t1373 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w17 pick17 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t1366 t1372 k17_1_3 k17_1_4
private theorem k17_1_6 : check w17 pick17 1 t1449 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w17 pick17 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1448 t1373 k17_1_2 k17_1_5
private theorem k17_1_7 : check w17 pick17 1 t1327 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k17_1_8 : check w17 pick17 1 t1473 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k17_1_9 : check w17 pick17 1 t1474 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w17 pick17 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1327 t1473 k17_1_7 k17_1_8
private theorem k17_1_10 : check w17 pick17 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k17_1_11 : check w17 pick17 1 t1507 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k17_1_12 : check w17 pick17 1 t1508 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w17 pick17 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t1507 k17_1_10 k17_1_11
private theorem k17_1_13 : check w17 pick17 1 t1509 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w17 pick17 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1474 t1508 k17_1_9 k17_1_12
private theorem k17_1_14 : check w17 pick17 1 t1510 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w17 pick17 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1449 t1509 k17_1_6 k17_1_13
theorem cov17_1 : PA.Covered 1 (OZ.Valid 1 w17.low w17.t w17.y w17.r w17.cap) (P33.root 1) :=
  Night6836Tree.sound w17 pick17 1 t1510 _ k17_1_14
private theorem k17_2_0 : check w17 pick17 2 t1562 ⟨2,7,4,16,2,52,2,220⟩ = true := by decide +kernel
private theorem k17_2_1 : check w17 pick17 2 t1439 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k17_2_2 : check w17 pick17 2 t1563 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w17 pick17 2 ⟨2,7,4,16,0,52,0,450⟩ 3 220 t1562 t1439 k17_2_0 k17_2_1
theorem cov17_2 : PA.Covered 2 (OZ.Valid 2 w17.low w17.t w17.y w17.r w17.cap) (P33.root 2) :=
  Night6836Tree.sound w17 pick17 2 t1563 _ k17_2_2
theorem cov17_3 : PA.Covered 3 (OZ.Valid 3 w17.low w17.t w17.y w17.r w17.cap) (P33.root 3) :=
  Night6836Tree.sound w17 pick17 3 t564 _ (by decide +kernel)
theorem cov17_4 : PA.Covered 4 (OZ.Valid 4 w17.low w17.t w17.y w17.r w17.cap) (P33.root 4) :=
  Night6836Tree.sound w17 pick17 4 t565 _ (by decide +kernel)
theorem cov17_5 : PA.Covered 5 (OZ.Valid 5 w17.low w17.t w17.y w17.r w17.cap) (P33.root 5) :=
  Night6836Tree.sound w17 pick17 5 t566 _ (by decide +kernel)
theorem cov17_6 : PA.Covered 6 (OZ.Valid 6 w17.low w17.t w17.y w17.r w17.cap) (P33.root 6) :=
  Night6836Tree.sound w17 pick17 6 t567 _ (by decide +kernel)
theorem cov17_7 : PA.Covered 7 (OZ.Valid 7 w17.low w17.t w17.y w17.r w17.cap) (P33.root 7) :=
  Night6836Tree.sound w17 pick17 7 t568 _ (by decide +kernel)
theorem window17 : P33.WindowCount w17 := by
  apply P33.window_count w17 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov17_1
  · exact cov17_2
  · exact cov17_3
  · exact cov17_4
  · exact cov17_5
  · exact cov17_6
  · exact cov17_7
def w18 : P33.Window := ⟨5,54,7344,7232,237591893795833626,13250,50000,5000000,81920000000⟩
def h18_0 : Height w18 := ⟨13250,50000,by decide +kernel⟩
def pick18 (cl : ℕ) : Height w18 := h18_0
private theorem k18_1_0 : check w18 pick18 1 t1578 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k18_1_1 : check w18 pick18 1 t1266 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k18_1_2 : check w18 pick18 1 t1579 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w18 pick18 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t1578 t1266 k18_1_0 k18_1_1
private theorem k18_1_3 : check w18 pick18 1 t1597 ⟨1,7,2,16,1,52,77,110⟩ = true := by decide +kernel
private theorem k18_1_4 : check w18 pick18 1 t1616 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k18_1_5 : check w18 pick18 1 t1617 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w18 pick18 1 ⟨1,7,2,16,1,52,77,138⟩ 3 110 t1597 t1616 k18_1_3 k18_1_4
private theorem k18_1_6 : check w18 pick18 1 t1618 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w18 pick18 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t1579 t1617 k18_1_2 k18_1_5
private theorem k18_1_7 : check w18 pick18 1 t1652 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k18_1_8 : check w18 pick18 1 t1658 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k18_1_9 : check w18 pick18 1 t1659 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w18 pick18 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t1652 t1658 k18_1_7 k18_1_8
private theorem k18_1_10 : check w18 pick18 1 t1662 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k18_1_11 : check w18 pick18 1 t1675 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k18_1_12 : check w18 pick18 1 t1676 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w18 pick18 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t1662 t1675 k18_1_10 k18_1_11
private theorem k18_1_13 : check w18 pick18 1 t1677 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w18 pick18 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t1659 t1676 k18_1_9 k18_1_12
private theorem k18_1_14 : check w18 pick18 1 t1678 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w18 pick18 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t1618 t1677 k18_1_6 k18_1_13
theorem cov18_1 : PA.Covered 1 (OZ.Valid 1 w18.low w18.t w18.y w18.r w18.cap) (P33.root 1) :=
  Night6836Tree.sound w18 pick18 1 t1678 _ k18_1_14
private theorem k18_2_0 : check w18 pick18 2 t1708 ⟨2,7,4,16,2,52,2,220⟩ = true := by decide +kernel
private theorem k18_2_1 : check w18 pick18 2 t1716 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k18_2_2 : check w18 pick18 2 t1717 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w18 pick18 2 ⟨2,7,4,16,0,52,0,450⟩ 3 220 t1708 t1716 k18_2_0 k18_2_1
theorem cov18_2 : PA.Covered 2 (OZ.Valid 2 w18.low w18.t w18.y w18.r w18.cap) (P33.root 2) :=
  Night6836Tree.sound w18 pick18 2 t1717 _ k18_2_2
theorem cov18_3 : PA.Covered 3 (OZ.Valid 3 w18.low w18.t w18.y w18.r w18.cap) (P33.root 3) :=
  Night6836Tree.sound w18 pick18 3 t564 _ (by decide +kernel)
theorem cov18_4 : PA.Covered 4 (OZ.Valid 4 w18.low w18.t w18.y w18.r w18.cap) (P33.root 4) :=
  Night6836Tree.sound w18 pick18 4 t565 _ (by decide +kernel)
theorem cov18_5 : PA.Covered 5 (OZ.Valid 5 w18.low w18.t w18.y w18.r w18.cap) (P33.root 5) :=
  Night6836Tree.sound w18 pick18 5 t566 _ (by decide +kernel)
theorem cov18_6 : PA.Covered 6 (OZ.Valid 6 w18.low w18.t w18.y w18.r w18.cap) (P33.root 6) :=
  Night6836Tree.sound w18 pick18 6 t567 _ (by decide +kernel)
theorem cov18_7 : PA.Covered 7 (OZ.Valid 7 w18.low w18.t w18.y w18.r w18.cap) (P33.root 7) :=
  Night6836Tree.sound w18 pick18 7 t568 _ (by decide +kernel)
theorem window18 : P33.WindowCount w18 := by
  apply P33.window_count w18 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov18_1
  · exact cov18_2
  · exact cov18_3
  · exact cov18_4
  · exact cov18_5
  · exact cov18_6
  · exact cov18_7
def w19 : P33.Window := ⟨5,55,7288,7232,237646396859645452,13992,50000,5000000,81920000000⟩
def h19_0 : Height w19 := ⟨13992,50000,by decide +kernel⟩
def pick19 (cl : ℕ) : Height w19 := h19_0
private theorem k19_1_0 : check w19 pick19 1 t1578 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k19_1_1 : check w19 pick19 1 t1745 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k19_1_2 : check w19 pick19 1 t1746 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w19 pick19 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t1578 t1745 k19_1_0 k19_1_1
private theorem k19_1_3 : check w19 pick19 1 t1771 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k19_1_4 : check w19 pick19 1 t1779 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k19_1_5 : check w19 pick19 1 t1780 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w19 pick19 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t1771 t1779 k19_1_3 k19_1_4
private theorem k19_1_6 : check w19 pick19 1 t1781 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w19 pick19 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1746 t1780 k19_1_2 k19_1_5
private theorem k19_1_7 : check w19 pick19 1 t1803 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k19_1_8 : check w19 pick19 1 t1828 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k19_1_9 : check w19 pick19 1 t1829 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w19 pick19 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t1803 t1828 k19_1_7 k19_1_8
private theorem k19_1_10 : check w19 pick19 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k19_1_11 : check w19 pick19 1 t1675 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k19_1_12 : check w19 pick19 1 t1830 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w19 pick19 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t1675 k19_1_10 k19_1_11
private theorem k19_1_13 : check w19 pick19 1 t1831 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w19 pick19 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1829 t1830 k19_1_9 k19_1_12
private theorem k19_1_14 : check w19 pick19 1 t1832 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w19 pick19 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1781 t1831 k19_1_6 k19_1_13
theorem cov19_1 : PA.Covered 1 (OZ.Valid 1 w19.low w19.t w19.y w19.r w19.cap) (P33.root 1) :=
  Night6836Tree.sound w19 pick19 1 t1832 _ k19_1_14
private theorem k19_2_0 : check w19 pick19 2 t1847 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k19_2_1 : check w19 pick19 2 t1851 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k19_2_2 : check w19 pick19 2 t1852 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w19 pick19 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t1847 t1851 k19_2_0 k19_2_1
theorem cov19_2 : PA.Covered 2 (OZ.Valid 2 w19.low w19.t w19.y w19.r w19.cap) (P33.root 2) :=
  Night6836Tree.sound w19 pick19 2 t1852 _ k19_2_2
theorem cov19_3 : PA.Covered 3 (OZ.Valid 3 w19.low w19.t w19.y w19.r w19.cap) (P33.root 3) :=
  Night6836Tree.sound w19 pick19 3 t564 _ (by decide +kernel)
theorem cov19_4 : PA.Covered 4 (OZ.Valid 4 w19.low w19.t w19.y w19.r w19.cap) (P33.root 4) :=
  Night6836Tree.sound w19 pick19 4 t565 _ (by decide +kernel)
theorem cov19_5 : PA.Covered 5 (OZ.Valid 5 w19.low w19.t w19.y w19.r w19.cap) (P33.root 5) :=
  Night6836Tree.sound w19 pick19 5 t566 _ (by decide +kernel)
theorem cov19_6 : PA.Covered 6 (OZ.Valid 6 w19.low w19.t w19.y w19.r w19.cap) (P33.root 6) :=
  Night6836Tree.sound w19 pick19 6 t567 _ (by decide +kernel)
theorem cov19_7 : PA.Covered 7 (OZ.Valid 7 w19.low w19.t w19.y w19.r w19.cap) (P33.root 7) :=
  Night6836Tree.sound w19 pick19 7 t568 _ (by decide +kernel)
theorem window19 : P33.WindowCount w19 := by
  apply P33.window_count w19 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov19_1
  · exact cov19_2
  · exact cov19_3
  · exact cov19_4
  · exact cov19_5
  · exact cov19_6
  · exact cov19_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w20 : P33.Window := ⟨5,56,7231,7168,237555929151934492,15116,50000,5000000,81920000000⟩
def h20_0 : Height w20 := ⟨15116,50000,by decide +kernel⟩
def pick20 (cl : ℕ) : Height w20 := h20_0
private theorem k20_1_0 : check w20 pick20 1 t1867 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k20_1_1 : check w20 pick20 1 t1878 ⟨1,7,2,16,1,52,43,62⟩ = true := by decide +kernel
private theorem k20_1_2 : check w20 pick20 1 t1744 ⟨1,7,2,16,1,52,63,76⟩ = true := by decide +kernel
private theorem k20_1_3 : check w20 pick20 1 t1879 ⟨1,7,2,16,1,52,43,76⟩ = true := glue w20 pick20 1 ⟨1,7,2,16,1,52,43,76⟩ 3 62 t1878 t1744 k20_1_1 k20_1_2
private theorem k20_1_4 : check w20 pick20 1 t1880 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w20 pick20 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t1867 t1879 k20_1_0 k20_1_3
private theorem k20_1_5 : check w20 pick20 1 t1771 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k20_1_6 : check w20 pick20 1 t1892 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k20_1_7 : check w20 pick20 1 t1893 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w20 pick20 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t1771 t1892 k20_1_5 k20_1_6
private theorem k20_1_8 : check w20 pick20 1 t1894 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w20 pick20 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1880 t1893 k20_1_4 k20_1_7
private theorem k20_1_9 : check w20 pick20 1 t1926 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k20_1_10 : check w20 pick20 1 t1952 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k20_1_11 : check w20 pick20 1 t1953 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w20 pick20 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1926 t1952 k20_1_9 k20_1_10
private theorem k20_1_12 : check w20 pick20 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k20_1_13 : check w20 pick20 1 t1675 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k20_1_14 : check w20 pick20 1 t1830 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w20 pick20 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t1675 k20_1_12 k20_1_13
private theorem k20_1_15 : check w20 pick20 1 t1954 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w20 pick20 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1953 t1830 k20_1_11 k20_1_14
private theorem k20_1_16 : check w20 pick20 1 t1955 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w20 pick20 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t1894 t1954 k20_1_8 k20_1_15
theorem cov20_1 : PA.Covered 1 (OZ.Valid 1 w20.low w20.t w20.y w20.r w20.cap) (P33.root 1) :=
  Night6836Tree.sound w20 pick20 1 t1955 _ k20_1_16
private theorem k20_2_0 : check w20 pick20 2 t1847 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k20_2_1 : check w20 pick20 2 t1851 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k20_2_2 : check w20 pick20 2 t1852 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w20 pick20 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t1847 t1851 k20_2_0 k20_2_1
theorem cov20_2 : PA.Covered 2 (OZ.Valid 2 w20.low w20.t w20.y w20.r w20.cap) (P33.root 2) :=
  Night6836Tree.sound w20 pick20 2 t1852 _ k20_2_2
theorem cov20_3 : PA.Covered 3 (OZ.Valid 3 w20.low w20.t w20.y w20.r w20.cap) (P33.root 3) :=
  Night6836Tree.sound w20 pick20 3 t564 _ (by decide +kernel)
theorem cov20_4 : PA.Covered 4 (OZ.Valid 4 w20.low w20.t w20.y w20.r w20.cap) (P33.root 4) :=
  Night6836Tree.sound w20 pick20 4 t565 _ (by decide +kernel)
theorem cov20_5 : PA.Covered 5 (OZ.Valid 5 w20.low w20.t w20.y w20.r w20.cap) (P33.root 5) :=
  Night6836Tree.sound w20 pick20 5 t566 _ (by decide +kernel)
theorem cov20_6 : PA.Covered 6 (OZ.Valid 6 w20.low w20.t w20.y w20.r w20.cap) (P33.root 6) :=
  Night6836Tree.sound w20 pick20 6 t567 _ (by decide +kernel)
theorem cov20_7 : PA.Covered 7 (OZ.Valid 7 w20.low w20.t w20.y w20.r w20.cap) (P33.root 7) :=
  Night6836Tree.sound w20 pick20 7 t568 _ (by decide +kernel)
theorem window20 : P33.WindowCount w20 := by
  apply P33.window_count w20 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov20_1
  · exact cov20_2
  · exact cov20_3
  · exact cov20_4
  · exact cov20_5
  · exact cov20_6
  · exact cov20_7
def w21 : P33.Window := ⟨5,57,7167,6400,235864455820498459,21183,50000,5000000,81920000000⟩
def h21_0 : Height w21 := ⟨21183,50000,by decide +kernel⟩
def pick21 (cl : ℕ) : Height w21 := h21_0
private theorem k21_1_0 : check w21 pick21 1 t1959 ⟨1,7,2,16,1,52,1,35⟩ = true := by decide +kernel
private theorem k21_1_1 : check w21 pick21 1 t1971 ⟨1,7,2,16,1,52,36,55⟩ = true := by decide +kernel
private theorem k21_1_2 : check w21 pick21 1 t1972 ⟨1,7,2,16,1,52,1,55⟩ = true := glue w21 pick21 1 ⟨1,7,2,16,1,52,1,55⟩ 3 35 t1959 t1971 k21_1_0 k21_1_1
private theorem k21_1_3 : check w21 pick21 1 t2001 ⟨1,7,2,16,1,52,56,76⟩ = true := by decide +kernel
private theorem k21_1_4 : check w21 pick21 1 t2002 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w21 pick21 1 ⟨1,7,2,16,1,52,1,76⟩ 3 55 t1972 t2001 k21_1_2 k21_1_3
private theorem k21_1_5 : check w21 pick21 1 t2010 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k21_1_6 : check w21 pick21 1 t2048 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k21_1_7 : check w21 pick21 1 t2049 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w21 pick21 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t2010 t2048 k21_1_5 k21_1_6
private theorem k21_1_8 : check w21 pick21 1 t2050 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w21 pick21 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t2002 t2049 k21_1_4 k21_1_7
private theorem k21_1_9 : check w21 pick21 1 t1926 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k21_1_10 : check w21 pick21 1 t1952 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k21_1_11 : check w21 pick21 1 t1953 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w21 pick21 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1926 t1952 k21_1_9 k21_1_10
private theorem k21_1_12 : check w21 pick21 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k21_1_13 : check w21 pick21 1 t2078 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k21_1_14 : check w21 pick21 1 t2079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w21 pick21 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t2078 k21_1_12 k21_1_13
private theorem k21_1_15 : check w21 pick21 1 t2080 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w21 pick21 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1953 t2079 k21_1_11 k21_1_14
private theorem k21_1_16 : check w21 pick21 1 t2081 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w21 pick21 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t2050 t2080 k21_1_8 k21_1_15
theorem cov21_1 : PA.Covered 1 (OZ.Valid 1 w21.low w21.t w21.y w21.r w21.cap) (P33.root 1) :=
  Night6836Tree.sound w21 pick21 1 t2081 _ k21_1_16
private theorem k21_2_0 : check w21 pick21 2 t2096 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k21_2_1 : check w21 pick21 2 t2103 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k21_2_2 : check w21 pick21 2 t2104 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w21 pick21 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t2096 t2103 k21_2_0 k21_2_1
theorem cov21_2 : PA.Covered 2 (OZ.Valid 2 w21.low w21.t w21.y w21.r w21.cap) (P33.root 2) :=
  Night6836Tree.sound w21 pick21 2 t2104 _ k21_2_2
theorem cov21_3 : PA.Covered 3 (OZ.Valid 3 w21.low w21.t w21.y w21.r w21.cap) (P33.root 3) :=
  Night6836Tree.sound w21 pick21 3 t564 _ (by decide +kernel)
theorem cov21_4 : PA.Covered 4 (OZ.Valid 4 w21.low w21.t w21.y w21.r w21.cap) (P33.root 4) :=
  Night6836Tree.sound w21 pick21 4 t565 _ (by decide +kernel)
theorem cov21_5 : PA.Covered 5 (OZ.Valid 5 w21.low w21.t w21.y w21.r w21.cap) (P33.root 5) :=
  Night6836Tree.sound w21 pick21 5 t566 _ (by decide +kernel)
theorem cov21_6 : PA.Covered 6 (OZ.Valid 6 w21.low w21.t w21.y w21.r w21.cap) (P33.root 6) :=
  Night6836Tree.sound w21 pick21 6 t567 _ (by decide +kernel)
theorem cov21_7 : PA.Covered 7 (OZ.Valid 7 w21.low w21.t w21.y w21.r w21.cap) (P33.root 7) :=
  Night6836Tree.sound w21 pick21 7 t568 _ (by decide +kernel)
theorem window21 : P33.WindowCount w21 := by
  apply P33.window_count w21 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov21_1
  · exact cov21_2
  · exact cov21_3
  · exact cov21_4
  · exact cov21_5
  · exact cov21_6
  · exact cov21_7
def w22 : P33.Window := ⟨5,58,7098,7027,237543042552385511,17514,50000,5000000,81920000000⟩
def h22_0 : Height w22 := ⟨17514,50000,by decide +kernel⟩
def pick22 (cl : ℕ) : Height w22 := h22_0
private theorem k22_1_0 : check w22 pick22 1 t1867 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k22_1_1 : check w22 pick22 1 t1878 ⟨1,7,2,16,1,52,43,62⟩ = true := by decide +kernel
private theorem k22_1_2 : check w22 pick22 1 t1744 ⟨1,7,2,16,1,52,63,76⟩ = true := by decide +kernel
private theorem k22_1_3 : check w22 pick22 1 t1879 ⟨1,7,2,16,1,52,43,76⟩ = true := glue w22 pick22 1 ⟨1,7,2,16,1,52,43,76⟩ 3 62 t1878 t1744 k22_1_1 k22_1_2
private theorem k22_1_4 : check w22 pick22 1 t1880 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w22 pick22 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t1867 t1879 k22_1_0 k22_1_3
private theorem k22_1_5 : check w22 pick22 1 t2111 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k22_1_6 : check w22 pick22 1 t2112 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k22_1_7 : check w22 pick22 1 t2113 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w22 pick22 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t2111 t2112 k22_1_5 k22_1_6
private theorem k22_1_8 : check w22 pick22 1 t2114 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w22 pick22 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1880 t2113 k22_1_4 k22_1_7
private theorem k22_1_9 : check w22 pick22 1 t1926 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k22_1_10 : check w22 pick22 1 t1952 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k22_1_11 : check w22 pick22 1 t1953 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w22 pick22 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1926 t1952 k22_1_9 k22_1_10
private theorem k22_1_12 : check w22 pick22 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k22_1_13 : check w22 pick22 1 t1675 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k22_1_14 : check w22 pick22 1 t1830 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w22 pick22 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t1675 k22_1_12 k22_1_13
private theorem k22_1_15 : check w22 pick22 1 t1954 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w22 pick22 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1953 t1830 k22_1_11 k22_1_14
private theorem k22_1_16 : check w22 pick22 1 t2115 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w22 pick22 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t2114 t1954 k22_1_8 k22_1_15
theorem cov22_1 : PA.Covered 1 (OZ.Valid 1 w22.low w22.t w22.y w22.r w22.cap) (P33.root 1) :=
  Night6836Tree.sound w22 pick22 1 t2115 _ k22_1_16
private theorem k22_2_0 : check w22 pick22 2 t1847 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k22_2_1 : check w22 pick22 2 t2103 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k22_2_2 : check w22 pick22 2 t2116 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w22 pick22 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t1847 t2103 k22_2_0 k22_2_1
theorem cov22_2 : PA.Covered 2 (OZ.Valid 2 w22.low w22.t w22.y w22.r w22.cap) (P33.root 2) :=
  Night6836Tree.sound w22 pick22 2 t2116 _ k22_2_2
theorem cov22_3 : PA.Covered 3 (OZ.Valid 3 w22.low w22.t w22.y w22.r w22.cap) (P33.root 3) :=
  Night6836Tree.sound w22 pick22 3 t564 _ (by decide +kernel)
theorem cov22_4 : PA.Covered 4 (OZ.Valid 4 w22.low w22.t w22.y w22.r w22.cap) (P33.root 4) :=
  Night6836Tree.sound w22 pick22 4 t565 _ (by decide +kernel)
theorem cov22_5 : PA.Covered 5 (OZ.Valid 5 w22.low w22.t w22.y w22.r w22.cap) (P33.root 5) :=
  Night6836Tree.sound w22 pick22 5 t566 _ (by decide +kernel)
theorem cov22_6 : PA.Covered 6 (OZ.Valid 6 w22.low w22.t w22.y w22.r w22.cap) (P33.root 6) :=
  Night6836Tree.sound w22 pick22 6 t567 _ (by decide +kernel)
theorem cov22_7 : PA.Covered 7 (OZ.Valid 7 w22.low w22.t w22.y w22.r w22.cap) (P33.root 7) :=
  Night6836Tree.sound w22 pick22 7 t568 _ (by decide +kernel)
theorem window22 : P33.WindowCount w22 := by
  apply P33.window_count w22 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov22_1
  · exact cov22_2
  · exact cov22_3
  · exact cov22_4
  · exact cov22_5
  · exact cov22_6
  · exact cov22_7
def w23 : P33.Window := ⟨5,59,6164,4665,238022163067076613,42806,50000,5000000,81920000000⟩
def h23_0 : Height w23 := ⟨42806,50000,by decide +kernel⟩
def pick23 (cl : ℕ) : Height w23 := h23_0
private theorem k23_1_0 : check w23 pick23 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k23_1_1 : check w23 pick23 1 t1266 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k23_1_2 : check w23 pick23 1 t1267 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w23 pick23 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t950 t1266 k23_1_0 k23_1_1
private theorem k23_1_3 : check w23 pick23 1 t2124 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k23_1_4 : check w23 pick23 1 t2130 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k23_1_5 : check w23 pick23 1 t2131 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w23 pick23 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t2124 t2130 k23_1_3 k23_1_4
private theorem k23_1_6 : check w23 pick23 1 t2132 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w23 pick23 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1267 t2131 k23_1_2 k23_1_5
private theorem k23_1_7 : check w23 pick23 1 t1327 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k23_1_8 : check w23 pick23 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k23_1_9 : check w23 pick23 1 t1328 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w23 pick23 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1327 t1066 k23_1_7 k23_1_8
private theorem k23_1_10 : check w23 pick23 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k23_1_11 : check w23 pick23 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k23_1_12 : check w23 pick23 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w23 pick23 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k23_1_10 k23_1_11
private theorem k23_1_13 : check w23 pick23 1 t1329 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w23 pick23 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1328 t1079 k23_1_9 k23_1_12
private theorem k23_1_14 : check w23 pick23 1 t2133 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w23 pick23 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t2132 t1329 k23_1_6 k23_1_13
theorem cov23_1 : PA.Covered 1 (OZ.Valid 1 w23.low w23.t w23.y w23.r w23.cap) (P33.root 1) :=
  Night6836Tree.sound w23 pick23 1 t2133 _ k23_1_14
private theorem k23_2_0 : check w23 pick23 2 t1337 ⟨2,7,4,16,2,52,2,220⟩ = true := by decide +kernel
private theorem k23_2_1 : check w23 pick23 2 t1338 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k23_2_2 : check w23 pick23 2 t1339 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w23 pick23 2 ⟨2,7,4,16,0,52,0,450⟩ 3 220 t1337 t1338 k23_2_0 k23_2_1
theorem cov23_2 : PA.Covered 2 (OZ.Valid 2 w23.low w23.t w23.y w23.r w23.cap) (P33.root 2) :=
  Night6836Tree.sound w23 pick23 2 t1339 _ k23_2_2
theorem cov23_3 : PA.Covered 3 (OZ.Valid 3 w23.low w23.t w23.y w23.r w23.cap) (P33.root 3) :=
  Night6836Tree.sound w23 pick23 3 t564 _ (by decide +kernel)
theorem cov23_4 : PA.Covered 4 (OZ.Valid 4 w23.low w23.t w23.y w23.r w23.cap) (P33.root 4) :=
  Night6836Tree.sound w23 pick23 4 t565 _ (by decide +kernel)
theorem cov23_5 : PA.Covered 5 (OZ.Valid 5 w23.low w23.t w23.y w23.r w23.cap) (P33.root 5) :=
  Night6836Tree.sound w23 pick23 5 t566 _ (by decide +kernel)
theorem cov23_6 : PA.Covered 6 (OZ.Valid 6 w23.low w23.t w23.y w23.r w23.cap) (P33.root 6) :=
  Night6836Tree.sound w23 pick23 6 t567 _ (by decide +kernel)
theorem cov23_7 : PA.Covered 7 (OZ.Valid 7 w23.low w23.t w23.y w23.r w23.cap) (P33.root 7) :=
  Night6836Tree.sound w23 pick23 7 t2134 _ (by decide +kernel)
theorem window23 : P33.WindowCount w23 := by
  apply P33.window_count w23 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov23_1
  · exact cov23_2
  · exact cov23_3
  · exact cov23_4
  · exact cov23_5
  · exact cov23_6
  · exact cov23_7
def w24 : P33.Window := ⟨5,59,7026,6943,237701977302636447,18844,50000,5000000,81920000000⟩
def h24_0 : Height w24 := ⟨18844,50000,by decide +kernel⟩
def pick24 (cl : ℕ) : Height w24 := h24_0
private theorem k24_1_0 : check w24 pick24 1 t1867 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k24_1_1 : check w24 pick24 1 t1878 ⟨1,7,2,16,1,52,43,62⟩ = true := by decide +kernel
private theorem k24_1_2 : check w24 pick24 1 t1744 ⟨1,7,2,16,1,52,63,76⟩ = true := by decide +kernel
private theorem k24_1_3 : check w24 pick24 1 t1879 ⟨1,7,2,16,1,52,43,76⟩ = true := glue w24 pick24 1 ⟨1,7,2,16,1,52,43,76⟩ 3 62 t1878 t1744 k24_1_1 k24_1_2
private theorem k24_1_4 : check w24 pick24 1 t1880 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w24 pick24 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t1867 t1879 k24_1_0 k24_1_3
private theorem k24_1_5 : check w24 pick24 1 t2010 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k24_1_6 : check w24 pick24 1 t2136 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k24_1_7 : check w24 pick24 1 t2137 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w24 pick24 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t2010 t2136 k24_1_5 k24_1_6
private theorem k24_1_8 : check w24 pick24 1 t2138 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w24 pick24 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1880 t2137 k24_1_4 k24_1_7
private theorem k24_1_9 : check w24 pick24 1 t1926 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k24_1_10 : check w24 pick24 1 t1952 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k24_1_11 : check w24 pick24 1 t1953 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w24 pick24 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1926 t1952 k24_1_9 k24_1_10
private theorem k24_1_12 : check w24 pick24 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k24_1_13 : check w24 pick24 1 t1675 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k24_1_14 : check w24 pick24 1 t1830 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w24 pick24 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t1675 k24_1_12 k24_1_13
private theorem k24_1_15 : check w24 pick24 1 t1954 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w24 pick24 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1953 t1830 k24_1_11 k24_1_14
private theorem k24_1_16 : check w24 pick24 1 t2139 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w24 pick24 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t2138 t1954 k24_1_8 k24_1_15
theorem cov24_1 : PA.Covered 1 (OZ.Valid 1 w24.low w24.t w24.y w24.r w24.cap) (P33.root 1) :=
  Night6836Tree.sound w24 pick24 1 t2139 _ k24_1_16
private theorem k24_2_0 : check w24 pick24 2 t1847 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k24_2_1 : check w24 pick24 2 t2103 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k24_2_2 : check w24 pick24 2 t2116 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w24 pick24 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t1847 t2103 k24_2_0 k24_2_1
theorem cov24_2 : PA.Covered 2 (OZ.Valid 2 w24.low w24.t w24.y w24.r w24.cap) (P33.root 2) :=
  Night6836Tree.sound w24 pick24 2 t2116 _ k24_2_2
theorem cov24_3 : PA.Covered 3 (OZ.Valid 3 w24.low w24.t w24.y w24.r w24.cap) (P33.root 3) :=
  Night6836Tree.sound w24 pick24 3 t564 _ (by decide +kernel)
theorem cov24_4 : PA.Covered 4 (OZ.Valid 4 w24.low w24.t w24.y w24.r w24.cap) (P33.root 4) :=
  Night6836Tree.sound w24 pick24 4 t565 _ (by decide +kernel)
theorem cov24_5 : PA.Covered 5 (OZ.Valid 5 w24.low w24.t w24.y w24.r w24.cap) (P33.root 5) :=
  Night6836Tree.sound w24 pick24 5 t566 _ (by decide +kernel)
theorem cov24_6 : PA.Covered 6 (OZ.Valid 6 w24.low w24.t w24.y w24.r w24.cap) (P33.root 6) :=
  Night6836Tree.sound w24 pick24 6 t567 _ (by decide +kernel)
theorem cov24_7 : PA.Covered 7 (OZ.Valid 7 w24.low w24.t w24.y w24.r w24.cap) (P33.root 7) :=
  Night6836Tree.sound w24 pick24 7 t568 _ (by decide +kernel)
theorem window24 : P33.WindowCount w24 := by
  apply P33.window_count w24 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov24_1
  · exact cov24_2
  · exact cov24_3
  · exact cov24_4
  · exact cov24_5
  · exact cov24_6
  · exact cov24_7
def w25 : P33.Window := ⟨5,60,6942,6760,237629392997174698,20924,50000,5000000,81920000000⟩
def h25_0 : Height w25 := ⟨20924,50000,by decide +kernel⟩
def pick25 (cl : ℕ) : Height w25 := h25_0
private theorem k25_1_0 : check w25 pick25 1 t1867 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k25_1_1 : check w25 pick25 1 t1878 ⟨1,7,2,16,1,52,43,62⟩ = true := by decide +kernel
private theorem k25_1_2 : check w25 pick25 1 t1744 ⟨1,7,2,16,1,52,63,76⟩ = true := by decide +kernel
private theorem k25_1_3 : check w25 pick25 1 t1879 ⟨1,7,2,16,1,52,43,76⟩ = true := glue w25 pick25 1 ⟨1,7,2,16,1,52,43,76⟩ 3 62 t1878 t1744 k25_1_1 k25_1_2
private theorem k25_1_4 : check w25 pick25 1 t1880 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w25 pick25 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t1867 t1879 k25_1_0 k25_1_3
private theorem k25_1_5 : check w25 pick25 1 t2010 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k25_1_6 : check w25 pick25 1 t2136 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k25_1_7 : check w25 pick25 1 t2137 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w25 pick25 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t2010 t2136 k25_1_5 k25_1_6
private theorem k25_1_8 : check w25 pick25 1 t2138 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w25 pick25 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1880 t2137 k25_1_4 k25_1_7
private theorem k25_1_9 : check w25 pick25 1 t1926 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k25_1_10 : check w25 pick25 1 t1952 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k25_1_11 : check w25 pick25 1 t1953 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w25 pick25 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1926 t1952 k25_1_9 k25_1_10
private theorem k25_1_12 : check w25 pick25 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k25_1_13 : check w25 pick25 1 t2149 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k25_1_14 : check w25 pick25 1 t2150 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w25 pick25 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t2149 k25_1_12 k25_1_13
private theorem k25_1_15 : check w25 pick25 1 t2151 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w25 pick25 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1953 t2150 k25_1_11 k25_1_14
private theorem k25_1_16 : check w25 pick25 1 t2152 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w25 pick25 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t2138 t2151 k25_1_8 k25_1_15
theorem cov25_1 : PA.Covered 1 (OZ.Valid 1 w25.low w25.t w25.y w25.r w25.cap) (P33.root 1) :=
  Night6836Tree.sound w25 pick25 1 t2152 _ k25_1_16
private theorem k25_2_0 : check w25 pick25 2 t1847 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k25_2_1 : check w25 pick25 2 t2103 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k25_2_2 : check w25 pick25 2 t2116 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w25 pick25 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t1847 t2103 k25_2_0 k25_2_1
theorem cov25_2 : PA.Covered 2 (OZ.Valid 2 w25.low w25.t w25.y w25.r w25.cap) (P33.root 2) :=
  Night6836Tree.sound w25 pick25 2 t2116 _ k25_2_2
theorem cov25_3 : PA.Covered 3 (OZ.Valid 3 w25.low w25.t w25.y w25.r w25.cap) (P33.root 3) :=
  Night6836Tree.sound w25 pick25 3 t564 _ (by decide +kernel)
theorem cov25_4 : PA.Covered 4 (OZ.Valid 4 w25.low w25.t w25.y w25.r w25.cap) (P33.root 4) :=
  Night6836Tree.sound w25 pick25 4 t565 _ (by decide +kernel)
theorem cov25_5 : PA.Covered 5 (OZ.Valid 5 w25.low w25.t w25.y w25.r w25.cap) (P33.root 5) :=
  Night6836Tree.sound w25 pick25 5 t566 _ (by decide +kernel)
theorem cov25_6 : PA.Covered 6 (OZ.Valid 6 w25.low w25.t w25.y w25.r w25.cap) (P33.root 6) :=
  Night6836Tree.sound w25 pick25 6 t567 _ (by decide +kernel)
theorem cov25_7 : PA.Covered 7 (OZ.Valid 7 w25.low w25.t w25.y w25.r w25.cap) (P33.root 7) :=
  Night6836Tree.sound w25 pick25 7 t568 _ (by decide +kernel)
theorem window25 : P33.WindowCount w25 := by
  apply P33.window_count w25 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov25_1
  · exact cov25_2
  · exact cov25_3
  · exact cov25_4
  · exact cov25_5
  · exact cov25_6
  · exact cov25_7
def w26 : P33.Window := ⟨5,61,6275,5890,238338192904667757,29260,50000,5000000,81920000000⟩
def h26_0 : Height w26 := ⟨29260,50000,by decide +kernel⟩
def pick26 (cl : ℕ) : Height w26 := h26_0
private theorem k26_1_0 : check w26 pick26 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k26_1_1 : check w26 pick26 1 t976 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k26_1_2 : check w26 pick26 1 t977 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w26 pick26 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t950 t976 k26_1_0 k26_1_1
private theorem k26_1_3 : check w26 pick26 1 t2155 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k26_1_4 : check w26 pick26 1 t2159 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k26_1_5 : check w26 pick26 1 t2160 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w26 pick26 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t2155 t2159 k26_1_3 k26_1_4
private theorem k26_1_6 : check w26 pick26 1 t2161 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w26 pick26 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t977 t2160 k26_1_2 k26_1_5
private theorem k26_1_7 : check w26 pick26 1 t1251 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k26_1_8 : check w26 pick26 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k26_1_9 : check w26 pick26 1 t1252 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w26 pick26 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1251 t1066 k26_1_7 k26_1_8
private theorem k26_1_10 : check w26 pick26 1 t1078 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k26_1_11 : check w26 pick26 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k26_1_12 : check w26 pick26 1 t1079 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w26 pick26 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1078 t786 k26_1_10 k26_1_11
private theorem k26_1_13 : check w26 pick26 1 t1253 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w26 pick26 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1252 t1079 k26_1_9 k26_1_12
private theorem k26_1_14 : check w26 pick26 1 t2162 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w26 pick26 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t2161 t1253 k26_1_6 k26_1_13
theorem cov26_1 : PA.Covered 1 (OZ.Valid 1 w26.low w26.t w26.y w26.r w26.cap) (P33.root 1) :=
  Night6836Tree.sound w26 pick26 1 t2162 _ k26_1_14
private theorem k26_2_0 : check w26 pick26 2 t2170 ⟨2,7,4,16,2,52,2,220⟩ = true := by decide +kernel
private theorem k26_2_1 : check w26 pick26 2 t2178 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k26_2_2 : check w26 pick26 2 t2179 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w26 pick26 2 ⟨2,7,4,16,0,52,0,450⟩ 3 220 t2170 t2178 k26_2_0 k26_2_1
theorem cov26_2 : PA.Covered 2 (OZ.Valid 2 w26.low w26.t w26.y w26.r w26.cap) (P33.root 2) :=
  Night6836Tree.sound w26 pick26 2 t2179 _ k26_2_2
theorem cov26_3 : PA.Covered 3 (OZ.Valid 3 w26.low w26.t w26.y w26.r w26.cap) (P33.root 3) :=
  Night6836Tree.sound w26 pick26 3 t564 _ (by decide +kernel)
theorem cov26_4 : PA.Covered 4 (OZ.Valid 4 w26.low w26.t w26.y w26.r w26.cap) (P33.root 4) :=
  Night6836Tree.sound w26 pick26 4 t565 _ (by decide +kernel)
theorem cov26_5 : PA.Covered 5 (OZ.Valid 5 w26.low w26.t w26.y w26.r w26.cap) (P33.root 5) :=
  Night6836Tree.sound w26 pick26 5 t566 _ (by decide +kernel)
theorem cov26_6 : PA.Covered 6 (OZ.Valid 6 w26.low w26.t w26.y w26.r w26.cap) (P33.root 6) :=
  Night6836Tree.sound w26 pick26 6 t567 _ (by decide +kernel)
theorem cov26_7 : PA.Covered 7 (OZ.Valid 7 w26.low w26.t w26.y w26.r w26.cap) (P33.root 7) :=
  Night6836Tree.sound w26 pick26 7 t2134 _ (by decide +kernel)
theorem window26 : P33.WindowCount w26 := by
  apply P33.window_count w26 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov26_1
  · exact cov26_2
  · exact cov26_3
  · exact cov26_4
  · exact cov26_5
  · exact cov26_6
  · exact cov26_7
def w27 : P33.Window := ⟨5,61,6759,6384,237680484989438732,24707,50000,5000000,81920000000⟩
def h27_0 : Height w27 := ⟨24707,50000,by decide +kernel⟩
def pick27 (cl : ℕ) : Height w27 := h27_0
private theorem k27_1_0 : check w27 pick27 1 t1867 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k27_1_1 : check w27 pick27 1 t2183 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k27_1_2 : check w27 pick27 1 t2184 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w27 pick27 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t1867 t2183 k27_1_0 k27_1_1
private theorem k27_1_3 : check w27 pick27 1 t2191 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k27_1_4 : check w27 pick27 1 t2198 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k27_1_5 : check w27 pick27 1 t2199 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w27 pick27 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t2191 t2198 k27_1_3 k27_1_4
private theorem k27_1_6 : check w27 pick27 1 t2200 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w27 pick27 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t2184 t2199 k27_1_2 k27_1_5
private theorem k27_1_7 : check w27 pick27 1 t2211 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k27_1_8 : check w27 pick27 1 t2218 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k27_1_9 : check w27 pick27 1 t2219 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w27 pick27 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t2211 t2218 k27_1_7 k27_1_8
private theorem k27_1_10 : check w27 pick27 1 t1498 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k27_1_11 : check w27 pick27 1 t1675 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k27_1_12 : check w27 pick27 1 t1830 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w27 pick27 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t1498 t1675 k27_1_10 k27_1_11
private theorem k27_1_13 : check w27 pick27 1 t2220 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w27 pick27 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t2219 t1830 k27_1_9 k27_1_12
private theorem k27_1_14 : check w27 pick27 1 t2221 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w27 pick27 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t2200 t2220 k27_1_6 k27_1_13
theorem cov27_1 : PA.Covered 1 (OZ.Valid 1 w27.low w27.t w27.y w27.r w27.cap) (P33.root 1) :=
  Night6836Tree.sound w27 pick27 1 t2221 _ k27_1_14
private theorem k27_2_0 : check w27 pick27 2 t1847 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k27_2_1 : check w27 pick27 2 t2103 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k27_2_2 : check w27 pick27 2 t2116 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w27 pick27 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t1847 t2103 k27_2_0 k27_2_1
theorem cov27_2 : PA.Covered 2 (OZ.Valid 2 w27.low w27.t w27.y w27.r w27.cap) (P33.root 2) :=
  Night6836Tree.sound w27 pick27 2 t2116 _ k27_2_2
theorem cov27_3 : PA.Covered 3 (OZ.Valid 3 w27.low w27.t w27.y w27.r w27.cap) (P33.root 3) :=
  Night6836Tree.sound w27 pick27 3 t564 _ (by decide +kernel)
theorem cov27_4 : PA.Covered 4 (OZ.Valid 4 w27.low w27.t w27.y w27.r w27.cap) (P33.root 4) :=
  Night6836Tree.sound w27 pick27 4 t565 _ (by decide +kernel)
theorem cov27_5 : PA.Covered 5 (OZ.Valid 5 w27.low w27.t w27.y w27.r w27.cap) (P33.root 5) :=
  Night6836Tree.sound w27 pick27 5 t566 _ (by decide +kernel)
theorem cov27_6 : PA.Covered 6 (OZ.Valid 6 w27.low w27.t w27.y w27.r w27.cap) (P33.root 6) :=
  Night6836Tree.sound w27 pick27 6 t567 _ (by decide +kernel)
theorem cov27_7 : PA.Covered 7 (OZ.Valid 7 w27.low w27.t w27.y w27.r w27.cap) (P33.root 7) :=
  Night6836Tree.sound w27 pick27 7 t568 _ (by decide +kernel)
theorem window27 : P33.WindowCount w27 := by
  apply P33.window_count w27 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov27_1
  · exact cov27_2
  · exact cov27_3
  · exact cov27_4
  · exact cov27_5
  · exact cov27_6
  · exact cov27_7
def w28 : P33.Window := ⟨5,62,5889,5488,238272862747074128,34632,50000,5000000,81920000000⟩
def h28_0 : Height w28 := ⟨34632,50000,by decide +kernel⟩
def pick28 (cl : ℕ) : Height w28 := h28_0
private theorem k28_1_0 : check w28 pick28 1 t801 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k28_1_1 : check w28 pick28 1 t2223 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k28_1_2 : check w28 pick28 1 t2224 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w28 pick28 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t801 t2223 k28_1_0 k28_1_1
private theorem k28_1_3 : check w28 pick28 1 t2236 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k28_1_4 : check w28 pick28 1 t2254 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k28_1_5 : check w28 pick28 1 t2255 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w28 pick28 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t2236 t2254 k28_1_3 k28_1_4
private theorem k28_1_6 : check w28 pick28 1 t2256 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w28 pick28 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t2224 t2255 k28_1_2 k28_1_5
private theorem k28_1_7 : check w28 pick28 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k28_1_8 : check w28 pick28 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k28_1_9 : check w28 pick28 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w28 pick28 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k28_1_7 k28_1_8
private theorem k28_1_10 : check w28 pick28 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k28_1_11 : check w28 pick28 1 t786 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k28_1_12 : check w28 pick28 1 t787 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w28 pick28 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t786 k28_1_10 k28_1_11
private theorem k28_1_13 : check w28 pick28 1 t2259 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w28 pick28 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t787 k28_1_9 k28_1_12
private theorem k28_1_14 : check w28 pick28 1 t2260 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w28 pick28 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t2256 t2259 k28_1_6 k28_1_13
theorem cov28_1 : PA.Covered 1 (OZ.Valid 1 w28.low w28.t w28.y w28.r w28.cap) (P33.root 1) :=
  Night6836Tree.sound w28 pick28 1 t2260 _ k28_1_14
private theorem k28_2_0 : check w28 pick28 2 t1337 ⟨2,7,4,16,2,52,2,220⟩ = true := by decide +kernel
private theorem k28_2_1 : check w28 pick28 2 t1338 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k28_2_2 : check w28 pick28 2 t1339 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w28 pick28 2 ⟨2,7,4,16,0,52,0,450⟩ 3 220 t1337 t1338 k28_2_0 k28_2_1
theorem cov28_2 : PA.Covered 2 (OZ.Valid 2 w28.low w28.t w28.y w28.r w28.cap) (P33.root 2) :=
  Night6836Tree.sound w28 pick28 2 t1339 _ k28_2_2
theorem cov28_3 : PA.Covered 3 (OZ.Valid 3 w28.low w28.t w28.y w28.r w28.cap) (P33.root 3) :=
  Night6836Tree.sound w28 pick28 3 t564 _ (by decide +kernel)
theorem cov28_4 : PA.Covered 4 (OZ.Valid 4 w28.low w28.t w28.y w28.r w28.cap) (P33.root 4) :=
  Night6836Tree.sound w28 pick28 4 t565 _ (by decide +kernel)
theorem cov28_5 : PA.Covered 5 (OZ.Valid 5 w28.low w28.t w28.y w28.r w28.cap) (P33.root 5) :=
  Night6836Tree.sound w28 pick28 5 t566 _ (by decide +kernel)
theorem cov28_6 : PA.Covered 6 (OZ.Valid 6 w28.low w28.t w28.y w28.r w28.cap) (P33.root 6) :=
  Night6836Tree.sound w28 pick28 6 t567 _ (by decide +kernel)
theorem cov28_7 : PA.Covered 7 (OZ.Valid 7 w28.low w28.t w28.y w28.r w28.cap) (P33.root 7) :=
  Night6836Tree.sound w28 pick28 7 t2134 _ (by decide +kernel)
theorem window28 : P33.WindowCount w28 := by
  apply P33.window_count w28 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov28_1
  · exact cov28_2
  · exact cov28_3
  · exact cov28_4
  · exact cov28_5
  · exact cov28_6
  · exact cov28_7
def w29 : P33.Window := ⟨5,62,6383,6104,237631011665319175,28081,50000,5000000,81920000000⟩
def h29_0 : Height w29 := ⟨28081,50000,by decide +kernel⟩
def pick29 (cl : ℕ) : Height w29 := h29_0
private theorem k29_1_0 : check w29 pick29 1 t950 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k29_1_1 : check w29 pick29 1 t1266 ⟨1,7,2,16,1,52,43,76⟩ = true := by decide +kernel
private theorem k29_1_2 : check w29 pick29 1 t1267 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w29 pick29 1 ⟨1,7,2,16,1,52,1,76⟩ 3 42 t950 t1266 k29_1_0 k29_1_1
private theorem k29_1_3 : check w29 pick29 1 t2124 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k29_1_4 : check w29 pick29 1 t2130 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k29_1_5 : check w29 pick29 1 t2131 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w29 pick29 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t2124 t2130 k29_1_3 k29_1_4
private theorem k29_1_6 : check w29 pick29 1 t2132 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w29 pick29 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t1267 t2131 k29_1_2 k29_1_5
private theorem k29_1_7 : check w29 pick29 1 t1327 ⟨1,7,2,16,1,52,132,159⟩ = true := by decide +kernel
private theorem k29_1_8 : check w29 pick29 1 t1066 ⟨1,7,2,16,1,52,160,192⟩ = true := by decide +kernel
private theorem k29_1_9 : check w29 pick29 1 t1328 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w29 pick29 1 ⟨1,7,2,16,1,52,132,192⟩ 3 159 t1327 t1066 k29_1_7 k29_1_8
private theorem k29_1_10 : check w29 pick29 1 t2262 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k29_1_11 : check w29 pick29 1 t1507 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k29_1_12 : check w29 pick29 1 t2263 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w29 pick29 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t2262 t1507 k29_1_10 k29_1_11
private theorem k29_1_13 : check w29 pick29 1 t2264 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w29 pick29 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t1328 t2263 k29_1_9 k29_1_12
private theorem k29_1_14 : check w29 pick29 1 t2265 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w29 pick29 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t2132 t2264 k29_1_6 k29_1_13
theorem cov29_1 : PA.Covered 1 (OZ.Valid 1 w29.low w29.t w29.y w29.r w29.cap) (P33.root 1) :=
  Night6836Tree.sound w29 pick29 1 t2265 _ k29_1_14
private theorem k29_2_0 : check w29 pick29 2 t2271 ⟨2,7,4,16,2,52,2,193⟩ = true := by decide +kernel
private theorem k29_2_1 : check w29 pick29 2 t2276 ⟨2,7,4,16,2,52,194,450⟩ = true := by decide +kernel
private theorem k29_2_2 : check w29 pick29 2 t2277 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w29 pick29 2 ⟨2,7,4,16,0,52,0,450⟩ 3 193 t2271 t2276 k29_2_0 k29_2_1
theorem cov29_2 : PA.Covered 2 (OZ.Valid 2 w29.low w29.t w29.y w29.r w29.cap) (P33.root 2) :=
  Night6836Tree.sound w29 pick29 2 t2277 _ k29_2_2
theorem cov29_3 : PA.Covered 3 (OZ.Valid 3 w29.low w29.t w29.y w29.r w29.cap) (P33.root 3) :=
  Night6836Tree.sound w29 pick29 3 t564 _ (by decide +kernel)
theorem cov29_4 : PA.Covered 4 (OZ.Valid 4 w29.low w29.t w29.y w29.r w29.cap) (P33.root 4) :=
  Night6836Tree.sound w29 pick29 4 t565 _ (by decide +kernel)
theorem cov29_5 : PA.Covered 5 (OZ.Valid 5 w29.low w29.t w29.y w29.r w29.cap) (P33.root 5) :=
  Night6836Tree.sound w29 pick29 5 t566 _ (by decide +kernel)
theorem cov29_6 : PA.Covered 6 (OZ.Valid 6 w29.low w29.t w29.y w29.r w29.cap) (P33.root 6) :=
  Night6836Tree.sound w29 pick29 6 t567 _ (by decide +kernel)
theorem cov29_7 : PA.Covered 7 (OZ.Valid 7 w29.low w29.t w29.y w29.r w29.cap) (P33.root 7) :=
  Night6836Tree.sound w29 pick29 7 t2134 _ (by decide +kernel)
theorem window29 : P33.WindowCount w29 := by
  apply P33.window_count w29 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov29_1
  · exact cov29_2
  · exact cov29_3
  · exact cov29_4
  · exact cov29_5
  · exact cov29_6
  · exact cov29_7
end ProximityPrize.SubmissionLower.Night6836Bank
