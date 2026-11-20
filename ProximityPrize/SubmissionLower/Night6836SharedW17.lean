/- Apache-2.0. 68.36 local owner certificates by Bome2017, extending the packet method of BitWonka, Lucieno and 0xAndoroid. -/
import ProximityPrize.SubmissionLower.Night6836SharedT00
import ProximityPrize.SubmissionLower.Night6836SharedT01
import ProximityPrize.SubmissionLower.Night6836SharedT03
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w510 : P33.Window := ⟨8,50,6610,5661,245843863299752706,41470,27000,5000000,81920000000⟩
def h510_0 : Height w510 := ⟨41470,27000,by decide +kernel⟩
def h510_1 : Height w510 := ⟨45496,24000,by decide +kernel⟩
def h510_2 : Height w510 := ⟨50602,21000,by decide +kernel⟩
def h510_3 : Height w510 := ⟨57670,18000,by decide +kernel⟩
def h510_4 : Height w510 := ⟨68890,15000,by decide +kernel⟩
def pick510 (cl : ℕ) : Height w510 := if cl<16 then (if cl<2 then (h510_0) else (h510_1)) else (if cl<96 then (h510_2) else (if cl<853 then (h510_3) else (h510_4)))
private theorem k510_1_0 : check w510 pick510 1 t10580 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k510_1_1 : check w510 pick510 1 t10681 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k510_1_2 : check w510 pick510 1 t10682 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w510 pick510 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10580 t10681 k510_1_0 k510_1_1
private theorem k510_1_3 : check w510 pick510 1 t10594 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k510_1_4 : check w510 pick510 1 t9760 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k510_1_5 : check w510 pick510 1 t10595 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w510 pick510 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10594 t9760 k510_1_3 k510_1_4
private theorem k510_1_6 : check w510 pick510 1 t10683 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w510 pick510 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10682 t10595 k510_1_2 k510_1_5
private theorem k510_1_7 : check w510 pick510 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k510_1_8 : check w510 pick510 1 t10685 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k510_1_9 : check w510 pick510 1 t10686 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w510 pick510 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t9740 t10685 k510_1_7 k510_1_8
private theorem k510_1_10 : check w510 pick510 1 t6332 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k510_1_11 : check w510 pick510 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k510_1_12 : check w510 pick510 1 t10617 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w510 pick510 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t6332 t10616 k510_1_10 k510_1_11
private theorem k510_1_13 : check w510 pick510 1 t10687 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w510 pick510 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t10686 t10617 k510_1_9 k510_1_12
private theorem k510_1_14 : check w510 pick510 1 t10688 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w510 pick510 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10683 t10687 k510_1_6 k510_1_13
theorem cov510_1 : PA.Covered 1 (OZ.Valid 1 w510.low w510.t w510.y w510.r w510.cap) (P33.root 1) :=
  Night6836Tree.sound w510 pick510 1 t10688 _ k510_1_14
private theorem k510_2_0 : check w510 pick510 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k510_2_1 : check w510 pick510 2 t10645 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k510_2_2 : check w510 pick510 2 t10646 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w510 pick510 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10645 k510_2_0 k510_2_1
private theorem k510_2_3 : check w510 pick510 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k510_2_4 : check w510 pick510 2 t10652 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k510_2_5 : check w510 pick510 2 t10653 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w510 pick510 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t10652 k510_2_3 k510_2_4
private theorem k510_2_6 : check w510 pick510 2 t10654 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w510 pick510 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10646 t10653 k510_2_2 k510_2_5
theorem cov510_2 : PA.Covered 2 (OZ.Valid 2 w510.low w510.t w510.y w510.r w510.cap) (P33.root 2) :=
  Night6836Tree.sound w510 pick510 2 t10654 _ k510_2_6
theorem cov510_3 : PA.Covered 3 (OZ.Valid 3 w510.low w510.t w510.y w510.r w510.cap) (P33.root 3) :=
  Night6836Tree.sound w510 pick510 3 t564 _ (by decide +kernel)
theorem cov510_4 : PA.Covered 4 (OZ.Valid 4 w510.low w510.t w510.y w510.r w510.cap) (P33.root 4) :=
  Night6836Tree.sound w510 pick510 4 t565 _ (by decide +kernel)
theorem cov510_5 : PA.Covered 5 (OZ.Valid 5 w510.low w510.t w510.y w510.r w510.cap) (P33.root 5) :=
  Night6836Tree.sound w510 pick510 5 t566 _ (by decide +kernel)
theorem cov510_6 : PA.Covered 6 (OZ.Valid 6 w510.low w510.t w510.y w510.r w510.cap) (P33.root 6) :=
  Night6836Tree.sound w510 pick510 6 t567 _ (by decide +kernel)
theorem cov510_7 : PA.Covered 7 (OZ.Valid 7 w510.low w510.t w510.y w510.r w510.cap) (P33.root 7) :=
  Night6836Tree.sound w510 pick510 7 t568 _ (by decide +kernel)
theorem window510 : P33.WindowCount w510 := by
  apply P33.window_count w510 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov510_1
  · exact cov510_2
  · exact cov510_3
  · exact cov510_4
  · exact cov510_5
  · exact cov510_6
  · exact cov510_7
def w511 : P33.Window := ⟨8,50,6802,6734,246962124678642848,37073,21000,5000000,81920000000⟩
def h511_0 : Height w511 := ⟨37073,21000,by decide +kernel⟩
def h511_1 : Height w511 := ⟨41892,18000,by decide +kernel⟩
def h511_2 : Height w511 := ⟨48892,15000,by decide +kernel⟩
def h511_3 : Height w511 := ⟨61267,12000,by decide +kernel⟩
def pick511 (cl : ℕ) : Height w511 := if cl<91 then (if cl<10 then (h511_0) else (h511_1)) else (if cl<925 then (h511_2) else (h511_3))
private theorem k511_1_0 : check w511 pick511 1 t10659 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k511_1_1 : check w511 pick511 1 t10698 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k511_1_2 : check w511 pick511 1 t10699 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w511 pick511 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10659 t10698 k511_1_0 k511_1_1
private theorem k511_1_3 : check w511 pick511 1 t10674 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k511_1_4 : check w511 pick511 1 t10664 ⟨1,7,2,16,1,52,111,138⟩ = true := by decide +kernel
private theorem k511_1_5 : check w511 pick511 1 t10675 ⟨1,7,2,16,1,52,84,138⟩ = true := glue w511 pick511 1 ⟨1,7,2,16,1,52,84,138⟩ 3 110 t10674 t10664 k511_1_3 k511_1_4
private theorem k511_1_6 : check w511 pick511 1 t10700 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w511 pick511 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10699 t10675 k511_1_2 k511_1_5
private theorem k511_1_7 : check w511 pick511 1 t4077 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k511_1_8 : check w511 pick511 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k511_1_9 : check w511 pick511 1 t4091 ⟨1,7,2,16,1,52,139,192⟩ = true := glue w511 pick511 1 ⟨1,7,2,16,1,52,139,192⟩ 3 165 t4077 t4090 k511_1_7 k511_1_8
private theorem k511_1_10 : check w511 pick511 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k511_1_11 : check w511 pick511 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k511_1_12 : check w511 pick511 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w511 pick511 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k511_1_10 k511_1_11
private theorem k511_1_13 : check w511 pick511 1 t10668 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w511 pick511 1 ⟨1,7,2,16,1,52,139,450⟩ 3 192 t4091 t10667 k511_1_9 k511_1_12
private theorem k511_1_14 : check w511 pick511 1 t10701 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w511 pick511 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10700 t10668 k511_1_6 k511_1_13
theorem cov511_1 : PA.Covered 1 (OZ.Valid 1 w511.low w511.t w511.y w511.r w511.cap) (P33.root 1) :=
  Night6836Tree.sound w511 pick511 1 t10701 _ k511_1_14
private theorem k511_2_0 : check w511 pick511 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k511_2_1 : check w511 pick511 2 t10645 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k511_2_2 : check w511 pick511 2 t10646 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w511 pick511 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10645 k511_2_0 k511_2_1
private theorem k511_2_3 : check w511 pick511 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k511_2_4 : check w511 pick511 2 t10652 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k511_2_5 : check w511 pick511 2 t10653 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w511 pick511 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t10652 k511_2_3 k511_2_4
private theorem k511_2_6 : check w511 pick511 2 t10654 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w511 pick511 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10646 t10653 k511_2_2 k511_2_5
theorem cov511_2 : PA.Covered 2 (OZ.Valid 2 w511.low w511.t w511.y w511.r w511.cap) (P33.root 2) :=
  Night6836Tree.sound w511 pick511 2 t10654 _ k511_2_6
theorem cov511_3 : PA.Covered 3 (OZ.Valid 3 w511.low w511.t w511.y w511.r w511.cap) (P33.root 3) :=
  Night6836Tree.sound w511 pick511 3 t564 _ (by decide +kernel)
theorem cov511_4 : PA.Covered 4 (OZ.Valid 4 w511.low w511.t w511.y w511.r w511.cap) (P33.root 4) :=
  Night6836Tree.sound w511 pick511 4 t565 _ (by decide +kernel)
theorem cov511_5 : PA.Covered 5 (OZ.Valid 5 w511.low w511.t w511.y w511.r w511.cap) (P33.root 5) :=
  Night6836Tree.sound w511 pick511 5 t566 _ (by decide +kernel)
theorem cov511_6 : PA.Covered 6 (OZ.Valid 6 w511.low w511.t w511.y w511.r w511.cap) (P33.root 6) :=
  Night6836Tree.sound w511 pick511 6 t567 _ (by decide +kernel)
theorem cov511_7 : PA.Covered 7 (OZ.Valid 7 w511.low w511.t w511.y w511.r w511.cap) (P33.root 7) :=
  Night6836Tree.sound w511 pick511 7 t568 _ (by decide +kernel)
theorem window511 : P33.WindowCount w511 := by
  apply P33.window_count w511 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov511_1
  · exact cov511_2
  · exact cov511_3
  · exact cov511_4
  · exact cov511_5
  · exact cov511_6
  · exact cov511_7
def w512 : P33.Window := ⟨8,51,6733,6658,240418995135942313,38880,21000,5000000,81920000000⟩
def h512_0 : Height w512 := ⟨38880,21000,by decide +kernel⟩
def h512_1 : Height w512 := ⟨43883,18000,by decide +kernel⟩
def h512_2 : Height w512 := ⟨51203,15000,by decide +kernel⟩
def h512_3 : Height w512 := ⟨64271,12000,by decide +kernel⟩
def pick512 (cl : ℕ) : Height w512 := if cl<117 then (if cl<14 then (h512_0) else (h512_1)) else (if cl<961 then (h512_2) else (h512_3))
private theorem k512_1_0 : check w512 pick512 1 t10707 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k512_1_1 : check w512 pick512 1 t10720 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k512_1_2 : check w512 pick512 1 t10721 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w512 pick512 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10707 t10720 k512_1_0 k512_1_1
private theorem k512_1_3 : check w512 pick512 1 t10739 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k512_1_4 : check w512 pick512 1 t10749 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k512_1_5 : check w512 pick512 1 t10750 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w512 pick512 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10739 t10749 k512_1_3 k512_1_4
private theorem k512_1_6 : check w512 pick512 1 t10751 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w512 pick512 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10721 t10750 k512_1_2 k512_1_5
private theorem k512_1_7 : check w512 pick512 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k512_1_8 : check w512 pick512 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k512_1_9 : check w512 pick512 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w512 pick512 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k512_1_7 k512_1_8
private theorem k512_1_10 : check w512 pick512 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k512_1_11 : check w512 pick512 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w512 pick512 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k512_1_9 k512_1_10
private theorem k512_1_12 : check w512 pick512 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k512_1_13 : check w512 pick512 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k512_1_14 : check w512 pick512 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w512 pick512 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k512_1_12 k512_1_13
private theorem k512_1_15 : check w512 pick512 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w512 pick512 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k512_1_11 k512_1_14
private theorem k512_1_16 : check w512 pick512 1 t10753 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w512 pick512 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10751 t10752 k512_1_6 k512_1_15
theorem cov512_1 : PA.Covered 1 (OZ.Valid 1 w512.low w512.t w512.y w512.r w512.cap) (P33.root 1) :=
  Night6836Tree.sound w512 pick512 1 t10753 _ k512_1_16
private theorem k512_2_0 : check w512 pick512 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k512_2_1 : check w512 pick512 2 t10765 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k512_2_2 : check w512 pick512 2 t10766 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w512 pick512 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10765 k512_2_0 k512_2_1
private theorem k512_2_3 : check w512 pick512 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k512_2_4 : check w512 pick512 2 t10652 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k512_2_5 : check w512 pick512 2 t10653 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w512 pick512 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t10652 k512_2_3 k512_2_4
private theorem k512_2_6 : check w512 pick512 2 t10767 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w512 pick512 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10766 t10653 k512_2_2 k512_2_5
theorem cov512_2 : PA.Covered 2 (OZ.Valid 2 w512.low w512.t w512.y w512.r w512.cap) (P33.root 2) :=
  Night6836Tree.sound w512 pick512 2 t10767 _ k512_2_6
theorem cov512_3 : PA.Covered 3 (OZ.Valid 3 w512.low w512.t w512.y w512.r w512.cap) (P33.root 3) :=
  Night6836Tree.sound w512 pick512 3 t4151 _ (by decide +kernel)
theorem cov512_4 : PA.Covered 4 (OZ.Valid 4 w512.low w512.t w512.y w512.r w512.cap) (P33.root 4) :=
  Night6836Tree.sound w512 pick512 4 t565 _ (by decide +kernel)
theorem cov512_5 : PA.Covered 5 (OZ.Valid 5 w512.low w512.t w512.y w512.r w512.cap) (P33.root 5) :=
  Night6836Tree.sound w512 pick512 5 t566 _ (by decide +kernel)
theorem cov512_6 : PA.Covered 6 (OZ.Valid 6 w512.low w512.t w512.y w512.r w512.cap) (P33.root 6) :=
  Night6836Tree.sound w512 pick512 6 t567 _ (by decide +kernel)
theorem cov512_7 : PA.Covered 7 (OZ.Valid 7 w512.low w512.t w512.y w512.r w512.cap) (P33.root 7) :=
  Night6836Tree.sound w512 pick512 7 t568 _ (by decide +kernel)
theorem window512 : P33.WindowCount w512 := by
  apply P33.window_count w512 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov512_1
  · exact cov512_2
  · exact cov512_3
  · exact cov512_4
  · exact cov512_5
  · exact cov512_6
  · exact cov512_7
def w513 : P33.Window := ⟨8,52,6657,6575,241670110638656380,36851,24000,5000000,81920000000⟩
def h513_0 : Height w513 := ⟨36851,24000,by decide +kernel⟩
def h513_1 : Height w513 := ⟨40822,21000,by decide +kernel⟩
def h513_2 : Height w513 := ⟨46030,18000,by decide +kernel⟩
def h513_3 : Height w513 := ⟨53711,15000,by decide +kernel⟩
def h513_4 : Height w513 := ⟨67567,12000,by decide +kernel⟩
def pick513 (cl : ℕ) : Height w513 := if cl<20 then (if cl<2 then (h513_0) else (h513_1)) else (if cl<157 then (h513_2) else (if cl<976 then (h513_3) else (h513_4)))
private theorem k513_1_0 : check w513 pick513 1 t10707 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k513_1_1 : check w513 pick513 1 t10720 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k513_1_2 : check w513 pick513 1 t10721 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w513 pick513 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10707 t10720 k513_1_0 k513_1_1
private theorem k513_1_3 : check w513 pick513 1 t10739 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k513_1_4 : check w513 pick513 1 t10749 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k513_1_5 : check w513 pick513 1 t10750 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w513 pick513 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10739 t10749 k513_1_3 k513_1_4
private theorem k513_1_6 : check w513 pick513 1 t10751 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w513 pick513 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10721 t10750 k513_1_2 k513_1_5
private theorem k513_1_7 : check w513 pick513 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k513_1_8 : check w513 pick513 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k513_1_9 : check w513 pick513 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w513 pick513 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k513_1_7 k513_1_8
private theorem k513_1_10 : check w513 pick513 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k513_1_11 : check w513 pick513 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w513 pick513 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k513_1_9 k513_1_10
private theorem k513_1_12 : check w513 pick513 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k513_1_13 : check w513 pick513 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k513_1_14 : check w513 pick513 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w513 pick513 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k513_1_12 k513_1_13
private theorem k513_1_15 : check w513 pick513 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w513 pick513 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k513_1_11 k513_1_14
private theorem k513_1_16 : check w513 pick513 1 t10753 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w513 pick513 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10751 t10752 k513_1_6 k513_1_15
theorem cov513_1 : PA.Covered 1 (OZ.Valid 1 w513.low w513.t w513.y w513.r w513.cap) (P33.root 1) :=
  Night6836Tree.sound w513 pick513 1 t10753 _ k513_1_16
private theorem k513_2_0 : check w513 pick513 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k513_2_1 : check w513 pick513 2 t10765 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k513_2_2 : check w513 pick513 2 t10766 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w513 pick513 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10765 k513_2_0 k513_2_1
private theorem k513_2_3 : check w513 pick513 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k513_2_4 : check w513 pick513 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k513_2_5 : check w513 pick513 2 t10768 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w513 pick513 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t9411 k513_2_3 k513_2_4
private theorem k513_2_6 : check w513 pick513 2 t10769 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w513 pick513 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10766 t10768 k513_2_2 k513_2_5
theorem cov513_2 : PA.Covered 2 (OZ.Valid 2 w513.low w513.t w513.y w513.r w513.cap) (P33.root 2) :=
  Night6836Tree.sound w513 pick513 2 t10769 _ k513_2_6
theorem cov513_3 : PA.Covered 3 (OZ.Valid 3 w513.low w513.t w513.y w513.r w513.cap) (P33.root 3) :=
  Night6836Tree.sound w513 pick513 3 t4151 _ (by decide +kernel)
theorem cov513_4 : PA.Covered 4 (OZ.Valid 4 w513.low w513.t w513.y w513.r w513.cap) (P33.root 4) :=
  Night6836Tree.sound w513 pick513 4 t565 _ (by decide +kernel)
theorem cov513_5 : PA.Covered 5 (OZ.Valid 5 w513.low w513.t w513.y w513.r w513.cap) (P33.root 5) :=
  Night6836Tree.sound w513 pick513 5 t566 _ (by decide +kernel)
theorem cov513_6 : PA.Covered 6 (OZ.Valid 6 w513.low w513.t w513.y w513.r w513.cap) (P33.root 6) :=
  Night6836Tree.sound w513 pick513 6 t567 _ (by decide +kernel)
theorem cov513_7 : PA.Covered 7 (OZ.Valid 7 w513.low w513.t w513.y w513.r w513.cap) (P33.root 7) :=
  Night6836Tree.sound w513 pick513 7 t568 _ (by decide +kernel)
theorem window513 : P33.WindowCount w513 := by
  apply P33.window_count w513 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov513_1
  · exact cov513_2
  · exact cov513_3
  · exact cov513_4
  · exact cov513_5
  · exact cov513_6
  · exact cov513_7
def w514 : P33.Window := ⟨8,53,5232,4283,244651861410267318,59119,36000,5000000,81920000000⟩
def h514_0 : Height w514 := ⟨59119,36000,by decide +kernel⟩
def h514_1 : Height w514 := ⟨63125,33000,by decide +kernel⟩
def h514_2 : Height w514 := ⟨67853,30000,by decide +kernel⟩
def h514_3 : Height w514 := ⟨73666,27000,by decide +kernel⟩
def h514_4 : Height w514 := ⟨81223,24000,by decide +kernel⟩
def h514_5 : Height w514 := ⟨91843,21000,by decide +kernel⟩
def pick514 (cl : ℕ) : Height w514 := if cl<32 then (if cl<2 then (h514_0) else (if cl<10 then (h514_1) else (h514_2))) else (if cl<145 then (h514_3) else (if cl<733 then (h514_4) else (h514_5)))
private theorem k514_1_0 : check w514 pick514 1 t5132 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k514_1_1 : check w514 pick514 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k514_1_2 : check w514 pick514 1 t10770 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w514 pick514 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t5132 t10040 k514_1_0 k514_1_1
private theorem k514_1_3 : check w514 pick514 1 t10771 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k514_1_4 : check w514 pick514 1 t10772 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w514 pick514 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10770 t10771 k514_1_2 k514_1_3
private theorem k514_1_5 : check w514 pick514 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k514_1_6 : check w514 pick514 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k514_1_7 : check w514 pick514 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w514 pick514 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k514_1_5 k514_1_6
private theorem k514_1_8 : check w514 pick514 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k514_1_9 : check w514 pick514 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k514_1_10 : check w514 pick514 1 t10502 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w514 pick514 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10064 k514_1_8 k514_1_9
private theorem k514_1_11 : check w514 pick514 1 t10503 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w514 pick514 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t10502 k514_1_7 k514_1_10
private theorem k514_1_12 : check w514 pick514 1 t10773 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w514 pick514 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10772 t10503 k514_1_4 k514_1_11
theorem cov514_1 : PA.Covered 1 (OZ.Valid 1 w514.low w514.t w514.y w514.r w514.cap) (P33.root 1) :=
  Night6836Tree.sound w514 pick514 1 t10773 _ k514_1_12
private theorem k514_2_0 : check w514 pick514 2 t10269 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k514_2_1 : check w514 pick514 2 t10774 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k514_2_2 : check w514 pick514 2 t10775 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w514 pick514 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10269 t10774 k514_2_0 k514_2_1
theorem cov514_2 : PA.Covered 2 (OZ.Valid 2 w514.low w514.t w514.y w514.r w514.cap) (P33.root 2) :=
  Night6836Tree.sound w514 pick514 2 t10775 _ k514_2_2
theorem cov514_3 : PA.Covered 3 (OZ.Valid 3 w514.low w514.t w514.y w514.r w514.cap) (P33.root 3) :=
  Night6836Tree.sound w514 pick514 3 t564 _ (by decide +kernel)
theorem cov514_4 : PA.Covered 4 (OZ.Valid 4 w514.low w514.t w514.y w514.r w514.cap) (P33.root 4) :=
  Night6836Tree.sound w514 pick514 4 t565 _ (by decide +kernel)
theorem cov514_5 : PA.Covered 5 (OZ.Valid 5 w514.low w514.t w514.y w514.r w514.cap) (P33.root 5) :=
  Night6836Tree.sound w514 pick514 5 t566 _ (by decide +kernel)
theorem cov514_6 : PA.Covered 6 (OZ.Valid 6 w514.low w514.t w514.y w514.r w514.cap) (P33.root 6) :=
  Night6836Tree.sound w514 pick514 6 t567 _ (by decide +kernel)
theorem cov514_7 : PA.Covered 7 (OZ.Valid 7 w514.low w514.t w514.y w514.r w514.cap) (P33.root 7) :=
  Night6836Tree.sound w514 pick514 7 t2134 _ (by decide +kernel)
theorem window514 : P33.WindowCount w514 := by
  apply P33.window_count w514 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov514_1
  · exact cov514_2
  · exact cov514_3
  · exact cov514_4
  · exact cov514_5
  · exact cov514_6
  · exact cov514_7
def w515 : P33.Window := ⟨8,53,6574,5787,244938039117722629,43340,27000,5000000,81920000000⟩
def h515_0 : Height w515 := ⟨43340,27000,by decide +kernel⟩
def h515_1 : Height w515 := ⟨47371,24000,by decide +kernel⟩
def h515_2 : Height w515 := ⟨52474,21000,by decide +kernel⟩
def h515_3 : Height w515 := ⟨59508,18000,by decide +kernel⟩
def h515_4 : Height w515 := ⟨70592,15000,by decide +kernel⟩
def pick515 (cl : ℕ) : Height w515 := if cl<16 then (if cl<2 then (h515_0) else (h515_1)) else (if cl<94 then (h515_2) else (if cl<853 then (h515_3) else (h515_4)))
private theorem k515_1_0 : check w515 pick515 1 t4544 ⟨1,7,2,16,1,52,1,42⟩ = true := by decide +kernel
private theorem k515_1_1 : check w515 pick515 1 t10776 ⟨1,7,2,16,1,52,43,69⟩ = true := by decide +kernel
private theorem k515_1_2 : check w515 pick515 1 t10777 ⟨1,7,2,16,1,52,1,69⟩ = true := glue w515 pick515 1 ⟨1,7,2,16,1,52,1,69⟩ 3 42 t4544 t10776 k515_1_0 k515_1_1
private theorem k515_1_3 : check w515 pick515 1 t10778 ⟨1,7,2,16,1,52,70,97⟩ = true := by decide +kernel
private theorem k515_1_4 : check w515 pick515 1 t10780 ⟨1,7,2,16,1,52,98,131⟩ = true := by decide +kernel
private theorem k515_1_5 : check w515 pick515 1 t10781 ⟨1,7,2,16,1,52,70,131⟩ = true := glue w515 pick515 1 ⟨1,7,2,16,1,52,70,131⟩ 3 97 t10778 t10780 k515_1_3 k515_1_4
private theorem k515_1_6 : check w515 pick515 1 t10782 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w515 pick515 1 ⟨1,7,2,16,1,52,1,131⟩ 3 69 t10777 t10781 k515_1_2 k515_1_5
private theorem k515_1_7 : check w515 pick515 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k515_1_8 : check w515 pick515 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k515_1_9 : check w515 pick515 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w515 pick515 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k515_1_7 k515_1_8
private theorem k515_1_10 : check w515 pick515 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k515_1_11 : check w515 pick515 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w515 pick515 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k515_1_9 k515_1_10
private theorem k515_1_12 : check w515 pick515 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k515_1_13 : check w515 pick515 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k515_1_14 : check w515 pick515 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w515 pick515 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k515_1_12 k515_1_13
private theorem k515_1_15 : check w515 pick515 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w515 pick515 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k515_1_11 k515_1_14
private theorem k515_1_16 : check w515 pick515 1 t10783 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w515 pick515 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10782 t10752 k515_1_6 k515_1_15
theorem cov515_1 : PA.Covered 1 (OZ.Valid 1 w515.low w515.t w515.y w515.r w515.cap) (P33.root 1) :=
  Night6836Tree.sound w515 pick515 1 t10783 _ k515_1_16
private theorem k515_2_0 : check w515 pick515 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k515_2_1 : check w515 pick515 2 t10765 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k515_2_2 : check w515 pick515 2 t10766 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w515 pick515 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10765 k515_2_0 k515_2_1
private theorem k515_2_3 : check w515 pick515 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k515_2_4 : check w515 pick515 2 t10652 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k515_2_5 : check w515 pick515 2 t10653 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w515 pick515 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t10652 k515_2_3 k515_2_4
private theorem k515_2_6 : check w515 pick515 2 t10767 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w515 pick515 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10766 t10653 k515_2_2 k515_2_5
theorem cov515_2 : PA.Covered 2 (OZ.Valid 2 w515.low w515.t w515.y w515.r w515.cap) (P33.root 2) :=
  Night6836Tree.sound w515 pick515 2 t10767 _ k515_2_6
theorem cov515_3 : PA.Covered 3 (OZ.Valid 3 w515.low w515.t w515.y w515.r w515.cap) (P33.root 3) :=
  Night6836Tree.sound w515 pick515 3 t4151 _ (by decide +kernel)
theorem cov515_4 : PA.Covered 4 (OZ.Valid 4 w515.low w515.t w515.y w515.r w515.cap) (P33.root 4) :=
  Night6836Tree.sound w515 pick515 4 t565 _ (by decide +kernel)
theorem cov515_5 : PA.Covered 5 (OZ.Valid 5 w515.low w515.t w515.y w515.r w515.cap) (P33.root 5) :=
  Night6836Tree.sound w515 pick515 5 t566 _ (by decide +kernel)
theorem cov515_6 : PA.Covered 6 (OZ.Valid 6 w515.low w515.t w515.y w515.r w515.cap) (P33.root 6) :=
  Night6836Tree.sound w515 pick515 6 t567 _ (by decide +kernel)
theorem cov515_7 : PA.Covered 7 (OZ.Valid 7 w515.low w515.t w515.y w515.r w515.cap) (P33.root 7) :=
  Night6836Tree.sound w515 pick515 7 t568 _ (by decide +kernel)
theorem window515 : P33.WindowCount w515 := by
  apply P33.window_count w515 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov515_1
  · exact cov515_2
  · exact cov515_3
  · exact cov515_4
  · exact cov515_5
  · exact cov515_6
  · exact cov515_7
def w516 : P33.Window := ⟨8,53,6574,6450,243433538391010730,39167,24000,5000000,81920000000⟩
def h516_0 : Height w516 := ⟨39167,24000,by decide +kernel⟩
def h516_1 : Height w516 := ⟨43325,21000,by decide +kernel⟩
def h516_2 : Height w516 := ⟨48826,18000,by decide +kernel⟩
def h516_3 : Height w516 := ⟨57029,15000,by decide +kernel⟩
def h516_4 : Height w516 := ⟨72055,12000,by decide +kernel⟩
def pick516 (cl : ℕ) : Height w516 := if cl<24 then (if cl<4 then (h516_0) else (h516_1)) else (if cl<206 then (h516_2) else (if cl<1002 then (h516_3) else (h516_4)))
private theorem k516_1_0 : check w516 pick516 1 t10707 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k516_1_1 : check w516 pick516 1 t10720 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k516_1_2 : check w516 pick516 1 t10721 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w516 pick516 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10707 t10720 k516_1_0 k516_1_1
private theorem k516_1_3 : check w516 pick516 1 t10739 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k516_1_4 : check w516 pick516 1 t10749 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k516_1_5 : check w516 pick516 1 t10750 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w516 pick516 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10739 t10749 k516_1_3 k516_1_4
private theorem k516_1_6 : check w516 pick516 1 t10751 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w516 pick516 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10721 t10750 k516_1_2 k516_1_5
private theorem k516_1_7 : check w516 pick516 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k516_1_8 : check w516 pick516 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k516_1_9 : check w516 pick516 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w516 pick516 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k516_1_7 k516_1_8
private theorem k516_1_10 : check w516 pick516 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k516_1_11 : check w516 pick516 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w516 pick516 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k516_1_9 k516_1_10
private theorem k516_1_12 : check w516 pick516 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k516_1_13 : check w516 pick516 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k516_1_14 : check w516 pick516 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w516 pick516 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k516_1_12 k516_1_13
private theorem k516_1_15 : check w516 pick516 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w516 pick516 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k516_1_11 k516_1_14
private theorem k516_1_16 : check w516 pick516 1 t10753 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w516 pick516 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10751 t10752 k516_1_6 k516_1_15
theorem cov516_1 : PA.Covered 1 (OZ.Valid 1 w516.low w516.t w516.y w516.r w516.cap) (P33.root 1) :=
  Night6836Tree.sound w516 pick516 1 t10753 _ k516_1_16
private theorem k516_2_0 : check w516 pick516 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k516_2_1 : check w516 pick516 2 t10765 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k516_2_2 : check w516 pick516 2 t10766 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w516 pick516 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10765 k516_2_0 k516_2_1
private theorem k516_2_3 : check w516 pick516 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k516_2_4 : check w516 pick516 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k516_2_5 : check w516 pick516 2 t10768 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w516 pick516 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t9411 k516_2_3 k516_2_4
private theorem k516_2_6 : check w516 pick516 2 t10769 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w516 pick516 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10766 t10768 k516_2_2 k516_2_5
theorem cov516_2 : PA.Covered 2 (OZ.Valid 2 w516.low w516.t w516.y w516.r w516.cap) (P33.root 2) :=
  Night6836Tree.sound w516 pick516 2 t10769 _ k516_2_6
theorem cov516_3 : PA.Covered 3 (OZ.Valid 3 w516.low w516.t w516.y w516.r w516.cap) (P33.root 3) :=
  Night6836Tree.sound w516 pick516 3 t4151 _ (by decide +kernel)
theorem cov516_4 : PA.Covered 4 (OZ.Valid 4 w516.low w516.t w516.y w516.r w516.cap) (P33.root 4) :=
  Night6836Tree.sound w516 pick516 4 t565 _ (by decide +kernel)
theorem cov516_5 : PA.Covered 5 (OZ.Valid 5 w516.low w516.t w516.y w516.r w516.cap) (P33.root 5) :=
  Night6836Tree.sound w516 pick516 5 t566 _ (by decide +kernel)
theorem cov516_6 : PA.Covered 6 (OZ.Valid 6 w516.low w516.t w516.y w516.r w516.cap) (P33.root 6) :=
  Night6836Tree.sound w516 pick516 6 t567 _ (by decide +kernel)
theorem cov516_7 : PA.Covered 7 (OZ.Valid 7 w516.low w516.t w516.y w516.r w516.cap) (P33.root 7) :=
  Night6836Tree.sound w516 pick516 7 t568 _ (by decide +kernel)
theorem window516 : P33.WindowCount w516 := by
  apply P33.window_count w516 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov516_1
  · exact cov516_2
  · exact cov516_3
  · exact cov516_4
  · exact cov516_5
  · exact cov516_6
  · exact cov516_7
def w517 : P33.Window := ⟨8,54,6449,6126,245242723669719401,43991,24000,5000000,81920000000⟩
def h517_0 : Height w517 := ⟨43991,24000,by decide +kernel⟩
def h517_1 : Height w517 := ⟨48618,21000,by decide +kernel⟩
def h517_2 : Height w517 := ⟨54870,18000,by decide +kernel⟩
def h517_3 : Height w517 := ⟨64449,15000,by decide +kernel⟩
def pick517 (cl : ℕ) : Height w517 := if cl<45 then (if cl<6 then (h517_0) else (h517_1)) else (if cl<331 then (h517_2) else (h517_3))
private theorem k517_1_0 : check w517 pick517 1 t10707 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k517_1_1 : check w517 pick517 1 t10720 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k517_1_2 : check w517 pick517 1 t10721 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w517 pick517 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10707 t10720 k517_1_0 k517_1_1
private theorem k517_1_3 : check w517 pick517 1 t10739 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k517_1_4 : check w517 pick517 1 t10749 ⟨1,7,2,16,1,52,105,131⟩ = true := by decide +kernel
private theorem k517_1_5 : check w517 pick517 1 t10750 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w517 pick517 1 ⟨1,7,2,16,1,52,77,131⟩ 3 104 t10739 t10749 k517_1_3 k517_1_4
private theorem k517_1_6 : check w517 pick517 1 t10751 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w517 pick517 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10721 t10750 k517_1_2 k517_1_5
private theorem k517_1_7 : check w517 pick517 1 t4629 ⟨1,7,2,5,1,52,132,165⟩ = true := by decide +kernel
private theorem k517_1_8 : check w517 pick517 1 t4633 ⟨1,7,6,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k517_1_9 : check w517 pick517 1 t4634 ⟨1,7,2,16,1,52,132,165⟩ = true := glue w517 pick517 1 ⟨1,7,2,16,1,52,132,165⟩ 1 5 t4629 t4633 k517_1_7 k517_1_8
private theorem k517_1_10 : check w517 pick517 1 t4090 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k517_1_11 : check w517 pick517 1 t4635 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w517 pick517 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t4634 t4090 k517_1_9 k517_1_10
private theorem k517_1_12 : check w517 pick517 1 t4097 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k517_1_13 : check w517 pick517 1 t10616 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k517_1_14 : check w517 pick517 1 t10667 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w517 pick517 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t4097 t10616 k517_1_12 k517_1_13
private theorem k517_1_15 : check w517 pick517 1 t10752 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w517 pick517 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t4635 t10667 k517_1_11 k517_1_14
private theorem k517_1_16 : check w517 pick517 1 t10753 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w517 pick517 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10751 t10752 k517_1_6 k517_1_15
theorem cov517_1 : PA.Covered 1 (OZ.Valid 1 w517.low w517.t w517.y w517.r w517.cap) (P33.root 1) :=
  Night6836Tree.sound w517 pick517 1 t10753 _ k517_1_16
private theorem k517_2_0 : check w517 pick517 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k517_2_1 : check w517 pick517 2 t10765 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k517_2_2 : check w517 pick517 2 t10766 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w517 pick517 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10765 k517_2_0 k517_2_1
private theorem k517_2_3 : check w517 pick517 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k517_2_4 : check w517 pick517 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k517_2_5 : check w517 pick517 2 t10768 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w517 pick517 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t9411 k517_2_3 k517_2_4
private theorem k517_2_6 : check w517 pick517 2 t10769 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w517 pick517 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10766 t10768 k517_2_2 k517_2_5
theorem cov517_2 : PA.Covered 2 (OZ.Valid 2 w517.low w517.t w517.y w517.r w517.cap) (P33.root 2) :=
  Night6836Tree.sound w517 pick517 2 t10769 _ k517_2_6
theorem cov517_3 : PA.Covered 3 (OZ.Valid 3 w517.low w517.t w517.y w517.r w517.cap) (P33.root 3) :=
  Night6836Tree.sound w517 pick517 3 t4151 _ (by decide +kernel)
theorem cov517_4 : PA.Covered 4 (OZ.Valid 4 w517.low w517.t w517.y w517.r w517.cap) (P33.root 4) :=
  Night6836Tree.sound w517 pick517 4 t565 _ (by decide +kernel)
theorem cov517_5 : PA.Covered 5 (OZ.Valid 5 w517.low w517.t w517.y w517.r w517.cap) (P33.root 5) :=
  Night6836Tree.sound w517 pick517 5 t566 _ (by decide +kernel)
theorem cov517_6 : PA.Covered 6 (OZ.Valid 6 w517.low w517.t w517.y w517.r w517.cap) (P33.root 6) :=
  Night6836Tree.sound w517 pick517 6 t567 _ (by decide +kernel)
theorem cov517_7 : PA.Covered 7 (OZ.Valid 7 w517.low w517.t w517.y w517.r w517.cap) (P33.root 7) :=
  Night6836Tree.sound w517 pick517 7 t2134 _ (by decide +kernel)
theorem window517 : P33.WindowCount w517 := by
  apply P33.window_count w517 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov517_1
  · exact cov517_2
  · exact cov517_3
  · exact cov517_4
  · exact cov517_5
  · exact cov517_6
  · exact cov517_7
def w518 : P33.Window := ⟨8,55,6125,5787,246818793067494140,45655,27000,5000000,81920000000⟩
def h518_0 : Height w518 := ⟨45655,27000,by decide +kernel⟩
def h518_1 : Height w518 := ⟨49789,24000,by decide +kernel⟩
def h518_2 : Height w518 := ⟨55036,21000,by decide +kernel⟩
def h518_3 : Height w518 := ⟨62292,18000,by decide +kernel⟩
def h518_4 : Height w518 := ⟨73758,15000,by decide +kernel⟩
def pick518 (cl : ℕ) : Height w518 := if cl<20 then (if cl<3 then (h518_0) else (h518_1)) else (if cl<107 then (h518_2) else (if cl<925 then (h518_3) else (h518_4)))
private theorem k518_1_0 : check w518 pick518 1 t10784 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k518_1_1 : check w518 pick518 1 t10801 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k518_1_2 : check w518 pick518 1 t10802 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w518 pick518 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10784 t10801 k518_1_0 k518_1_1
private theorem k518_1_3 : check w518 pick518 1 t10806 ⟨1,7,2,16,1,20,77,138⟩ = true := by decide +kernel
private theorem k518_1_4 : check w518 pick518 1 t10514 ⟨1,7,2,16,21,52,77,138⟩ = true := by decide +kernel
private theorem k518_1_5 : check w518 pick518 1 t10807 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w518 pick518 1 ⟨1,7,2,16,1,52,77,138⟩ 2 20 t10806 t10514 k518_1_3 k518_1_4
private theorem k518_1_6 : check w518 pick518 1 t10808 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w518 pick518 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t10802 t10807 k518_1_2 k518_1_5
private theorem k518_1_7 : check w518 pick518 1 t9740 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k518_1_8 : check w518 pick518 1 t10685 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k518_1_9 : check w518 pick518 1 t10686 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w518 pick518 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t9740 t10685 k518_1_7 k518_1_8
private theorem k518_1_10 : check w518 pick518 1 t1662 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k518_1_11 : check w518 pick518 1 t10813 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k518_1_12 : check w518 pick518 1 t10814 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w518 pick518 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t1662 t10813 k518_1_10 k518_1_11
private theorem k518_1_13 : check w518 pick518 1 t10815 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w518 pick518 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t10686 t10814 k518_1_9 k518_1_12
private theorem k518_1_14 : check w518 pick518 1 t10816 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w518 pick518 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10808 t10815 k518_1_6 k518_1_13
theorem cov518_1 : PA.Covered 1 (OZ.Valid 1 w518.low w518.t w518.y w518.r w518.cap) (P33.root 1) :=
  Night6836Tree.sound w518 pick518 1 t10816 _ k518_1_14
private theorem k518_2_0 : check w518 pick518 2 t10631 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k518_2_1 : check w518 pick518 2 t10645 ⟨2,7,4,16,2,52,71,111⟩ = true := by decide +kernel
private theorem k518_2_2 : check w518 pick518 2 t10646 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w518 pick518 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10631 t10645 k518_2_0 k518_2_1
private theorem k518_2_3 : check w518 pick518 2 t10649 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k518_2_4 : check w518 pick518 2 t9411 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k518_2_5 : check w518 pick518 2 t10768 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w518 pick518 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10649 t9411 k518_2_3 k518_2_4
private theorem k518_2_6 : check w518 pick518 2 t10817 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w518 pick518 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10646 t10768 k518_2_2 k518_2_5
theorem cov518_2 : PA.Covered 2 (OZ.Valid 2 w518.low w518.t w518.y w518.r w518.cap) (P33.root 2) :=
  Night6836Tree.sound w518 pick518 2 t10817 _ k518_2_6
theorem cov518_3 : PA.Covered 3 (OZ.Valid 3 w518.low w518.t w518.y w518.r w518.cap) (P33.root 3) :=
  Night6836Tree.sound w518 pick518 3 t564 _ (by decide +kernel)
theorem cov518_4 : PA.Covered 4 (OZ.Valid 4 w518.low w518.t w518.y w518.r w518.cap) (P33.root 4) :=
  Night6836Tree.sound w518 pick518 4 t565 _ (by decide +kernel)
theorem cov518_5 : PA.Covered 5 (OZ.Valid 5 w518.low w518.t w518.y w518.r w518.cap) (P33.root 5) :=
  Night6836Tree.sound w518 pick518 5 t566 _ (by decide +kernel)
theorem cov518_6 : PA.Covered 6 (OZ.Valid 6 w518.low w518.t w518.y w518.r w518.cap) (P33.root 6) :=
  Night6836Tree.sound w518 pick518 6 t567 _ (by decide +kernel)
theorem cov518_7 : PA.Covered 7 (OZ.Valid 7 w518.low w518.t w518.y w518.r w518.cap) (P33.root 7) :=
  Night6836Tree.sound w518 pick518 7 t2134 _ (by decide +kernel)
theorem window518 : P33.WindowCount w518 := by
  apply P33.window_count w518 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov518_1
  · exact cov518_2
  · exact cov518_3
  · exact cov518_4
  · exact cov518_5
  · exact cov518_6
  · exact cov518_7
def w519 : P33.Window := ⟨8,56,5786,5433,246142518233146290,52196,27000,5000000,81920000000⟩
def h519_0 : Height w519 := ⟨52196,27000,by decide +kernel⟩
def h519_1 : Height w519 := ⟨56890,24000,by decide +kernel⟩
def h519_2 : Height w519 := ⟨62978,21000,by decide +kernel⟩
def h519_3 : Height w519 := ⟨71623,18000,by decide +kernel⟩
def h519_4 : Height w519 := ⟨85779,15000,by decide +kernel⟩
def pick519 (cl : ℕ) : Height w519 := if cl<41 then (if cl<10 then (h519_0) else (h519_1)) else (if cl<260 then (h519_2) else (if cl<984 then (h519_3) else (h519_4)))
private theorem k519_1_0 : check w519 pick519 1 t3666 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k519_1_1 : check w519 pick519 1 t10233 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k519_1_2 : check w519 pick519 1 t10234 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w519 pick519 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t3666 t10233 k519_1_0 k519_1_1
private theorem k519_1_3 : check w519 pick519 1 t10511 ⟨1,7,2,16,1,20,77,138⟩ = true := by decide +kernel
private theorem k519_1_4 : check w519 pick519 1 t10514 ⟨1,7,2,16,21,52,77,138⟩ = true := by decide +kernel
private theorem k519_1_5 : check w519 pick519 1 t10515 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w519 pick519 1 ⟨1,7,2,16,1,52,77,138⟩ 2 20 t10511 t10514 k519_1_3 k519_1_4
private theorem k519_1_6 : check w519 pick519 1 t10516 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w519 pick519 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t10234 t10515 k519_1_2 k519_1_5
private theorem k519_1_7 : check w519 pick519 1 t3199 ⟨1,7,2,16,1,52,139,165⟩ = true := by decide +kernel
private theorem k519_1_8 : check w519 pick519 1 t3371 ⟨1,7,2,16,1,52,166,199⟩ = true := by decide +kernel
private theorem k519_1_9 : check w519 pick519 1 t3372 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w519 pick519 1 ⟨1,7,2,16,1,52,139,199⟩ 3 165 t3199 t3371 k519_1_7 k519_1_8
private theorem k519_1_10 : check w519 pick519 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k519_1_11 : check w519 pick519 1 t10521 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k519_1_12 : check w519 pick519 1 t10818 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w519 pick519 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10521 k519_1_10 k519_1_11
private theorem k519_1_13 : check w519 pick519 1 t10819 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w519 pick519 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t3372 t10818 k519_1_9 k519_1_12
private theorem k519_1_14 : check w519 pick519 1 t10820 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w519 pick519 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10516 t10819 k519_1_6 k519_1_13
theorem cov519_1 : PA.Covered 1 (OZ.Valid 1 w519.low w519.t w519.y w519.r w519.cap) (P33.root 1) :=
  Night6836Tree.sound w519 pick519 1 t10820 _ k519_1_14
private theorem k519_2_0 : check w519 pick519 2 t10300 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k519_2_1 : check w519 pick519 2 t10312 ⟨2,7,4,16,2,52,71,84⟩ = true := by decide +kernel
private theorem k519_2_2 : check w519 pick519 2 t10827 ⟨2,7,4,16,2,52,85,111⟩ = true := by decide +kernel
private theorem k519_2_3 : check w519 pick519 2 t10828 ⟨2,7,4,16,2,52,71,111⟩ = true := glue w519 pick519 2 ⟨2,7,4,16,2,52,71,111⟩ 3 84 t10312 t10827 k519_2_1 k519_2_2
private theorem k519_2_4 : check w519 pick519 2 t10829 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w519 pick519 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10300 t10828 k519_2_0 k519_2_3
private theorem k519_2_5 : check w519 pick519 2 t10446 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k519_2_6 : check w519 pick519 2 t9794 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k519_2_7 : check w519 pick519 2 t10830 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w519 pick519 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10446 t9794 k519_2_5 k519_2_6
private theorem k519_2_8 : check w519 pick519 2 t10831 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w519 pick519 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10829 t10830 k519_2_4 k519_2_7
theorem cov519_2 : PA.Covered 2 (OZ.Valid 2 w519.low w519.t w519.y w519.r w519.cap) (P33.root 2) :=
  Night6836Tree.sound w519 pick519 2 t10831 _ k519_2_8
theorem cov519_3 : PA.Covered 3 (OZ.Valid 3 w519.low w519.t w519.y w519.r w519.cap) (P33.root 3) :=
  Night6836Tree.sound w519 pick519 3 t564 _ (by decide +kernel)
theorem cov519_4 : PA.Covered 4 (OZ.Valid 4 w519.low w519.t w519.y w519.r w519.cap) (P33.root 4) :=
  Night6836Tree.sound w519 pick519 4 t565 _ (by decide +kernel)
theorem cov519_5 : PA.Covered 5 (OZ.Valid 5 w519.low w519.t w519.y w519.r w519.cap) (P33.root 5) :=
  Night6836Tree.sound w519 pick519 5 t566 _ (by decide +kernel)
theorem cov519_6 : PA.Covered 6 (OZ.Valid 6 w519.low w519.t w519.y w519.r w519.cap) (P33.root 6) :=
  Night6836Tree.sound w519 pick519 6 t567 _ (by decide +kernel)
theorem cov519_7 : PA.Covered 7 (OZ.Valid 7 w519.low w519.t w519.y w519.r w519.cap) (P33.root 7) :=
  Night6836Tree.sound w519 pick519 7 t2134 _ (by decide +kernel)
theorem window519 : P33.WindowCount w519 := by
  apply P33.window_count w519 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov519_1
  · exact cov519_2
  · exact cov519_3
  · exact cov519_4
  · exact cov519_5
  · exact cov519_6
  · exact cov519_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w520 : P33.Window := ⟨8,57,5432,5065,245476506957593488,55903,30000,5000000,81920000000⟩
def h520_0 : Height w520 := ⟨55903,30000,by decide +kernel⟩
def h520_1 : Height w520 := ⟨60300,27000,by decide +kernel⟩
def h520_2 : Height w520 := ⟨65768,24000,by decide +kernel⟩
def h520_3 : Height w520 := ⟨73034,21000,by decide +kernel⟩
def h520_4 : Height w520 := ⟨83672,18000,by decide +kernel⟩
def pick520 (cl : ℕ) : Height w520 := if cl<25 then (if cl<5 then (h520_0) else (h520_1)) else (if cl<107 then (h520_2) else (if cl<853 then (h520_3) else (h520_4)))
private theorem k520_1_0 : check w520 pick520 1 t10535 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k520_1_1 : check w520 pick520 1 t10552 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k520_1_2 : check w520 pick520 1 t10553 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w520 pick520 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10535 t10552 k520_1_0 k520_1_1
private theorem k520_1_3 : check w520 pick520 1 t10566 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k520_1_4 : check w520 pick520 1 t10572 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k520_1_5 : check w520 pick520 1 t10573 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w520 pick520 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t10566 t10572 k520_1_3 k520_1_4
private theorem k520_1_6 : check w520 pick520 1 t10574 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w520 pick520 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t10553 t10573 k520_1_2 k520_1_5
private theorem k520_1_7 : check w520 pick520 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k520_1_8 : check w520 pick520 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k520_1_9 : check w520 pick520 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w520 pick520 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k520_1_7 k520_1_8
private theorem k520_1_10 : check w520 pick520 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k520_1_11 : check w520 pick520 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k520_1_12 : check w520 pick520 1 t10502 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w520 pick520 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10064 k520_1_10 k520_1_11
private theorem k520_1_13 : check w520 pick520 1 t10503 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w520 pick520 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t10502 k520_1_9 k520_1_12
private theorem k520_1_14 : check w520 pick520 1 t10575 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w520 pick520 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10574 t10503 k520_1_6 k520_1_13
theorem cov520_1 : PA.Covered 1 (OZ.Valid 1 w520.low w520.t w520.y w520.r w520.cap) (P33.root 1) :=
  Night6836Tree.sound w520 pick520 1 t10575 _ k520_1_14
private theorem k520_2_0 : check w520 pick520 2 t10300 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k520_2_1 : check w520 pick520 2 t10312 ⟨2,7,4,16,2,52,71,84⟩ = true := by decide +kernel
private theorem k520_2_2 : check w520 pick520 2 t10838 ⟨2,7,4,16,2,52,85,111⟩ = true := by decide +kernel
private theorem k520_2_3 : check w520 pick520 2 t10839 ⟨2,7,4,16,2,52,71,111⟩ = true := glue w520 pick520 2 ⟨2,7,4,16,2,52,71,111⟩ 3 84 t10312 t10838 k520_2_1 k520_2_2
private theorem k520_2_4 : check w520 pick520 2 t10840 ⟨2,7,4,16,2,52,2,111⟩ = true := glue w520 pick520 2 ⟨2,7,4,16,2,52,2,111⟩ 3 70 t10300 t10839 k520_2_0 k520_2_3
private theorem k520_2_5 : check w520 pick520 2 t10843 ⟨2,7,4,16,2,52,112,220⟩ = true := by decide +kernel
private theorem k520_2_6 : check w520 pick520 2 t4902 ⟨2,7,4,16,2,52,221,450⟩ = true := by decide +kernel
private theorem k520_2_7 : check w520 pick520 2 t10844 ⟨2,7,4,16,2,52,112,450⟩ = true := glue w520 pick520 2 ⟨2,7,4,16,2,52,112,450⟩ 3 220 t10843 t4902 k520_2_5 k520_2_6
private theorem k520_2_8 : check w520 pick520 2 t10845 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w520 pick520 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10840 t10844 k520_2_4 k520_2_7
theorem cov520_2 : PA.Covered 2 (OZ.Valid 2 w520.low w520.t w520.y w520.r w520.cap) (P33.root 2) :=
  Night6836Tree.sound w520 pick520 2 t10845 _ k520_2_8
theorem cov520_3 : PA.Covered 3 (OZ.Valid 3 w520.low w520.t w520.y w520.r w520.cap) (P33.root 3) :=
  Night6836Tree.sound w520 pick520 3 t564 _ (by decide +kernel)
theorem cov520_4 : PA.Covered 4 (OZ.Valid 4 w520.low w520.t w520.y w520.r w520.cap) (P33.root 4) :=
  Night6836Tree.sound w520 pick520 4 t565 _ (by decide +kernel)
theorem cov520_5 : PA.Covered 5 (OZ.Valid 5 w520.low w520.t w520.y w520.r w520.cap) (P33.root 5) :=
  Night6836Tree.sound w520 pick520 5 t566 _ (by decide +kernel)
theorem cov520_6 : PA.Covered 6 (OZ.Valid 6 w520.low w520.t w520.y w520.r w520.cap) (P33.root 6) :=
  Night6836Tree.sound w520 pick520 6 t567 _ (by decide +kernel)
theorem cov520_7 : PA.Covered 7 (OZ.Valid 7 w520.low w520.t w520.y w520.r w520.cap) (P33.root 7) :=
  Night6836Tree.sound w520 pick520 7 t2134 _ (by decide +kernel)
theorem window520 : P33.WindowCount w520 := by
  apply P33.window_count w520 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov520_1
  · exact cov520_2
  · exact cov520_3
  · exact cov520_4
  · exact cov520_5
  · exact cov520_6
  · exact cov520_7
def w521 : P33.Window := ⟨8,58,5064,4681,244190604245831120,61205,33000,5000000,81920000000⟩
def h521_0 : Height w521 := ⟨61205,33000,by decide +kernel⟩
def h521_1 : Height w521 := ⟨65483,30000,by decide +kernel⟩
def h521_2 : Height w521 := ⟨70657,27000,by decide +kernel⟩
def h521_3 : Height w521 := ⟨77243,24000,by decide +kernel⟩
def h521_4 : Height w521 := ⟨86244,21000,by decide +kernel⟩
def h521_5 : Height w521 := ⟨99909,18000,by decide +kernel⟩
def pick521 (cl : ℕ) : Height w521 := if cl<62 then (if cl<4 then (h521_0) else (if cl<18 then (h521_1) else (h521_2))) else (if cl<281 then (h521_3) else (if cl<989 then (h521_4) else (h521_5)))
private theorem k521_1_0 : check w521 pick521 1 t10535 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k521_1_1 : check w521 pick521 1 t10552 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k521_1_2 : check w521 pick521 1 t10553 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w521 pick521 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t10535 t10552 k521_1_0 k521_1_1
private theorem k521_1_3 : check w521 pick521 1 t10566 ⟨1,7,2,16,1,52,77,104⟩ = true := by decide +kernel
private theorem k521_1_4 : check w521 pick521 1 t10572 ⟨1,7,2,16,1,52,105,138⟩ = true := by decide +kernel
private theorem k521_1_5 : check w521 pick521 1 t10573 ⟨1,7,2,16,1,52,77,138⟩ = true := glue w521 pick521 1 ⟨1,7,2,16,1,52,77,138⟩ 3 104 t10566 t10572 k521_1_3 k521_1_4
private theorem k521_1_6 : check w521 pick521 1 t10574 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w521 pick521 1 ⟨1,7,2,16,1,52,1,138⟩ 3 76 t10553 t10573 k521_1_2 k521_1_5
private theorem k521_1_7 : check w521 pick521 1 t2257 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k521_1_8 : check w521 pick521 1 t736 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k521_1_9 : check w521 pick521 1 t2258 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w521 pick521 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2257 t736 k521_1_7 k521_1_8
private theorem k521_1_10 : check w521 pick521 1 t760 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k521_1_11 : check w521 pick521 1 t10064 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k521_1_12 : check w521 pick521 1 t10502 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w521 pick521 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t760 t10064 k521_1_10 k521_1_11
private theorem k521_1_13 : check w521 pick521 1 t10503 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w521 pick521 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2258 t10502 k521_1_9 k521_1_12
private theorem k521_1_14 : check w521 pick521 1 t10575 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w521 pick521 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10574 t10503 k521_1_6 k521_1_13
theorem cov521_1 : PA.Covered 1 (OZ.Valid 1 w521.low w521.t w521.y w521.r w521.cap) (P33.root 1) :=
  Night6836Tree.sound w521 pick521 1 t10575 _ k521_1_14
private theorem k521_2_0 : check w521 pick521 2 t10108 ⟨2,7,4,16,2,52,2,70⟩ = true := by decide +kernel
private theorem k521_2_1 : check w521 pick521 2 t10149 ⟨2,7,4,16,2,52,71,91⟩ = true := by decide +kernel
private theorem k521_2_2 : check w521 pick521 2 t10150 ⟨2,7,4,16,2,52,2,91⟩ = true := glue w521 pick521 2 ⟨2,7,4,16,2,52,2,91⟩ 3 70 t10108 t10149 k521_2_0 k521_2_1
private theorem k521_2_3 : check w521 pick521 2 t10507 ⟨2,7,4,16,2,52,92,450⟩ = true := by decide +kernel
private theorem k521_2_4 : check w521 pick521 2 t10508 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w521 pick521 2 ⟨2,7,4,16,0,52,0,450⟩ 3 91 t10150 t10507 k521_2_2 k521_2_3
theorem cov521_2 : PA.Covered 2 (OZ.Valid 2 w521.low w521.t w521.y w521.r w521.cap) (P33.root 2) :=
  Night6836Tree.sound w521 pick521 2 t10508 _ k521_2_4
theorem cov521_3 : PA.Covered 3 (OZ.Valid 3 w521.low w521.t w521.y w521.r w521.cap) (P33.root 3) :=
  Night6836Tree.sound w521 pick521 3 t564 _ (by decide +kernel)
theorem cov521_4 : PA.Covered 4 (OZ.Valid 4 w521.low w521.t w521.y w521.r w521.cap) (P33.root 4) :=
  Night6836Tree.sound w521 pick521 4 t565 _ (by decide +kernel)
theorem cov521_5 : PA.Covered 5 (OZ.Valid 5 w521.low w521.t w521.y w521.r w521.cap) (P33.root 5) :=
  Night6836Tree.sound w521 pick521 5 t566 _ (by decide +kernel)
theorem cov521_6 : PA.Covered 6 (OZ.Valid 6 w521.low w521.t w521.y w521.r w521.cap) (P33.root 6) :=
  Night6836Tree.sound w521 pick521 6 t567 _ (by decide +kernel)
theorem cov521_7 : PA.Covered 7 (OZ.Valid 7 w521.low w521.t w521.y w521.r w521.cap) (P33.root 7) :=
  Night6836Tree.sound w521 pick521 7 t2134 _ (by decide +kernel)
theorem window521 : P33.WindowCount w521 := by
  apply P33.window_count w521 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov521_1
  · exact cov521_2
  · exact cov521_3
  · exact cov521_4
  · exact cov521_5
  · exact cov521_6
  · exact cov521_7
def w522 : P33.Window := ⟨8,59,4680,4283,245100848573538651,68535,36000,5000000,81920000000⟩
def h522_0 : Height w522 := ⟨68535,36000,by decide +kernel⟩
def h522_1 : Height w522 := ⟨72842,33000,by decide +kernel⟩
def h522_2 : Height w522 := ⟨77957,30000,by decide +kernel⟩
def h522_3 : Height w522 := ⟨84286,27000,by decide +kernel⟩
def h522_4 : Height w522 := ⟨92564,24000,by decide +kernel⟩
def h522_5 : Height w522 := ⟨104262,21000,by decide +kernel⟩
def pick522 (cl : ℕ) : Height w522 := if cl<49 then (if cl<4 then (h522_0) else (if cl<16 then (h522_1) else (h522_2))) else (if cl<211 then (h522_3) else (if cl<925 then (h522_4) else (h522_5)))
private theorem k522_1_0 : check w522 pick522 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k522_1_1 : check w522 pick522 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k522_1_2 : check w522 pick522 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w522 pick522 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k522_1_0 k522_1_1
private theorem k522_1_3 : check w522 pick522 1 t9997 ⟨1,7,2,16,1,52,84,110⟩ = true := by decide +kernel
private theorem k522_1_4 : check w522 pick522 1 t10848 ⟨1,7,2,16,1,52,111,145⟩ = true := by decide +kernel
private theorem k522_1_5 : check w522 pick522 1 t10849 ⟨1,7,2,16,1,52,84,145⟩ = true := glue w522 pick522 1 ⟨1,7,2,16,1,52,84,145⟩ 3 110 t9997 t10848 k522_1_3 k522_1_4
private theorem k522_1_6 : check w522 pick522 1 t10850 ⟨1,7,2,16,1,52,1,145⟩ = true := glue w522 pick522 1 ⟨1,7,2,16,1,52,1,145⟩ 3 83 t10041 t10849 k522_1_2 k522_1_5
private theorem k522_1_7 : check w522 pick522 1 t2373 ⟨1,7,2,16,1,52,146,179⟩ = true := by decide +kernel
private theorem k522_1_8 : check w522 pick522 1 t2374 ⟨1,7,2,16,1,52,180,206⟩ = true := by decide +kernel
private theorem k522_1_9 : check w522 pick522 1 t2375 ⟨1,7,2,16,1,52,146,206⟩ = true := glue w522 pick522 1 ⟨1,7,2,16,1,52,146,206⟩ 3 179 t2373 t2374 k522_1_7 k522_1_8
private theorem k522_1_10 : check w522 pick522 1 t2385 ⟨1,7,2,16,1,52,207,240⟩ = true := by decide +kernel
private theorem k522_1_11 : check w522 pick522 1 t10463 ⟨1,7,2,16,1,52,241,450⟩ = true := by decide +kernel
private theorem k522_1_12 : check w522 pick522 1 t10464 ⟨1,7,2,16,1,52,207,450⟩ = true := glue w522 pick522 1 ⟨1,7,2,16,1,52,207,450⟩ 3 240 t2385 t10463 k522_1_10 k522_1_11
private theorem k522_1_13 : check w522 pick522 1 t10851 ⟨1,7,2,16,1,52,146,450⟩ = true := glue w522 pick522 1 ⟨1,7,2,16,1,52,146,450⟩ 3 206 t2375 t10464 k522_1_9 k522_1_12
private theorem k522_1_14 : check w522 pick522 1 t10852 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w522 pick522 1 ⟨1,7,2,16,0,52,0,450⟩ 3 145 t10850 t10851 k522_1_6 k522_1_13
theorem cov522_1 : PA.Covered 1 (OZ.Valid 1 w522.low w522.t w522.y w522.r w522.cap) (P33.root 1) :=
  Night6836Tree.sound w522 pick522 1 t10852 _ k522_1_14
private theorem k522_2_0 : check w522 pick522 2 t10269 ⟨2,7,4,16,2,52,2,111⟩ = true := by decide +kernel
private theorem k522_2_1 : check w522 pick522 2 t10855 ⟨2,7,4,16,2,52,112,450⟩ = true := by decide +kernel
private theorem k522_2_2 : check w522 pick522 2 t10856 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w522 pick522 2 ⟨2,7,4,16,0,52,0,450⟩ 3 111 t10269 t10855 k522_2_0 k522_2_1
theorem cov522_2 : PA.Covered 2 (OZ.Valid 2 w522.low w522.t w522.y w522.r w522.cap) (P33.root 2) :=
  Night6836Tree.sound w522 pick522 2 t10856 _ k522_2_2
theorem cov522_3 : PA.Covered 3 (OZ.Valid 3 w522.low w522.t w522.y w522.r w522.cap) (P33.root 3) :=
  Night6836Tree.sound w522 pick522 3 t564 _ (by decide +kernel)
theorem cov522_4 : PA.Covered 4 (OZ.Valid 4 w522.low w522.t w522.y w522.r w522.cap) (P33.root 4) :=
  Night6836Tree.sound w522 pick522 4 t565 _ (by decide +kernel)
theorem cov522_5 : PA.Covered 5 (OZ.Valid 5 w522.low w522.t w522.y w522.r w522.cap) (P33.root 5) :=
  Night6836Tree.sound w522 pick522 5 t566 _ (by decide +kernel)
theorem cov522_6 : PA.Covered 6 (OZ.Valid 6 w522.low w522.t w522.y w522.r w522.cap) (P33.root 6) :=
  Night6836Tree.sound w522 pick522 6 t567 _ (by decide +kernel)
theorem cov522_7 : PA.Covered 7 (OZ.Valid 7 w522.low w522.t w522.y w522.r w522.cap) (P33.root 7) :=
  Night6836Tree.sound w522 pick522 7 t2134 _ (by decide +kernel)
theorem window522 : P33.WindowCount w522 := by
  apply P33.window_count w522 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov522_1
  · exact cov522_2
  · exact cov522_3
  · exact cov522_4
  · exact cov522_5
  · exact cov522_6
  · exact cov522_7
def w523 : P33.Window := ⟨8,60,4282,3870,241659641715282269,74787,42000,5000000,81920000000⟩
def h523_0 : Height w523 := ⟨74787,42000,by decide +kernel⟩
def h523_1 : Height w523 := ⟨78718,39000,by decide +kernel⟩
def h523_2 : Height w523 := ⟨83212,36000,by decide +kernel⟩
def h523_3 : Height w523 := ⟨88491,33000,by decide +kernel⟩
def h523_4 : Height w523 := ⟨94908,30000,by decide +kernel⟩
def h523_5 : Height w523 := ⟨103069,27000,by decide +kernel⟩
def pick523 (cl : ℕ) : Height w523 := if cl<32 then (if cl<2 then (h523_0) else (if cl<5 then (h523_1) else (h523_2))) else (if cl<55 then (h523_3) else (if cl<202 then (h523_4) else (h523_5)))
private theorem k523_1_0 : check w523 pick523 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k523_1_1 : check w523 pick523 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k523_1_2 : check w523 pick523 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w523 pick523 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k523_1_0 k523_1_1
private theorem k523_1_3 : check w523 pick523 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k523_1_4 : check w523 pick523 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w523 pick523 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k523_1_2 k523_1_3
private theorem k523_1_5 : check w523 pick523 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k523_1_6 : check w523 pick523 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k523_1_7 : check w523 pick523 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w523 pick523 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k523_1_5 k523_1_6
private theorem k523_1_8 : check w523 pick523 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k523_1_9 : check w523 pick523 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k523_1_10 : check w523 pick523 1 t10863 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w523 pick523 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10862 k523_1_8 k523_1_9
private theorem k523_1_11 : check w523 pick523 1 t10864 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w523 pick523 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10863 k523_1_7 k523_1_10
private theorem k523_1_12 : check w523 pick523 1 t10865 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w523 pick523 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10864 k523_1_4 k523_1_11
theorem cov523_1 : PA.Covered 1 (OZ.Valid 1 w523.low w523.t w523.y w523.r w523.cap) (P33.root 1) :=
  Night6836Tree.sound w523 pick523 1 t10865 _ k523_1_12
theorem cov523_2 : PA.Covered 2 (OZ.Valid 2 w523.low w523.t w523.y w523.r w523.cap) (P33.root 2) :=
  Night6836Tree.sound w523 pick523 2 t10037 _ (by decide +kernel)
theorem cov523_3 : PA.Covered 3 (OZ.Valid 3 w523.low w523.t w523.y w523.r w523.cap) (P33.root 3) :=
  Night6836Tree.sound w523 pick523 3 t564 _ (by decide +kernel)
theorem cov523_4 : PA.Covered 4 (OZ.Valid 4 w523.low w523.t w523.y w523.r w523.cap) (P33.root 4) :=
  Night6836Tree.sound w523 pick523 4 t565 _ (by decide +kernel)
theorem cov523_5 : PA.Covered 5 (OZ.Valid 5 w523.low w523.t w523.y w523.r w523.cap) (P33.root 5) :=
  Night6836Tree.sound w523 pick523 5 t566 _ (by decide +kernel)
theorem cov523_6 : PA.Covered 6 (OZ.Valid 6 w523.low w523.t w523.y w523.r w523.cap) (P33.root 6) :=
  Night6836Tree.sound w523 pick523 6 t567 _ (by decide +kernel)
theorem cov523_7 : PA.Covered 7 (OZ.Valid 7 w523.low w523.t w523.y w523.r w523.cap) (P33.root 7) :=
  Night6836Tree.sound w523 pick523 7 t2134 _ (by decide +kernel)
theorem window523 : P33.WindowCount w523 := by
  apply P33.window_count w523 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov523_1
  · exact cov523_2
  · exact cov523_3
  · exact cov523_4
  · exact cov523_5
  · exact cov523_6
  · exact cov523_7
def w524 : P33.Window := ⟨8,61,3869,3442,241077967333985452,88854,45000,5000000,81920000000⟩
def h524_0 : Height w524 := ⟨88854,45000,by decide +kernel⟩
def h524_1 : Height w524 := ⟨93144,42000,by decide +kernel⟩
def h524_2 : Height w524 := ⟨98039,39000,by decide +kernel⟩
def h524_3 : Height w524 := ⟨103758,36000,by decide +kernel⟩
def h524_4 : Height w524 := ⟨110645,33000,by decide +kernel⟩
def h524_5 : Height w524 := ⟨119258,30000,by decide +kernel⟩
def pick524 (cl : ℕ) : Height w524 := if cl<32 then (if cl<4 then (h524_0) else (if cl<13 then (h524_1) else (h524_2))) else (if cl<83 then (h524_3) else (if cl<260 then (h524_4) else (h524_5)))
private theorem k524_1_0 : check w524 pick524 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k524_1_1 : check w524 pick524 1 t10040 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k524_1_2 : check w524 pick524 1 t10041 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w524 pick524 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t10040 k524_1_0 k524_1_1
private theorem k524_1_3 : check w524 pick524 1 t10265 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k524_1_4 : check w524 pick524 1 t10266 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w524 pick524 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10041 t10265 k524_1_2 k524_1_3
private theorem k524_1_5 : check w524 pick524 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k524_1_6 : check w524 pick524 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k524_1_7 : check w524 pick524 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w524 pick524 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k524_1_5 k524_1_6
private theorem k524_1_8 : check w524 pick524 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k524_1_9 : check w524 pick524 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k524_1_10 : check w524 pick524 1 t10863 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w524 pick524 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10862 k524_1_8 k524_1_9
private theorem k524_1_11 : check w524 pick524 1 t10864 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w524 pick524 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10863 k524_1_7 k524_1_10
private theorem k524_1_12 : check w524 pick524 1 t10865 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w524 pick524 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10266 t10864 k524_1_4 k524_1_11
theorem cov524_1 : PA.Covered 1 (OZ.Valid 1 w524.low w524.t w524.y w524.r w524.cap) (P33.root 1) :=
  Night6836Tree.sound w524 pick524 1 t10865 _ k524_1_12
theorem cov524_2 : PA.Covered 2 (OZ.Valid 2 w524.low w524.t w524.y w524.r w524.cap) (P33.root 2) :=
  Night6836Tree.sound w524 pick524 2 t10216 _ (by decide +kernel)
theorem cov524_3 : PA.Covered 3 (OZ.Valid 3 w524.low w524.t w524.y w524.r w524.cap) (P33.root 3) :=
  Night6836Tree.sound w524 pick524 3 t564 _ (by decide +kernel)
theorem cov524_4 : PA.Covered 4 (OZ.Valid 4 w524.low w524.t w524.y w524.r w524.cap) (P33.root 4) :=
  Night6836Tree.sound w524 pick524 4 t565 _ (by decide +kernel)
theorem cov524_5 : PA.Covered 5 (OZ.Valid 5 w524.low w524.t w524.y w524.r w524.cap) (P33.root 5) :=
  Night6836Tree.sound w524 pick524 5 t566 _ (by decide +kernel)
theorem cov524_6 : PA.Covered 6 (OZ.Valid 6 w524.low w524.t w524.y w524.r w524.cap) (P33.root 6) :=
  Night6836Tree.sound w524 pick524 6 t567 _ (by decide +kernel)
theorem cov524_7 : PA.Covered 7 (OZ.Valid 7 w524.low w524.t w524.y w524.r w524.cap) (P33.root 7) :=
  Night6836Tree.sound w524 pick524 7 t2134 _ (by decide +kernel)
theorem window524 : P33.WindowCount w524 := by
  apply P33.window_count w524 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov524_1
  · exact cov524_2
  · exact cov524_3
  · exact cov524_4
  · exact cov524_5
  · exact cov524_6
  · exact cov524_7
def w525 : P33.Window := ⟨8,62,3441,2998,232833149077307445,101139,54000,5000000,81920000000⟩
def h525_0 : Height w525 := ⟨101139,54000,by decide +kernel⟩
def h525_1 : Height w525 := ⟨105112,51000,by decide +kernel⟩
def h525_2 : Height w525 := ⟨109509,48000,by decide +kernel⟩
def h525_3 : Height w525 := ⟨114447,45000,by decide +kernel⟩
def h525_4 : Height w525 := ⟨120096,42000,by decide +kernel⟩
def h525_5 : Height w525 := ⟨126698,39000,by decide +kernel⟩
def h525_6 : Height w525 := ⟨134626,36000,by decide +kernel⟩
def h525_7 : Height w525 := ⟨144469,33000,by decide +kernel⟩
def pick525 (cl : ℕ) : Height w525 := if cl<32 then (if cl<5 then (if cl<2 then (h525_0) else (h525_1)) else (if cl<13 then (h525_2) else (h525_3))) else (if cl<172 then (if cl<70 then (h525_4) else (h525_5)) else (if cl<418 then (h525_6) else (h525_7)))
private theorem k525_1_0 : check w525 pick525 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k525_1_1 : check w525 pick525 1 t10872 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k525_1_2 : check w525 pick525 1 t10873 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w525 pick525 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t2625 t10872 k525_1_0 k525_1_1
private theorem k525_1_3 : check w525 pick525 1 t10879 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k525_1_4 : check w525 pick525 1 t10888 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k525_1_5 : check w525 pick525 1 t10889 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w525 pick525 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10879 t10888 k525_1_3 k525_1_4
private theorem k525_1_6 : check w525 pick525 1 t10890 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w525 pick525 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10873 t10889 k525_1_2 k525_1_5
private theorem k525_1_7 : check w525 pick525 1 t10896 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k525_1_8 : check w525 pick525 1 t6586 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k525_1_9 : check w525 pick525 1 t10897 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w525 pick525 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10896 t6586 k525_1_7 k525_1_8
private theorem k525_1_10 : check w525 pick525 1 t6602 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k525_1_11 : check w525 pick525 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k525_1_12 : check w525 pick525 1 t10898 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w525 pick525 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6602 t10862 k525_1_10 k525_1_11
private theorem k525_1_13 : check w525 pick525 1 t10899 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w525 pick525 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10897 t10898 k525_1_9 k525_1_12
private theorem k525_1_14 : check w525 pick525 1 t10900 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w525 pick525 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10890 t10899 k525_1_6 k525_1_13
theorem cov525_1 : PA.Covered 1 (OZ.Valid 1 w525.low w525.t w525.y w525.r w525.cap) (P33.root 1) :=
  Night6836Tree.sound w525 pick525 1 t10900 _ k525_1_14
theorem cov525_2 : PA.Covered 2 (OZ.Valid 2 w525.low w525.t w525.y w525.r w525.cap) (P33.root 2) :=
  Night6836Tree.sound w525 pick525 2 t10908 _ (by decide +kernel)
theorem cov525_3 : PA.Covered 3 (OZ.Valid 3 w525.low w525.t w525.y w525.r w525.cap) (P33.root 3) :=
  Night6836Tree.sound w525 pick525 3 t564 _ (by decide +kernel)
theorem cov525_4 : PA.Covered 4 (OZ.Valid 4 w525.low w525.t w525.y w525.r w525.cap) (P33.root 4) :=
  Night6836Tree.sound w525 pick525 4 t565 _ (by decide +kernel)
theorem cov525_5 : PA.Covered 5 (OZ.Valid 5 w525.low w525.t w525.y w525.r w525.cap) (P33.root 5) :=
  Night6836Tree.sound w525 pick525 5 t566 _ (by decide +kernel)
theorem cov525_6 : PA.Covered 6 (OZ.Valid 6 w525.low w525.t w525.y w525.r w525.cap) (P33.root 6) :=
  Night6836Tree.sound w525 pick525 6 t567 _ (by decide +kernel)
theorem cov525_7 : PA.Covered 7 (OZ.Valid 7 w525.low w525.t w525.y w525.r w525.cap) (P33.root 7) :=
  Night6836Tree.sound w525 pick525 7 t2134 _ (by decide +kernel)
theorem window525 : P33.WindowCount w525 := by
  apply P33.window_count w525 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov525_1
  · exact cov525_2
  · exact cov525_3
  · exact cov525_4
  · exact cov525_5
  · exact cov525_6
  · exact cov525_7
def w526 : P33.Window := ⟨8,63,2997,2540,224172398339326456,122847,63000,5000000,81920000000⟩
def h526_0 : Height w526 := ⟨122847,63000,by decide +kernel⟩
def h526_1 : Height w526 := ⟨126901,60000,by decide +kernel⟩
def h526_2 : Height w526 := ⟨131321,57000,by decide +kernel⟩
def h526_3 : Height w526 := ⟨136193,54000,by decide +kernel⟩
def h526_4 : Height w526 := ⟨141630,51000,by decide +kernel⟩
def h526_5 : Height w526 := ⟨147786,48000,by decide +kernel⟩
def h526_6 : Height w526 := ⟨154877,45000,by decide +kernel⟩
def h526_7 : Height w526 := ⟨163215,42000,by decide +kernel⟩
def h526_8 : Height w526 := ⟨173269,39000,by decide +kernel⟩
def pick526 (cl : ℕ) : Height w526 := if cl<32 then (if cl<5 then (if cl<2 then (h526_0) else (h526_1)) else (if cl<13 then (h526_2) else (h526_3))) else (if cl<100 then (if cl<43 then (h526_4) else (h526_5)) else (if cl<216 then (h526_6) else (if cl<507 then (h526_7) else (h526_8))))
private theorem k526_1_0 : check w526 pick526 1 t5236 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k526_1_1 : check w526 pick526 1 t10911 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k526_1_2 : check w526 pick526 1 t10912 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w526 pick526 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5236 t10911 k526_1_0 k526_1_1
private theorem k526_1_3 : check w526 pick526 1 t10879 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k526_1_4 : check w526 pick526 1 t10888 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k526_1_5 : check w526 pick526 1 t10889 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w526 pick526 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10879 t10888 k526_1_3 k526_1_4
private theorem k526_1_6 : check w526 pick526 1 t10913 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w526 pick526 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10912 t10889 k526_1_2 k526_1_5
private theorem k526_1_7 : check w526 pick526 1 t10896 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k526_1_8 : check w526 pick526 1 t6586 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k526_1_9 : check w526 pick526 1 t10897 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w526 pick526 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10896 t6586 k526_1_7 k526_1_8
private theorem k526_1_10 : check w526 pick526 1 t6602 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k526_1_11 : check w526 pick526 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k526_1_12 : check w526 pick526 1 t10898 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w526 pick526 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6602 t10862 k526_1_10 k526_1_11
private theorem k526_1_13 : check w526 pick526 1 t10899 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w526 pick526 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10897 t10898 k526_1_9 k526_1_12
private theorem k526_1_14 : check w526 pick526 1 t10914 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w526 pick526 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10913 t10899 k526_1_6 k526_1_13
theorem cov526_1 : PA.Covered 1 (OZ.Valid 1 w526.low w526.t w526.y w526.r w526.cap) (P33.root 1) :=
  Night6836Tree.sound w526 pick526 1 t10914 _ k526_1_14
theorem cov526_2 : PA.Covered 2 (OZ.Valid 2 w526.low w526.t w526.y w526.r w526.cap) (P33.root 2) :=
  Night6836Tree.sound w526 pick526 2 t10908 _ (by decide +kernel)
theorem cov526_3 : PA.Covered 3 (OZ.Valid 3 w526.low w526.t w526.y w526.r w526.cap) (P33.root 3) :=
  Night6836Tree.sound w526 pick526 3 t564 _ (by decide +kernel)
theorem cov526_4 : PA.Covered 4 (OZ.Valid 4 w526.low w526.t w526.y w526.r w526.cap) (P33.root 4) :=
  Night6836Tree.sound w526 pick526 4 t565 _ (by decide +kernel)
theorem cov526_5 : PA.Covered 5 (OZ.Valid 5 w526.low w526.t w526.y w526.r w526.cap) (P33.root 5) :=
  Night6836Tree.sound w526 pick526 5 t566 _ (by decide +kernel)
theorem cov526_6 : PA.Covered 6 (OZ.Valid 6 w526.low w526.t w526.y w526.r w526.cap) (P33.root 6) :=
  Night6836Tree.sound w526 pick526 6 t567 _ (by decide +kernel)
theorem cov526_7 : PA.Covered 7 (OZ.Valid 7 w526.low w526.t w526.y w526.r w526.cap) (P33.root 7) :=
  Night6836Tree.sound w526 pick526 7 t2134 _ (by decide +kernel)
theorem window526 : P33.WindowCount w526 := by
  apply P33.window_count w526 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov526_1
  · exact cov526_2
  · exact cov526_3
  · exact cov526_4
  · exact cov526_5
  · exact cov526_6
  · exact cov526_7
def w527 : P33.Window := ⟨8,64,2539,2123,205255951987229318,150460,75000,5000000,81920000000⟩
def h527_0 : Height w527 := ⟨150460,75000,by decide +kernel⟩
def h527_1 : Height w527 := ⟨154548,72000,by decide +kernel⟩
def h527_2 : Height w527 := ⟨158942,69000,by decide +kernel⟩
def h527_3 : Height w527 := ⟨163697,66000,by decide +kernel⟩
def h527_4 : Height w527 := ⟨174602,60000,by decide +kernel⟩
def h527_5 : Height w527 := ⟨180966,57000,by decide +kernel⟩
def h527_6 : Height w527 := ⟨188140,54000,by decide +kernel⟩
def h527_7 : Height w527 := ⟨196342,51000,by decide +kernel⟩
def h527_8 : Height w527 := ⟨205880,48000,by decide +kernel⟩
def pick527 (cl : ℕ) : Height w527 := if cl<32 then (if cl<5 then (if cl<2 then (h527_0) else (h527_1)) else (if cl<10 then (h527_2) else (h527_3))) else (if cl<105 then (if cl<51 then (h527_4) else (h527_5)) else (if cl<213 then (h527_6) else (if cl<328 then (h527_7) else (h527_8))))
private theorem k527_1_0 : check w527 pick527 1 t5236 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k527_1_1 : check w527 pick527 1 t10920 ⟨1,7,2,16,1,52,50,76⟩ = true := by decide +kernel
private theorem k527_1_2 : check w527 pick527 1 t10921 ⟨1,7,2,16,1,52,1,76⟩ = true := glue w527 pick527 1 ⟨1,7,2,16,1,52,1,76⟩ 3 49 t5236 t10920 k527_1_0 k527_1_1
private theorem k527_1_3 : check w527 pick527 1 t10879 ⟨1,7,2,16,1,20,77,131⟩ = true := by decide +kernel
private theorem k527_1_4 : check w527 pick527 1 t10940 ⟨1,7,2,16,21,52,77,131⟩ = true := by decide +kernel
private theorem k527_1_5 : check w527 pick527 1 t10941 ⟨1,7,2,16,1,52,77,131⟩ = true := glue w527 pick527 1 ⟨1,7,2,16,1,52,77,131⟩ 2 20 t10879 t10940 k527_1_3 k527_1_4
private theorem k527_1_6 : check w527 pick527 1 t10942 ⟨1,7,2,16,1,52,1,131⟩ = true := glue w527 pick527 1 ⟨1,7,2,16,1,52,1,131⟩ 3 76 t10921 t10941 k527_1_2 k527_1_5
private theorem k527_1_7 : check w527 pick527 1 t10896 ⟨1,7,2,16,1,52,132,165⟩ = true := by decide +kernel
private theorem k527_1_8 : check w527 pick527 1 t6586 ⟨1,7,2,16,1,52,166,192⟩ = true := by decide +kernel
private theorem k527_1_9 : check w527 pick527 1 t10897 ⟨1,7,2,16,1,52,132,192⟩ = true := glue w527 pick527 1 ⟨1,7,2,16,1,52,132,192⟩ 3 165 t10896 t6586 k527_1_7 k527_1_8
private theorem k527_1_10 : check w527 pick527 1 t6602 ⟨1,7,2,16,1,52,193,233⟩ = true := by decide +kernel
private theorem k527_1_11 : check w527 pick527 1 t10862 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k527_1_12 : check w527 pick527 1 t10898 ⟨1,7,2,16,1,52,193,450⟩ = true := glue w527 pick527 1 ⟨1,7,2,16,1,52,193,450⟩ 3 233 t6602 t10862 k527_1_10 k527_1_11
private theorem k527_1_13 : check w527 pick527 1 t10899 ⟨1,7,2,16,1,52,132,450⟩ = true := glue w527 pick527 1 ⟨1,7,2,16,1,52,132,450⟩ 3 192 t10897 t10898 k527_1_9 k527_1_12
private theorem k527_1_14 : check w527 pick527 1 t10943 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w527 pick527 1 ⟨1,7,2,16,0,52,0,450⟩ 3 131 t10942 t10899 k527_1_6 k527_1_13
theorem cov527_1 : PA.Covered 1 (OZ.Valid 1 w527.low w527.t w527.y w527.r w527.cap) (P33.root 1) :=
  Night6836Tree.sound w527 pick527 1 t10943 _ k527_1_14
theorem cov527_2 : PA.Covered 2 (OZ.Valid 2 w527.low w527.t w527.y w527.r w527.cap) (P33.root 2) :=
  Night6836Tree.sound w527 pick527 2 t10908 _ (by decide +kernel)
theorem cov527_3 : PA.Covered 3 (OZ.Valid 3 w527.low w527.t w527.y w527.r w527.cap) (P33.root 3) :=
  Night6836Tree.sound w527 pick527 3 t564 _ (by decide +kernel)
theorem cov527_4 : PA.Covered 4 (OZ.Valid 4 w527.low w527.t w527.y w527.r w527.cap) (P33.root 4) :=
  Night6836Tree.sound w527 pick527 4 t565 _ (by decide +kernel)
theorem cov527_5 : PA.Covered 5 (OZ.Valid 5 w527.low w527.t w527.y w527.r w527.cap) (P33.root 5) :=
  Night6836Tree.sound w527 pick527 5 t566 _ (by decide +kernel)
theorem cov527_6 : PA.Covered 6 (OZ.Valid 6 w527.low w527.t w527.y w527.r w527.cap) (P33.root 6) :=
  Night6836Tree.sound w527 pick527 6 t567 _ (by decide +kernel)
theorem cov527_7 : PA.Covered 7 (OZ.Valid 7 w527.low w527.t w527.y w527.r w527.cap) (P33.root 7) :=
  Night6836Tree.sound w527 pick527 7 t2134 _ (by decide +kernel)
theorem window527 : P33.WindowCount w527 := by
  apply P33.window_count w527 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov527_1
  · exact cov527_2
  · exact cov527_3
  · exact cov527_4
  · exact cov527_5
  · exact cov527_6
  · exact cov527_7
def w528 : P33.Window := ⟨9,20,7959,7926,218577154401523262,8230,15000,5000000,81920000000⟩
def h528_0 : Height w528 := ⟨8230,15000,by decide +kernel⟩
def h528_1 : Height w528 := ⟨12545,12000,by decide +kernel⟩
def h528_2 : Height w528 := ⟨21906,9000,by decide +kernel⟩
def pick528 (cl : ℕ) : Height w528 := if cl<4 then (h528_0) else (if cl<302 then (h528_1) else (h528_2))
private theorem k528_1_0 : check w528 pick528 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k528_1_1 : check w528 pick528 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k528_1_2 : check w528 pick528 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w528 pick528 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k528_1_0 k528_1_1
private theorem k528_1_3 : check w528 pick528 1 t10947 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k528_1_4 : check w528 pick528 1 t10948 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w528 pick528 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10947 k528_1_2 k528_1_3
private theorem k528_1_5 : check w528 pick528 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k528_1_6 : check w528 pick528 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k528_1_7 : check w528 pick528 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w528 pick528 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k528_1_5 k528_1_6
private theorem k528_1_8 : check w528 pick528 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k528_1_9 : check w528 pick528 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k528_1_10 : check w528 pick528 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w528 pick528 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k528_1_8 k528_1_9
private theorem k528_1_11 : check w528 pick528 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w528 pick528 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k528_1_7 k528_1_10
private theorem k528_1_12 : check w528 pick528 1 t10949 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w528 pick528 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10948 t10007 k528_1_4 k528_1_11
theorem cov528_1 : PA.Covered 1 (OZ.Valid 1 w528.low w528.t w528.y w528.r w528.cap) (P33.root 1) :=
  Night6836Tree.sound w528 pick528 1 t10949 _ k528_1_12
theorem cov528_2 : PA.Covered 2 (OZ.Valid 2 w528.low w528.t w528.y w528.r w528.cap) (P33.root 2) :=
  Night6836Tree.sound w528 pick528 2 t2745 _ (by decide +kernel)
theorem cov528_3 : PA.Covered 3 (OZ.Valid 3 w528.low w528.t w528.y w528.r w528.cap) (P33.root 3) :=
  Night6836Tree.sound w528 pick528 3 t564 _ (by decide +kernel)
theorem cov528_4 : PA.Covered 4 (OZ.Valid 4 w528.low w528.t w528.y w528.r w528.cap) (P33.root 4) :=
  Night6836Tree.sound w528 pick528 4 t565 _ (by decide +kernel)
theorem cov528_5 : PA.Covered 5 (OZ.Valid 5 w528.low w528.t w528.y w528.r w528.cap) (P33.root 5) :=
  Night6836Tree.sound w528 pick528 5 t566 _ (by decide +kernel)
theorem cov528_6 : PA.Covered 6 (OZ.Valid 6 w528.low w528.t w528.y w528.r w528.cap) (P33.root 6) :=
  Night6836Tree.sound w528 pick528 6 t567 _ (by decide +kernel)
theorem cov528_7 : PA.Covered 7 (OZ.Valid 7 w528.low w528.t w528.y w528.r w528.cap) (P33.root 7) :=
  Night6836Tree.sound w528 pick528 7 t568 _ (by decide +kernel)
theorem window528 : P33.WindowCount w528 := by
  apply P33.window_count w528 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov528_1
  · exact cov528_2
  · exact cov528_3
  · exact cov528_4
  · exact cov528_5
  · exact cov528_6
  · exact cov528_7
def w529 : P33.Window := ⟨9,21,7925,7891,222230501678836021,9363,15000,5000000,81920000000⟩
def h529_0 : Height w529 := ⟨9363,15000,by decide +kernel⟩
def h529_1 : Height w529 := ⟨13906,12000,by decide +kernel⟩
def h529_2 : Height w529 := ⟨23939,9000,by decide +kernel⟩
def pick529 (cl : ℕ) : Height w529 := if cl<6 then (h529_0) else (if cl<494 then (h529_1) else (h529_2))
private theorem k529_1_0 : check w529 pick529 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k529_1_1 : check w529 pick529 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k529_1_2 : check w529 pick529 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w529 pick529 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k529_1_0 k529_1_1
private theorem k529_1_3 : check w529 pick529 1 t10952 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k529_1_4 : check w529 pick529 1 t10953 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w529 pick529 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10952 k529_1_2 k529_1_3
private theorem k529_1_5 : check w529 pick529 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k529_1_6 : check w529 pick529 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k529_1_7 : check w529 pick529 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w529 pick529 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k529_1_5 k529_1_6
private theorem k529_1_8 : check w529 pick529 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k529_1_9 : check w529 pick529 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k529_1_10 : check w529 pick529 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w529 pick529 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k529_1_8 k529_1_9
private theorem k529_1_11 : check w529 pick529 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w529 pick529 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k529_1_7 k529_1_10
private theorem k529_1_12 : check w529 pick529 1 t10954 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w529 pick529 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10953 t10007 k529_1_4 k529_1_11
theorem cov529_1 : PA.Covered 1 (OZ.Valid 1 w529.low w529.t w529.y w529.r w529.cap) (P33.root 1) :=
  Night6836Tree.sound w529 pick529 1 t10954 _ k529_1_12
theorem cov529_2 : PA.Covered 2 (OZ.Valid 2 w529.low w529.t w529.y w529.r w529.cap) (P33.root 2) :=
  Night6836Tree.sound w529 pick529 2 t2745 _ (by decide +kernel)
theorem cov529_3 : PA.Covered 3 (OZ.Valid 3 w529.low w529.t w529.y w529.r w529.cap) (P33.root 3) :=
  Night6836Tree.sound w529 pick529 3 t564 _ (by decide +kernel)
theorem cov529_4 : PA.Covered 4 (OZ.Valid 4 w529.low w529.t w529.y w529.r w529.cap) (P33.root 4) :=
  Night6836Tree.sound w529 pick529 4 t565 _ (by decide +kernel)
theorem cov529_5 : PA.Covered 5 (OZ.Valid 5 w529.low w529.t w529.y w529.r w529.cap) (P33.root 5) :=
  Night6836Tree.sound w529 pick529 5 t566 _ (by decide +kernel)
theorem cov529_6 : PA.Covered 6 (OZ.Valid 6 w529.low w529.t w529.y w529.r w529.cap) (P33.root 6) :=
  Night6836Tree.sound w529 pick529 6 t567 _ (by decide +kernel)
theorem cov529_7 : PA.Covered 7 (OZ.Valid 7 w529.low w529.t w529.y w529.r w529.cap) (P33.root 7) :=
  Night6836Tree.sound w529 pick529 7 t568 _ (by decide +kernel)
theorem window529 : P33.WindowCount w529 := by
  apply P33.window_count w529 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov529_1
  · exact cov529_2
  · exact cov529_3
  · exact cov529_4
  · exact cov529_5
  · exact cov529_6
  · exact cov529_7
end ProximityPrize.SubmissionLower.Night6836Bank

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Bank
open Night6836Tree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def w530 : P33.Window := ⟨9,22,7890,7857,225815184099207370,10509,15000,5000000,81920000000⟩
def h530_0 : Height w530 := ⟨10509,15000,by decide +kernel⟩
def h530_1 : Height w530 := ⟨15285,12000,by decide +kernel⟩
def h530_2 : Height w530 := ⟨26009,9000,by decide +kernel⟩
def pick530 (cl : ℕ) : Height w530 := if cl<10 then (h530_0) else (if cl<925 then (h530_1) else (h530_2))
private theorem k530_1_0 : check w530 pick530 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k530_1_1 : check w530 pick530 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k530_1_2 : check w530 pick530 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w530 pick530 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k530_1_0 k530_1_1
private theorem k530_1_3 : check w530 pick530 1 t9998 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k530_1_4 : check w530 pick530 1 t9999 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w530 pick530 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t9998 k530_1_2 k530_1_3
private theorem k530_1_5 : check w530 pick530 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k530_1_6 : check w530 pick530 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k530_1_7 : check w530 pick530 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w530 pick530 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k530_1_5 k530_1_6
private theorem k530_1_8 : check w530 pick530 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k530_1_9 : check w530 pick530 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k530_1_10 : check w530 pick530 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w530 pick530 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k530_1_8 k530_1_9
private theorem k530_1_11 : check w530 pick530 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w530 pick530 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k530_1_7 k530_1_10
private theorem k530_1_12 : check w530 pick530 1 t10008 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w530 pick530 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t9999 t10007 k530_1_4 k530_1_11
theorem cov530_1 : PA.Covered 1 (OZ.Valid 1 w530.low w530.t w530.y w530.r w530.cap) (P33.root 1) :=
  Night6836Tree.sound w530 pick530 1 t10008 _ k530_1_12
theorem cov530_2 : PA.Covered 2 (OZ.Valid 2 w530.low w530.t w530.y w530.r w530.cap) (P33.root 2) :=
  Night6836Tree.sound w530 pick530 2 t2745 _ (by decide +kernel)
theorem cov530_3 : PA.Covered 3 (OZ.Valid 3 w530.low w530.t w530.y w530.r w530.cap) (P33.root 3) :=
  Night6836Tree.sound w530 pick530 3 t564 _ (by decide +kernel)
theorem cov530_4 : PA.Covered 4 (OZ.Valid 4 w530.low w530.t w530.y w530.r w530.cap) (P33.root 4) :=
  Night6836Tree.sound w530 pick530 4 t565 _ (by decide +kernel)
theorem cov530_5 : PA.Covered 5 (OZ.Valid 5 w530.low w530.t w530.y w530.r w530.cap) (P33.root 5) :=
  Night6836Tree.sound w530 pick530 5 t566 _ (by decide +kernel)
theorem cov530_6 : PA.Covered 6 (OZ.Valid 6 w530.low w530.t w530.y w530.r w530.cap) (P33.root 6) :=
  Night6836Tree.sound w530 pick530 6 t567 _ (by decide +kernel)
theorem cov530_7 : PA.Covered 7 (OZ.Valid 7 w530.low w530.t w530.y w530.r w530.cap) (P33.root 7) :=
  Night6836Tree.sound w530 pick530 7 t568 _ (by decide +kernel)
theorem window530 : P33.WindowCount w530 := by
  apply P33.window_count w530 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov530_1
  · exact cov530_2
  · exact cov530_3
  · exact cov530_4
  · exact cov530_5
  · exact cov530_6
  · exact cov530_7
def w531 : P33.Window := ⟨9,23,6822,5823,199190616857317631,17256,19000,5000000,81920000000⟩
def h531_0 : Height w531 := ⟨17256,19000,by decide +kernel⟩
def h531_1 : Height w531 := ⟨25200,15000,by decide +kernel⟩
def pick531 (cl : ℕ) : Height w531 := if cl<36 then (h531_0) else (h531_1)
private theorem k531_1_0 : check w531 pick531 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k531_1_1 : check w531 pick531 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k531_1_2 : check w531 pick531 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w531 pick531 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k531_1_0 k531_1_1
private theorem k531_1_3 : check w531 pick531 1 t10955 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k531_1_4 : check w531 pick531 1 t10956 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w531 pick531 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10955 k531_1_2 k531_1_3
private theorem k531_1_5 : check w531 pick531 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k531_1_6 : check w531 pick531 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k531_1_7 : check w531 pick531 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w531 pick531 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k531_1_5 k531_1_6
private theorem k531_1_8 : check w531 pick531 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k531_1_9 : check w531 pick531 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k531_1_10 : check w531 pick531 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w531 pick531 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k531_1_8 k531_1_9
private theorem k531_1_11 : check w531 pick531 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w531 pick531 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k531_1_7 k531_1_10
private theorem k531_1_12 : check w531 pick531 1 t10957 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w531 pick531 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10956 t10007 k531_1_4 k531_1_11
theorem cov531_1 : PA.Covered 1 (OZ.Valid 1 w531.low w531.t w531.y w531.r w531.cap) (P33.root 1) :=
  Night6836Tree.sound w531 pick531 1 t10957 _ k531_1_12
theorem cov531_2 : PA.Covered 2 (OZ.Valid 2 w531.low w531.t w531.y w531.r w531.cap) (P33.root 2) :=
  Night6836Tree.sound w531 pick531 2 t2745 _ (by decide +kernel)
theorem cov531_3 : PA.Covered 3 (OZ.Valid 3 w531.low w531.t w531.y w531.r w531.cap) (P33.root 3) :=
  Night6836Tree.sound w531 pick531 3 t564 _ (by decide +kernel)
theorem cov531_4 : PA.Covered 4 (OZ.Valid 4 w531.low w531.t w531.y w531.r w531.cap) (P33.root 4) :=
  Night6836Tree.sound w531 pick531 4 t565 _ (by decide +kernel)
theorem cov531_5 : PA.Covered 5 (OZ.Valid 5 w531.low w531.t w531.y w531.r w531.cap) (P33.root 5) :=
  Night6836Tree.sound w531 pick531 5 t566 _ (by decide +kernel)
theorem cov531_6 : PA.Covered 6 (OZ.Valid 6 w531.low w531.t w531.y w531.r w531.cap) (P33.root 6) :=
  Night6836Tree.sound w531 pick531 6 t567 _ (by decide +kernel)
theorem cov531_7 : PA.Covered 7 (OZ.Valid 7 w531.low w531.t w531.y w531.r w531.cap) (P33.root 7) :=
  Night6836Tree.sound w531 pick531 7 t568 _ (by decide +kernel)
theorem window531 : P33.WindowCount w531 := by
  apply P33.window_count w531 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov531_1
  · exact cov531_2
  · exact cov531_3
  · exact cov531_4
  · exact cov531_5
  · exact cov531_6
  · exact cov531_7
def w532 : P33.Window := ⟨9,23,7856,7822,229387869368007023,11675,15000,5000000,81920000000⟩
def h532_0 : Height w532 := ⟨11675,15000,by decide +kernel⟩
def h532_1 : Height w532 := ⟨16691,12000,by decide +kernel⟩
def h532_2 : Height w532 := ⟨28139,9000,by decide +kernel⟩
def pick532 (cl : ℕ) : Height w532 := if cl<14 then (h532_0) else (if cl<925 then (h532_1) else (h532_2))
private theorem k532_1_0 : check w532 pick532 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k532_1_1 : check w532 pick532 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k532_1_2 : check w532 pick532 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w532 pick532 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k532_1_0 k532_1_1
private theorem k532_1_3 : check w532 pick532 1 t10952 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k532_1_4 : check w532 pick532 1 t10953 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w532 pick532 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10952 k532_1_2 k532_1_3
private theorem k532_1_5 : check w532 pick532 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k532_1_6 : check w532 pick532 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k532_1_7 : check w532 pick532 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w532 pick532 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k532_1_5 k532_1_6
private theorem k532_1_8 : check w532 pick532 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k532_1_9 : check w532 pick532 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k532_1_10 : check w532 pick532 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w532 pick532 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k532_1_8 k532_1_9
private theorem k532_1_11 : check w532 pick532 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w532 pick532 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k532_1_7 k532_1_10
private theorem k532_1_12 : check w532 pick532 1 t10954 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w532 pick532 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10953 t10007 k532_1_4 k532_1_11
theorem cov532_1 : PA.Covered 1 (OZ.Valid 1 w532.low w532.t w532.y w532.r w532.cap) (P33.root 1) :=
  Night6836Tree.sound w532 pick532 1 t10954 _ k532_1_12
theorem cov532_2 : PA.Covered 2 (OZ.Valid 2 w532.low w532.t w532.y w532.r w532.cap) (P33.root 2) :=
  Night6836Tree.sound w532 pick532 2 t2745 _ (by decide +kernel)
theorem cov532_3 : PA.Covered 3 (OZ.Valid 3 w532.low w532.t w532.y w532.r w532.cap) (P33.root 3) :=
  Night6836Tree.sound w532 pick532 3 t564 _ (by decide +kernel)
theorem cov532_4 : PA.Covered 4 (OZ.Valid 4 w532.low w532.t w532.y w532.r w532.cap) (P33.root 4) :=
  Night6836Tree.sound w532 pick532 4 t565 _ (by decide +kernel)
theorem cov532_5 : PA.Covered 5 (OZ.Valid 5 w532.low w532.t w532.y w532.r w532.cap) (P33.root 5) :=
  Night6836Tree.sound w532 pick532 5 t566 _ (by decide +kernel)
theorem cov532_6 : PA.Covered 6 (OZ.Valid 6 w532.low w532.t w532.y w532.r w532.cap) (P33.root 6) :=
  Night6836Tree.sound w532 pick532 6 t567 _ (by decide +kernel)
theorem cov532_7 : PA.Covered 7 (OZ.Valid 7 w532.low w532.t w532.y w532.r w532.cap) (P33.root 7) :=
  Night6836Tree.sound w532 pick532 7 t568 _ (by decide +kernel)
theorem window532 : P33.WindowCount w532 := by
  apply P33.window_count w532 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov532_1
  · exact cov532_2
  · exact cov532_3
  · exact cov532_4
  · exact cov532_5
  · exact cov532_6
  · exact cov532_7
def w533 : P33.Window := ⟨9,24,7821,7786,232890729175307502,12862,15000,5000000,81920000000⟩
def h533_0 : Height w533 := ⟨12862,15000,by decide +kernel⟩
def h533_1 : Height w533 := ⟨18128,12000,by decide +kernel⟩
def h533_2 : Height w533 := ⟨30332,9000,by decide +kernel⟩
def pick533 (cl : ℕ) : Height w533 := if cl<32 then (h533_0) else (if cl<925 then (h533_1) else (h533_2))
private theorem k533_1_0 : check w533 pick533 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k533_1_1 : check w533 pick533 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k533_1_2 : check w533 pick533 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w533 pick533 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k533_1_0 k533_1_1
private theorem k533_1_3 : check w533 pick533 1 t10955 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k533_1_4 : check w533 pick533 1 t10956 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w533 pick533 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10955 k533_1_2 k533_1_3
private theorem k533_1_5 : check w533 pick533 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k533_1_6 : check w533 pick533 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k533_1_7 : check w533 pick533 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w533 pick533 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k533_1_5 k533_1_6
private theorem k533_1_8 : check w533 pick533 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k533_1_9 : check w533 pick533 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k533_1_10 : check w533 pick533 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w533 pick533 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k533_1_8 k533_1_9
private theorem k533_1_11 : check w533 pick533 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w533 pick533 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k533_1_7 k533_1_10
private theorem k533_1_12 : check w533 pick533 1 t10957 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w533 pick533 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10956 t10007 k533_1_4 k533_1_11
theorem cov533_1 : PA.Covered 1 (OZ.Valid 1 w533.low w533.t w533.y w533.r w533.cap) (P33.root 1) :=
  Night6836Tree.sound w533 pick533 1 t10957 _ k533_1_12
theorem cov533_2 : PA.Covered 2 (OZ.Valid 2 w533.low w533.t w533.y w533.r w533.cap) (P33.root 2) :=
  Night6836Tree.sound w533 pick533 2 t2745 _ (by decide +kernel)
theorem cov533_3 : PA.Covered 3 (OZ.Valid 3 w533.low w533.t w533.y w533.r w533.cap) (P33.root 3) :=
  Night6836Tree.sound w533 pick533 3 t564 _ (by decide +kernel)
theorem cov533_4 : PA.Covered 4 (OZ.Valid 4 w533.low w533.t w533.y w533.r w533.cap) (P33.root 4) :=
  Night6836Tree.sound w533 pick533 4 t565 _ (by decide +kernel)
theorem cov533_5 : PA.Covered 5 (OZ.Valid 5 w533.low w533.t w533.y w533.r w533.cap) (P33.root 5) :=
  Night6836Tree.sound w533 pick533 5 t566 _ (by decide +kernel)
theorem cov533_6 : PA.Covered 6 (OZ.Valid 6 w533.low w533.t w533.y w533.r w533.cap) (P33.root 6) :=
  Night6836Tree.sound w533 pick533 6 t567 _ (by decide +kernel)
theorem cov533_7 : PA.Covered 7 (OZ.Valid 7 w533.low w533.t w533.y w533.r w533.cap) (P33.root 7) :=
  Night6836Tree.sound w533 pick533 7 t568 _ (by decide +kernel)
theorem window533 : P33.WindowCount w533 := by
  apply P33.window_count w533 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov533_1
  · exact cov533_2
  · exact cov533_3
  · exact cov533_4
  · exact cov533_5
  · exact cov533_6
  · exact cov533_7
def w534 : P33.Window := ⟨9,25,7785,7751,236501673348016001,14063,15000,5000000,81920000000⟩
def h534_0 : Height w534 := ⟨14063,15000,by decide +kernel⟩
def h534_1 : Height w534 := ⟨19584,12000,by decide +kernel⟩
def pick534 (cl : ℕ) : Height w534 := if cl<32 then (h534_0) else (h534_1)
private theorem k534_1_0 : check w534 pick534 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k534_1_1 : check w534 pick534 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k534_1_2 : check w534 pick534 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w534 pick534 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k534_1_0 k534_1_1
private theorem k534_1_3 : check w534 pick534 1 t10955 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k534_1_4 : check w534 pick534 1 t10956 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w534 pick534 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10955 k534_1_2 k534_1_3
private theorem k534_1_5 : check w534 pick534 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k534_1_6 : check w534 pick534 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k534_1_7 : check w534 pick534 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w534 pick534 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k534_1_5 k534_1_6
private theorem k534_1_8 : check w534 pick534 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k534_1_9 : check w534 pick534 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k534_1_10 : check w534 pick534 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w534 pick534 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k534_1_8 k534_1_9
private theorem k534_1_11 : check w534 pick534 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w534 pick534 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k534_1_7 k534_1_10
private theorem k534_1_12 : check w534 pick534 1 t10957 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w534 pick534 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10956 t10007 k534_1_4 k534_1_11
theorem cov534_1 : PA.Covered 1 (OZ.Valid 1 w534.low w534.t w534.y w534.r w534.cap) (P33.root 1) :=
  Night6836Tree.sound w534 pick534 1 t10957 _ k534_1_12
theorem cov534_2 : PA.Covered 2 (OZ.Valid 2 w534.low w534.t w534.y w534.r w534.cap) (P33.root 2) :=
  Night6836Tree.sound w534 pick534 2 t2745 _ (by decide +kernel)
theorem cov534_3 : PA.Covered 3 (OZ.Valid 3 w534.low w534.t w534.y w534.r w534.cap) (P33.root 3) :=
  Night6836Tree.sound w534 pick534 3 t564 _ (by decide +kernel)
theorem cov534_4 : PA.Covered 4 (OZ.Valid 4 w534.low w534.t w534.y w534.r w534.cap) (P33.root 4) :=
  Night6836Tree.sound w534 pick534 4 t565 _ (by decide +kernel)
theorem cov534_5 : PA.Covered 5 (OZ.Valid 5 w534.low w534.t w534.y w534.r w534.cap) (P33.root 5) :=
  Night6836Tree.sound w534 pick534 5 t566 _ (by decide +kernel)
theorem cov534_6 : PA.Covered 6 (OZ.Valid 6 w534.low w534.t w534.y w534.r w534.cap) (P33.root 6) :=
  Night6836Tree.sound w534 pick534 6 t567 _ (by decide +kernel)
theorem cov534_7 : PA.Covered 7 (OZ.Valid 7 w534.low w534.t w534.y w534.r w534.cap) (P33.root 7) :=
  Night6836Tree.sound w534 pick534 7 t568 _ (by decide +kernel)
theorem window534 : P33.WindowCount w534 := by
  apply P33.window_count w534 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov534_1
  · exact cov534_2
  · exact cov534_3
  · exact cov534_4
  · exact cov534_5
  · exact cov534_6
  · exact cov534_7
def w535 : P33.Window := ⟨9,26,7750,7594,241365427544836078,15884,15000,5000000,81920000000⟩
def h535_0 : Height w535 := ⟨15884,15000,by decide +kernel⟩
def h535_1 : Height w535 := ⟨21920,12000,by decide +kernel⟩
def pick535 (cl : ℕ) : Height w535 := if cl<40 then (h535_0) else (h535_1)
private theorem k535_1_0 : check w535 pick535 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k535_1_1 : check w535 pick535 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k535_1_2 : check w535 pick535 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w535 pick535 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k535_1_0 k535_1_1
private theorem k535_1_3 : check w535 pick535 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k535_1_4 : check w535 pick535 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w535 pick535 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k535_1_2 k535_1_3
private theorem k535_1_5 : check w535 pick535 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k535_1_6 : check w535 pick535 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k535_1_7 : check w535 pick535 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w535 pick535 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k535_1_5 k535_1_6
private theorem k535_1_8 : check w535 pick535 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k535_1_9 : check w535 pick535 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k535_1_10 : check w535 pick535 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w535 pick535 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k535_1_8 k535_1_9
private theorem k535_1_11 : check w535 pick535 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w535 pick535 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k535_1_7 k535_1_10
private theorem k535_1_12 : check w535 pick535 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w535 pick535 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k535_1_4 k535_1_11
theorem cov535_1 : PA.Covered 1 (OZ.Valid 1 w535.low w535.t w535.y w535.r w535.cap) (P33.root 1) :=
  Night6836Tree.sound w535 pick535 1 t10025 _ k535_1_12
theorem cov535_2 : PA.Covered 2 (OZ.Valid 2 w535.low w535.t w535.y w535.r w535.cap) (P33.root 2) :=
  Night6836Tree.sound w535 pick535 2 t2745 _ (by decide +kernel)
theorem cov535_3 : PA.Covered 3 (OZ.Valid 3 w535.low w535.t w535.y w535.r w535.cap) (P33.root 3) :=
  Night6836Tree.sound w535 pick535 3 t564 _ (by decide +kernel)
theorem cov535_4 : PA.Covered 4 (OZ.Valid 4 w535.low w535.t w535.y w535.r w535.cap) (P33.root 4) :=
  Night6836Tree.sound w535 pick535 4 t565 _ (by decide +kernel)
theorem cov535_5 : PA.Covered 5 (OZ.Valid 5 w535.low w535.t w535.y w535.r w535.cap) (P33.root 5) :=
  Night6836Tree.sound w535 pick535 5 t566 _ (by decide +kernel)
theorem cov535_6 : PA.Covered 6 (OZ.Valid 6 w535.low w535.t w535.y w535.r w535.cap) (P33.root 6) :=
  Night6836Tree.sound w535 pick535 6 t567 _ (by decide +kernel)
theorem cov535_7 : PA.Covered 7 (OZ.Valid 7 w535.low w535.t w535.y w535.r w535.cap) (P33.root 7) :=
  Night6836Tree.sound w535 pick535 7 t568 _ (by decide +kernel)
theorem window535 : P33.WindowCount w535 := by
  apply P33.window_count w535 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov535_1
  · exact cov535_2
  · exact cov535_3
  · exact cov535_4
  · exact cov535_5
  · exact cov535_6
  · exact cov535_7
def w536 : P33.Window := ⟨9,27,7714,7678,243089048820722252,16532,15000,5000000,81920000000⟩
def h536_0 : Height w536 := ⟨16532,15000,by decide +kernel⟩
def h536_1 : Height w536 := ⟨22593,12000,by decide +kernel⟩
def pick536 (cl : ℕ) : Height w536 := if cl<40 then (h536_0) else (h536_1)
private theorem k536_1_0 : check w536 pick536 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k536_1_1 : check w536 pick536 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k536_1_2 : check w536 pick536 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w536 pick536 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k536_1_0 k536_1_1
private theorem k536_1_3 : check w536 pick536 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k536_1_4 : check w536 pick536 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w536 pick536 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k536_1_2 k536_1_3
private theorem k536_1_5 : check w536 pick536 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k536_1_6 : check w536 pick536 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k536_1_7 : check w536 pick536 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w536 pick536 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k536_1_5 k536_1_6
private theorem k536_1_8 : check w536 pick536 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k536_1_9 : check w536 pick536 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k536_1_10 : check w536 pick536 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w536 pick536 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k536_1_8 k536_1_9
private theorem k536_1_11 : check w536 pick536 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w536 pick536 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k536_1_7 k536_1_10
private theorem k536_1_12 : check w536 pick536 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w536 pick536 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k536_1_4 k536_1_11
theorem cov536_1 : PA.Covered 1 (OZ.Valid 1 w536.low w536.t w536.y w536.r w536.cap) (P33.root 1) :=
  Night6836Tree.sound w536 pick536 1 t10025 _ k536_1_12
private theorem k536_2_0 : check w536 pick536 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k536_2_1 : check w536 pick536 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k536_2_2 : check w536 pick536 2 t9544 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w536 pick536 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9135 k536_2_0 k536_2_1
theorem cov536_2 : PA.Covered 2 (OZ.Valid 2 w536.low w536.t w536.y w536.r w536.cap) (P33.root 2) :=
  Night6836Tree.sound w536 pick536 2 t9544 _ k536_2_2
theorem cov536_3 : PA.Covered 3 (OZ.Valid 3 w536.low w536.t w536.y w536.r w536.cap) (P33.root 3) :=
  Night6836Tree.sound w536 pick536 3 t564 _ (by decide +kernel)
theorem cov536_4 : PA.Covered 4 (OZ.Valid 4 w536.low w536.t w536.y w536.r w536.cap) (P33.root 4) :=
  Night6836Tree.sound w536 pick536 4 t565 _ (by decide +kernel)
theorem cov536_5 : PA.Covered 5 (OZ.Valid 5 w536.low w536.t w536.y w536.r w536.cap) (P33.root 5) :=
  Night6836Tree.sound w536 pick536 5 t566 _ (by decide +kernel)
theorem cov536_6 : PA.Covered 6 (OZ.Valid 6 w536.low w536.t w536.y w536.r w536.cap) (P33.root 6) :=
  Night6836Tree.sound w536 pick536 6 t567 _ (by decide +kernel)
theorem cov536_7 : PA.Covered 7 (OZ.Valid 7 w536.low w536.t w536.y w536.r w536.cap) (P33.root 7) :=
  Night6836Tree.sound w536 pick536 7 t568 _ (by decide +kernel)
theorem window536 : P33.WindowCount w536 := by
  apply P33.window_count w536 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov536_1
  · exact cov536_2
  · exact cov536_3
  · exact cov536_4
  · exact cov536_5
  · exact cov536_6
  · exact cov536_7
def w537 : P33.Window := ⟨9,28,7677,7642,241292314315791476,13843,18000,5000000,81920000000⟩
def h537_0 : Height w537 := ⟨13843,18000,by decide +kernel⟩
def h537_1 : Height w537 := ⟨17793,15000,by decide +kernel⟩
def h537_2 : Height w537 := ⟨24135,12000,by decide +kernel⟩
def h537_3 : Height w537 := ⟨39677,9000,by decide +kernel⟩
def pick537 (cl : ℕ) : Height w537 := if cl<49 then (if cl<2 then (h537_0) else (h537_1)) else (if cl<1021 then (h537_2) else (h537_3))
private theorem k537_1_0 : check w537 pick537 1 t10158 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k537_1_1 : check w537 pick537 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k537_1_2 : check w537 pick537 1 t10159 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w537 pick537 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t10158 t9991 k537_1_0 k537_1_1
private theorem k537_1_3 : check w537 pick537 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k537_1_4 : check w537 pick537 1 t10160 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w537 pick537 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t10159 t10023 k537_1_2 k537_1_3
private theorem k537_1_5 : check w537 pick537 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k537_1_6 : check w537 pick537 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k537_1_7 : check w537 pick537 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w537 pick537 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k537_1_5 k537_1_6
private theorem k537_1_8 : check w537 pick537 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k537_1_9 : check w537 pick537 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k537_1_10 : check w537 pick537 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w537 pick537 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k537_1_8 k537_1_9
private theorem k537_1_11 : check w537 pick537 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w537 pick537 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k537_1_7 k537_1_10
private theorem k537_1_12 : check w537 pick537 1 t10161 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w537 pick537 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10160 t10007 k537_1_4 k537_1_11
theorem cov537_1 : PA.Covered 1 (OZ.Valid 1 w537.low w537.t w537.y w537.r w537.cap) (P33.root 1) :=
  Night6836Tree.sound w537 pick537 1 t10161 _ k537_1_12
private theorem k537_2_0 : check w537 pick537 2 t2916 ⟨2,7,4,16,2,52,2,98⟩ = true := by decide +kernel
private theorem k537_2_1 : check w537 pick537 2 t9135 ⟨2,7,4,16,2,52,99,450⟩ = true := by decide +kernel
private theorem k537_2_2 : check w537 pick537 2 t9544 ⟨2,7,4,16,0,52,0,450⟩ = true := glue w537 pick537 2 ⟨2,7,4,16,0,52,0,450⟩ 3 98 t2916 t9135 k537_2_0 k537_2_1
theorem cov537_2 : PA.Covered 2 (OZ.Valid 2 w537.low w537.t w537.y w537.r w537.cap) (P33.root 2) :=
  Night6836Tree.sound w537 pick537 2 t9544 _ k537_2_2
theorem cov537_3 : PA.Covered 3 (OZ.Valid 3 w537.low w537.t w537.y w537.r w537.cap) (P33.root 3) :=
  Night6836Tree.sound w537 pick537 3 t564 _ (by decide +kernel)
theorem cov537_4 : PA.Covered 4 (OZ.Valid 4 w537.low w537.t w537.y w537.r w537.cap) (P33.root 4) :=
  Night6836Tree.sound w537 pick537 4 t565 _ (by decide +kernel)
theorem cov537_5 : PA.Covered 5 (OZ.Valid 5 w537.low w537.t w537.y w537.r w537.cap) (P33.root 5) :=
  Night6836Tree.sound w537 pick537 5 t566 _ (by decide +kernel)
theorem cov537_6 : PA.Covered 6 (OZ.Valid 6 w537.low w537.t w537.y w537.r w537.cap) (P33.root 6) :=
  Night6836Tree.sound w537 pick537 6 t567 _ (by decide +kernel)
theorem cov537_7 : PA.Covered 7 (OZ.Valid 7 w537.low w537.t w537.y w537.r w537.cap) (P33.root 7) :=
  Night6836Tree.sound w537 pick537 7 t568 _ (by decide +kernel)
theorem window537 : P33.WindowCount w537 := by
  apply P33.window_count w537 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov537_1
  · exact cov537_2
  · exact cov537_3
  · exact cov537_4
  · exact cov537_5
  · exact cov537_6
  · exact cov537_7
def w538 : P33.Window := ⟨9,29,5628,4629,188347251684136085,27810,27000,5000000,81920000000⟩
def h538_0 : Height w538 := ⟨27810,27000,by decide +kernel⟩
def h538_1 : Height w538 := ⟨34252,23000,by decide +kernel⟩
def h538_2 : Height w538 := ⟨44483,19000,by decide +kernel⟩
def pick538 (cl : ℕ) : Height w538 := if cl<10 then (h538_0) else (if cl<172 then (h538_1) else (h538_2))
private theorem k538_1_0 : check w538 pick538 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k538_1_1 : check w538 pick538 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k538_1_2 : check w538 pick538 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w538 pick538 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k538_1_0 k538_1_1
private theorem k538_1_3 : check w538 pick538 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k538_1_4 : check w538 pick538 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w538 pick538 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k538_1_2 k538_1_3
private theorem k538_1_5 : check w538 pick538 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k538_1_6 : check w538 pick538 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k538_1_7 : check w538 pick538 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w538 pick538 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k538_1_5 k538_1_6
private theorem k538_1_8 : check w538 pick538 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k538_1_9 : check w538 pick538 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k538_1_10 : check w538 pick538 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w538 pick538 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k538_1_8 k538_1_9
private theorem k538_1_11 : check w538 pick538 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w538 pick538 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k538_1_7 k538_1_10
private theorem k538_1_12 : check w538 pick538 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w538 pick538 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k538_1_4 k538_1_11
theorem cov538_1 : PA.Covered 1 (OZ.Valid 1 w538.low w538.t w538.y w538.r w538.cap) (P33.root 1) :=
  Night6836Tree.sound w538 pick538 1 t10025 _ k538_1_12
theorem cov538_2 : PA.Covered 2 (OZ.Valid 2 w538.low w538.t w538.y w538.r w538.cap) (P33.root 2) :=
  Night6836Tree.sound w538 pick538 2 t2745 _ (by decide +kernel)
theorem cov538_3 : PA.Covered 3 (OZ.Valid 3 w538.low w538.t w538.y w538.r w538.cap) (P33.root 3) :=
  Night6836Tree.sound w538 pick538 3 t564 _ (by decide +kernel)
theorem cov538_4 : PA.Covered 4 (OZ.Valid 4 w538.low w538.t w538.y w538.r w538.cap) (P33.root 4) :=
  Night6836Tree.sound w538 pick538 4 t565 _ (by decide +kernel)
theorem cov538_5 : PA.Covered 5 (OZ.Valid 5 w538.low w538.t w538.y w538.r w538.cap) (P33.root 5) :=
  Night6836Tree.sound w538 pick538 5 t566 _ (by decide +kernel)
theorem cov538_6 : PA.Covered 6 (OZ.Valid 6 w538.low w538.t w538.y w538.r w538.cap) (P33.root 6) :=
  Night6836Tree.sound w538 pick538 6 t567 _ (by decide +kernel)
theorem cov538_7 : PA.Covered 7 (OZ.Valid 7 w538.low w538.t w538.y w538.r w538.cap) (P33.root 7) :=
  Night6836Tree.sound w538 pick538 7 t2134 _ (by decide +kernel)
theorem window538 : P33.WindowCount w538 := by
  apply P33.window_count w538 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov538_1
  · exact cov538_2
  · exact cov538_3
  · exact cov538_4
  · exact cov538_5
  · exact cov538_6
  · exact cov538_7
def w539 : P33.Window := ⟨9,29,6098,5149,237625721517655877,25380,24000,5000000,81920000000⟩
def h539_0 : Height w539 := ⟨25380,24000,by decide +kernel⟩
def h539_1 : Height w539 := ⟨30186,21000,by decide +kernel⟩
def h539_2 : Height w539 := ⟨37115,18000,by decide +kernel⟩
def h539_3 : Height w539 := ⟨49167,15000,by decide +kernel⟩
def pick539 (cl : ℕ) : Height w539 := if cl<92 then (if cl<10 then (h539_0) else (h539_1)) else (if cl<925 then (h539_2) else (h539_3))
private theorem k539_1_0 : check w539 pick539 1 t2625 ⟨1,7,2,16,1,52,1,49⟩ = true := by decide +kernel
private theorem k539_1_1 : check w539 pick539 1 t9991 ⟨1,7,2,16,1,52,50,83⟩ = true := by decide +kernel
private theorem k539_1_2 : check w539 pick539 1 t9992 ⟨1,7,2,16,1,52,1,83⟩ = true := glue w539 pick539 1 ⟨1,7,2,16,1,52,1,83⟩ 3 49 t2625 t9991 k539_1_0 k539_1_1
private theorem k539_1_3 : check w539 pick539 1 t10023 ⟨1,7,2,16,1,52,84,138⟩ = true := by decide +kernel
private theorem k539_1_4 : check w539 pick539 1 t10024 ⟨1,7,2,16,1,52,1,138⟩ = true := glue w539 pick539 1 ⟨1,7,2,16,1,52,1,138⟩ 3 83 t9992 t10023 k539_1_2 k539_1_3
private theorem k539_1_5 : check w539 pick539 1 t2459 ⟨1,7,2,16,1,52,139,172⟩ = true := by decide +kernel
private theorem k539_1_6 : check w539 pick539 1 t382 ⟨1,7,2,16,1,52,173,199⟩ = true := by decide +kernel
private theorem k539_1_7 : check w539 pick539 1 t2460 ⟨1,7,2,16,1,52,139,199⟩ = true := glue w539 pick539 1 ⟨1,7,2,16,1,52,139,199⟩ 3 172 t2459 t382 k539_1_5 k539_1_6
private theorem k539_1_8 : check w539 pick539 1 t436 ⟨1,7,2,16,1,52,200,233⟩ = true := by decide +kernel
private theorem k539_1_9 : check w539 pick539 1 t10005 ⟨1,7,2,16,1,52,234,450⟩ = true := by decide +kernel
private theorem k539_1_10 : check w539 pick539 1 t10006 ⟨1,7,2,16,1,52,200,450⟩ = true := glue w539 pick539 1 ⟨1,7,2,16,1,52,200,450⟩ 3 233 t436 t10005 k539_1_8 k539_1_9
private theorem k539_1_11 : check w539 pick539 1 t10007 ⟨1,7,2,16,1,52,139,450⟩ = true := glue w539 pick539 1 ⟨1,7,2,16,1,52,139,450⟩ 3 199 t2460 t10006 k539_1_7 k539_1_10
private theorem k539_1_12 : check w539 pick539 1 t10025 ⟨1,7,2,16,0,52,0,450⟩ = true := glue w539 pick539 1 ⟨1,7,2,16,0,52,0,450⟩ 3 138 t10024 t10007 k539_1_4 k539_1_11
theorem cov539_1 : PA.Covered 1 (OZ.Valid 1 w539.low w539.t w539.y w539.r w539.cap) (P33.root 1) :=
  Night6836Tree.sound w539 pick539 1 t10025 _ k539_1_12
theorem cov539_2 : PA.Covered 2 (OZ.Valid 2 w539.low w539.t w539.y w539.r w539.cap) (P33.root 2) :=
  Night6836Tree.sound w539 pick539 2 t10958 _ (by decide +kernel)
theorem cov539_3 : PA.Covered 3 (OZ.Valid 3 w539.low w539.t w539.y w539.r w539.cap) (P33.root 3) :=
  Night6836Tree.sound w539 pick539 3 t564 _ (by decide +kernel)
theorem cov539_4 : PA.Covered 4 (OZ.Valid 4 w539.low w539.t w539.y w539.r w539.cap) (P33.root 4) :=
  Night6836Tree.sound w539 pick539 4 t565 _ (by decide +kernel)
theorem cov539_5 : PA.Covered 5 (OZ.Valid 5 w539.low w539.t w539.y w539.r w539.cap) (P33.root 5) :=
  Night6836Tree.sound w539 pick539 5 t566 _ (by decide +kernel)
theorem cov539_6 : PA.Covered 6 (OZ.Valid 6 w539.low w539.t w539.y w539.r w539.cap) (P33.root 6) :=
  Night6836Tree.sound w539 pick539 6 t567 _ (by decide +kernel)
theorem cov539_7 : PA.Covered 7 (OZ.Valid 7 w539.low w539.t w539.y w539.r w539.cap) (P33.root 7) :=
  Night6836Tree.sound w539 pick539 7 t2134 _ (by decide +kernel)
theorem window539 : P33.WindowCount w539 := by
  apply P33.window_count w539 (by decide) (by decide) (by decide +kernel)
  intro m hp ht
  interval_cases m
  · exact cov539_1
  · exact cov539_2
  · exact cov539_3
  · exact cov539_4
  · exact cov539_5
  · exact cov539_6
  · exact cov539_7
end ProximityPrize.SubmissionLower.Night6836Bank
