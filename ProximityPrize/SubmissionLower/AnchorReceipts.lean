import ProximityPrize.SubmissionLower.AnchorTopFactor
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic

namespace SoundnessAnchor
open K1_13 K1_13_1_1
open private fastBlock_eq from ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option Elab.async false

structure Entry (s : ℕ) where
  index : ℕ
  gain : ℕ
  powers : Powers
  checked : bound s (offset index) powers + gain ≤ blockBudget s (offset index)

private theorem certify {s r g : ℕ} {v : Powers}
    (h : bound s (offset r) v + g ≤ fastBlock s r) :
    bound s (offset r) v + g ≤ blockBudget s (offset r) := (fastBlock_eq s r) ▸ h

private def entry59_31 : Entry 59 :=
  ⟨31, 1, ⟨⟨0,0,7,1⟩,0⟩, certify (by decide +kernel)⟩
private def entry60_30 : Entry 60 :=
  ⟨30, 1, ⟨⟨0,0,7,2⟩,0⟩, certify (by decide +kernel)⟩
private def entry60_31 : Entry 60 :=
  ⟨31, 1, ⟨⟨0,0,5,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry61_29 : Entry 61 :=
  ⟨29, 9, ⟨⟨0,0,7,2⟩,0⟩, certify (by decide +kernel)⟩
private def entry62_28 : Entry 62 :=
  ⟨28, 8, ⟨⟨0,0,7,3⟩,0⟩, certify (by decide +kernel)⟩
private def entry63_27 : Entry 63 :=
  ⟨27, 8, ⟨⟨0,0,7,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry64_26 : Entry 64 :=
  ⟨26, 14, ⟨⟨0,0,8,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry64_27 : Entry 64 :=
  ⟨27, 4, ⟨⟨0,0,6,2⟩,0⟩, certify (by decide +kernel)⟩
private def entry65_25 : Entry 65 :=
  ⟨25, 12, ⟨⟨0,0,7,5⟩,0⟩, certify (by decide +kernel)⟩
private def entry65_26 : Entry 65 :=
  ⟨26, 4, ⟨⟨0,0,6,2⟩,0⟩, certify (by decide +kernel)⟩
private def entry65_27 : Entry 65 :=
  ⟨27, 3, ⟨⟨0,0,5,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry66_24 : Entry 66 :=
  ⟨24, 16, ⟨⟨0,0,7,6⟩,0⟩, certify (by decide +kernel)⟩
private def entry66_25 : Entry 66 :=
  ⟨25, 3, ⟨⟨0,0,6,3⟩,0⟩, certify (by decide +kernel)⟩
private def entry67_23 : Entry 67 :=
  ⟨23, 13, ⟨⟨0,0,8,6⟩,0⟩, certify (by decide +kernel)⟩
private def entry67_24 : Entry 67 :=
  ⟨24, 18, ⟨⟨0,0,6,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry68_22 : Entry 68 :=
  ⟨22, 9, ⟨⟨0,0,8,7⟩,0⟩, certify (by decide +kernel)⟩
private def entry68_23 : Entry 68 :=
  ⟨23, 28, ⟨⟨0,0,7,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry69_21 : Entry 69 :=
  ⟨21, 6, ⟨⟨0,0,8,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry69_22 : Entry 69 :=
  ⟨22, 24, ⟨⟨0,0,7,5⟩,0⟩, certify (by decide +kernel)⟩
private def entry69_23 : Entry 69 :=
  ⟨23, 8, ⟨⟨0,0,6,2⟩,0⟩, certify (by decide +kernel)⟩
private def entry70_20 : Entry 70 :=
  ⟨20, 3, ⟨⟨0,0,8,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry70_21 : Entry 70 :=
  ⟨21, 24, ⟨⟨0,0,7,6⟩,0⟩, certify (by decide +kernel)⟩
private def entry70_22 : Entry 70 :=
  ⟨22, 7, ⟨⟨0,0,6,3⟩,0⟩, certify (by decide +kernel)⟩
private def entry70_23 : Entry 70 :=
  ⟨23, 3, ⟨⟨0,0,5,1⟩,0⟩, certify (by decide +kernel)⟩
private def entry71_19 : Entry 71 :=
  ⟨19, 1, ⟨⟨0,0,8,9⟩,0⟩, certify (by decide +kernel)⟩
private def entry71_20 : Entry 71 :=
  ⟨20, 15, ⟨⟨0,0,7,7⟩,0⟩, certify (by decide +kernel)⟩
private def entry71_21 : Entry 71 :=
  ⟨21, 27, ⟨⟨0,0,6,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry71_22 : Entry 71 :=
  ⟨22, 1, ⟨⟨0,0,5,1⟩,0⟩, certify (by decide +kernel)⟩
private def entry72_19 : Entry 72 :=
  ⟨19, 8, ⟨⟨0,0,7,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry72_20 : Entry 72 :=
  ⟨20, 42, ⟨⟨0,0,6,5⟩,0⟩, certify (by decide +kernel)⟩
private def entry72_21 : Entry 72 :=
  ⟨21, 1, ⟨⟨0,0,5,2⟩,0⟩, certify (by decide +kernel)⟩
private def entry73_18 : Entry 73 :=
  ⟨18, 2, ⟨⟨0,0,7,9⟩,0⟩, certify (by decide +kernel)⟩
private def entry73_19 : Entry 73 :=
  ⟨19, 26, ⟨⟨0,0,6,6⟩,0⟩, certify (by decide +kernel)⟩
private def entry73_20 : Entry 73 :=
  ⟨20, 12, ⟨⟨0,0,5,3⟩,0⟩, certify (by decide +kernel)⟩
private def entry74_18 : Entry 74 :=
  ⟨18, 13, ⟨⟨0,0,7,7⟩,0⟩, certify (by decide +kernel)⟩
private def entry74_19 : Entry 74 :=
  ⟨19, 10, ⟨⟨0,0,6,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry74_20 : Entry 74 :=
  ⟨20, 5, ⟨⟨0,0,4,2⟩,0⟩, certify (by decide +kernel)⟩
private def entry75_17 : Entry 75 :=
  ⟨17, 3, ⟨⟨0,0,7,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry75_18 : Entry 75 :=
  ⟨18, 39, ⟨⟨0,0,6,5⟩,0⟩, certify (by decide +kernel)⟩
private def entry75_19 : Entry 75 :=
  ⟨19, 4, ⟨⟨0,0,5,2⟩,0⟩, certify (by decide +kernel)⟩
private def entry76_17 : Entry 76 :=
  ⟨17, 18, ⟨⟨0,0,6,6⟩,0⟩, certify (by decide +kernel)⟩
private def entry76_18 : Entry 76 :=
  ⟨18, 2, ⟨⟨0,0,5,3⟩,0⟩, certify (by decide +kernel)⟩
private def entry77_16 : Entry 77 :=
  ⟨16, 3, ⟨⟨0,1,6,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry77_17 : Entry 77 :=
  ⟨17, 51, ⟨⟨0,0,5,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry78_16 : Entry 78 :=
  ⟨16, 21, ⟨⟨0,0,5,6⟩,0⟩, certify (by decide +kernel)⟩
private def entry78_17 : Entry 78 :=
  ⟨17, 7, ⟨⟨0,0,4,3⟩,0⟩, certify (by decide +kernel)⟩
private def entry79_15 : Entry 79 :=
  ⟨15, 3, ⟨⟨0,2,5,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry79_16 : Entry 79 :=
  ⟨16, 4, ⟨⟨0,0,4,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry79_17 : Entry 79 :=
  ⟨17, 2, ⟨⟨0,0,3,1⟩,0⟩, certify (by decide +kernel)⟩
private def entry80_15 : Entry 80 :=
  ⟨15, 24, ⟨⟨0,0,5,5⟩,0⟩, certify (by decide +kernel)⟩
private def entry81_14 : Entry 81 :=
  ⟨14, 3, ⟨⟨0,3,4,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry81_15 : Entry 81 :=
  ⟨15, 11, ⟨⟨0,0,4,3⟩,0⟩, certify (by decide +kernel)⟩
private def entry82_14 : Entry 82 :=
  ⟨14, 24, ⟨⟨0,0,4,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry83_13 : Entry 83 :=
  ⟨13, 3, ⟨⟨0,4,3,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry84_13 : Entry 84 :=
  ⟨13, 24, ⟨⟨0,2,3,5⟩,0⟩, certify (by decide +kernel)⟩
private def entry85_12 : Entry 85 :=
  ⟨12, 3, ⟨⟨0,5,2,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry86_12 : Entry 86 :=
  ⟨12, 24, ⟨⟨0,3,2,5⟩,0⟩, certify (by decide +kernel)⟩
private def entry87_11 : Entry 87 :=
  ⟨11, 3, ⟨⟨0,6,1,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry87_12 : Entry 87 :=
  ⟨12, 1, ⟨⟨1,0,2,1⟩,0⟩, certify (by decide +kernel)⟩
private def entry88_11 : Entry 88 :=
  ⟨11, 24, ⟨⟨0,4,1,5⟩,0⟩, certify (by decide +kernel)⟩
private def entry89_10 : Entry 89 :=
  ⟨10, 3, ⟨⟨0,7,0,8⟩,0⟩, certify (by decide +kernel)⟩
private def entry89_11 : Entry 89 :=
  ⟨11, 1, ⟨⟨3,0,2,1⟩,0⟩, certify (by decide +kernel)⟩
private def entry90_10 : Entry 90 :=
  ⟨10, 24, ⟨⟨0,5,0,5⟩,0⟩, certify (by decide +kernel)⟩
private def entry91_9 : Entry 91 :=
  ⟨9, 3, ⟨⟨10,7,0,7⟩,1⟩, certify (by decide +kernel)⟩
private def entry91_10 : Entry 91 :=
  ⟨10, 3, ⟨⟨4,1,1,1⟩,0⟩, certify (by decide +kernel)⟩
private def entry92_9 : Entry 92 :=
  ⟨9, 24, ⟨⟨6,4,0,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry93_8 : Entry 93 :=
  ⟨8, 3, ⟨⟨13,7,0,6⟩,2⟩, certify (by decide +kernel)⟩
private def entry93_9 : Entry 93 :=
  ⟨9, 1, ⟨⟨5,2,0,1⟩,0⟩, certify (by decide +kernel)⟩
private def entry94_8 : Entry 94 :=
  ⟨8, 24, ⟨⟨12,5,0,3⟩,1⟩, certify (by decide +kernel)⟩
private def entry95_7 : Entry 95 :=
  ⟨7, 2, ⟨⟨15,7,0,6⟩,0⟩, certify (by decide +kernel)⟩
private def entry95_8 : Entry 95 :=
  ⟨8, 2, ⟨⟨7,2,0,0⟩,1⟩, certify (by decide +kernel)⟩
private def entry96_7 : Entry 96 :=
  ⟨7, 24, ⟨⟨11,5,0,2⟩,2⟩, certify (by decide +kernel)⟩
private def entry97_6 : Entry 97 :=
  ⟨6, 2, ⟨⟨17,7,0,5⟩,0⟩, certify (by decide +kernel)⟩
private def entry97_7 : Entry 97 :=
  ⟨7, 4, ⟨⟨12,3,0,0⟩,1⟩, certify (by decide +kernel)⟩
private def entry98_6 : Entry 98 :=
  ⟨6, 24, ⟨⟨15,5,0,1⟩,3⟩, certify (by decide +kernel)⟩
private def entry99_5 : Entry 99 :=
  ⟨5, 2, ⟨⟨19,7,0,4⟩,0⟩, certify (by decide +kernel)⟩
private def entry99_6 : Entry 99 :=
  ⟨6, 7, ⟨⟨12,3,0,0⟩,2⟩, certify (by decide +kernel)⟩
private def entry100_5 : Entry 100 :=
  ⟨5, 24, ⟨⟨16,5,0,0⟩,4⟩, certify (by decide +kernel)⟩
private def entry101_4 : Entry 101 :=
  ⟨4, 2, ⟨⟨21,7,0,3⟩,0⟩, certify (by decide +kernel)⟩
private def entry101_5 : Entry 101 :=
  ⟨5, 9, ⟨⟨15,3,0,0⟩,2⟩, certify (by decide +kernel)⟩
private def entry102_4 : Entry 102 :=
  ⟨4, 23, ⟨⟨20,5,0,0⟩,5⟩, certify (by decide +kernel)⟩
private def entry103_3 : Entry 103 :=
  ⟨3, 2, ⟨⟨23,7,0,2⟩,0⟩, certify (by decide +kernel)⟩
private def entry103_4 : Entry 103 :=
  ⟨4, 11, ⟨⟨18,4,0,0⟩,3⟩, certify (by decide +kernel)⟩
private def entry104_3 : Entry 104 :=
  ⟨3, 19, ⟨⟨22,5,0,0⟩,6⟩, certify (by decide +kernel)⟩
private def entry104_4 : Entry 104 :=
  ⟨4, 1, ⟨⟨17,3,0,0⟩,1⟩, certify (by decide +kernel)⟩
private def entry105_2 : Entry 105 :=
  ⟨2, 2, ⟨⟨25,7,0,1⟩,0⟩, certify (by decide +kernel)⟩
private def entry105_3 : Entry 105 :=
  ⟨3, 19, ⟨⟨20,4,0,0⟩,3⟩, certify (by decide +kernel)⟩
private def entry106_2 : Entry 106 :=
  ⟨2, 15, ⟨⟨24,6,0,0⟩,6⟩, certify (by decide +kernel)⟩
private def entry106_3 : Entry 106 :=
  ⟨3, 2, ⟨⟨16,4,0,0⟩,1⟩, certify (by decide +kernel)⟩
private def entry107_1 : Entry 107 :=
  ⟨1, 2, ⟨⟨27,7,0,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry107_2 : Entry 107 :=
  ⟨2, 9, ⟨⟨21,5,0,0⟩,4⟩, certify (by decide +kernel)⟩
private def entry108_1 : Entry 108 :=
  ⟨1, 9, ⟨⟨26,6,0,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry108_2 : Entry 108 :=
  ⟨2, 16, ⟨⟨21,4,0,0⟩,2⟩, certify (by decide +kernel)⟩
private def entry109_0 : Entry 109 :=
  ⟨0, 1, ⟨⟨28,7,0,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry109_1 : Entry 109 :=
  ⟨1, 3, ⟨⟨25,5,0,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry109_2 : Entry 109 :=
  ⟨2, 7, ⟨⟨17,3,0,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry110_0 : Entry 110 :=
  ⟨0, 4, ⟨⟨27,6,0,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry111_0 : Entry 111 :=
  ⟨0, 9, ⟨⟨26,5,0,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry111_1 : Entry 111 :=
  ⟨1, 9, ⟨⟨19,3,0,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry112_1 : Entry 112 :=
  ⟨1, 3, ⟨⟨18,2,0,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry113_1 : Entry 113 :=
  ⟨1, 1, ⟨⟨17,1,0,0⟩,0⟩, certify (by decide +kernel)⟩
private def entry114_0 : Entry 114 :=
  ⟨0, 11, ⟨⟨19,2,0,0⟩,0⟩, certify (by decide +kernel)⟩

private def entries : (s : ℕ) → List (Entry s)
  | 59 => [entry59_31]
  | 60 => [entry60_30, entry60_31]
  | 61 => [entry61_29]
  | 62 => [entry62_28]
  | 63 => [entry63_27]
  | 64 => [entry64_26, entry64_27]
  | 65 => [entry65_25, entry65_26, entry65_27]
  | 66 => [entry66_24, entry66_25]
  | 67 => [entry67_23, entry67_24]
  | 68 => [entry68_22, entry68_23]
  | 69 => [entry69_21, entry69_22, entry69_23]
  | 70 => [entry70_20, entry70_21, entry70_22, entry70_23]
  | 71 => [entry71_19, entry71_20, entry71_21, entry71_22]
  | 72 => [entry72_19, entry72_20, entry72_21]
  | 73 => [entry73_18, entry73_19, entry73_20]
  | 74 => [entry74_18, entry74_19, entry74_20]
  | 75 => [entry75_17, entry75_18, entry75_19]
  | 76 => [entry76_17, entry76_18]
  | 77 => [entry77_16, entry77_17]
  | 78 => [entry78_16, entry78_17]
  | 79 => [entry79_15, entry79_16, entry79_17]
  | 80 => [entry80_15]
  | 81 => [entry81_14, entry81_15]
  | 82 => [entry82_14]
  | 83 => [entry83_13]
  | 84 => [entry84_13]
  | 85 => [entry85_12]
  | 86 => [entry86_12]
  | 87 => [entry87_11, entry87_12]
  | 88 => [entry88_11]
  | 89 => [entry89_10, entry89_11]
  | 90 => [entry90_10]
  | 91 => [entry91_9, entry91_10]
  | 92 => [entry92_9]
  | 93 => [entry93_8, entry93_9]
  | 94 => [entry94_8]
  | 95 => [entry95_7, entry95_8]
  | 96 => [entry96_7]
  | 97 => [entry97_6, entry97_7]
  | 98 => [entry98_6]
  | 99 => [entry99_5, entry99_6]
  | 100 => [entry100_5]
  | 101 => [entry101_4, entry101_5]
  | 102 => [entry102_4]
  | 103 => [entry103_3, entry103_4]
  | 104 => [entry104_3, entry104_4]
  | 105 => [entry105_2, entry105_3]
  | 106 => [entry106_2, entry106_3]
  | 107 => [entry107_1, entry107_2]
  | 108 => [entry108_1, entry108_2]
  | 109 => [entry109_0, entry109_1, entry109_2]
  | 110 => [entry110_0]
  | 111 => [entry111_0, entry111_1]
  | 112 => [entry112_1]
  | 113 => [entry113_1]
  | 114 => [entry114_0]
  | _ => []

private def gainAt {s : ℕ} (r : ℕ) : List (Entry s) → ℕ
  | [] => 0
  | e :: rest => if r = e.index then e.gain else gainAt r rest

def improvement (s r : ℕ) := gainAt r (entries s)

theorem rank_plus_gain (s r : ℕ)
    (h : Module.finrank Geom (LinearMap.range (blockMap s (offset r))) ≤ blockBudget s (offset r)) :
    Module.finrank Geom (LinearMap.range (blockMap s (offset r))) + improvement s r ≤
      blockBudget s (offset r) := by
  suffices H : ∀ xs : List (Entry s),
      Module.finrank Geom (LinearMap.range (blockMap s (offset r))) + gainAt r xs ≤
        blockBudget s (offset r) from H _
  intro xs
  induction xs with
  | nil => exact h
  | cons e rest ih =>
    simp only [gainAt]
    split
    next he =>
      subst r
      exact (Nat.add_le_add_right (rank_block_le s (offset e.index) e.powers) e.gain).trans e.checked
    next => exact ih

theorem gain_total : (∑ s : Fin 121, ∑ r : Fin 138, improvement s r) = 1057 := by
  simp only [← sumRange_eq_fin]
  decide +kernel

end SoundnessAnchor
