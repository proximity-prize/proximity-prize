import ProximityPrize.SubmissionLower.R6961LoRescueSourceSchedule
import ProximityPrize.SubmissionLower.R6963LoFastLayerNat
import ProximityPrize.SubmissionLower.R6961LoRescuePoolMoments0

set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueSource
open P1_7 (Bank debit)
open Lower6960.HelperSource (WidthGuard)
open Lower6960.RescueSource (fastLayer fastPhase)
open Lower6963.Lo.FastLayerNat (fastLayerG phase_of_blockG)
open Lower6961.Lo.RescuePoolMoments

private def blk (f : ℕ → ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | s, (n, v) :: rest => phaseBlock f s n = v ∧ blk f (s + n) rest

private theorem blk_sum {f : ℕ → ℕ} {s : ℕ} {cs : List (ℕ × ℕ)} (h : blk f s cs) :
    phaseBlock f s (cs.map Prod.fst).sum = (cs.map Prod.snd).sum := by
  induction cs generalizing s with
  | nil => rfl
  | cons cv rest ih =>
    rcases cv with ⟨n, v⟩
    rcases h with ⟨h1, h2⟩
    exact phaseBlock_append h1 (ih h2) rfl rfl rfl

private theorem mkP (r : Fin 13) (s : Fin 17) (h a b c d e n z : ℕ) (cs : List (ℕ × ℕ))
    (hsz : (bank r s).shape.J / b + 1 = n)
    (hn : (cs.map Prod.fst).sum = n) (hz : (cs.map Prod.snd).sum = z)
    (hc : blk (fastLayer (bank r s).shape 179798 h a b c d e) 0 cs) :
    fastPhase (bank r s).shape 179798 h a b c d e = z :=
  phase_of_block hsz (by rw [← hn, ← hz]; exact blk_sum hc)


private theorem rec_6_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2368 1 1 6 1 0) 0 128 = 682282407765565101838 := by decide +kernel
private theorem rec_6_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2368 1 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2368 1 1 6 1 0) 0 130 = 682282407765565101838 :=
  phaseBlock_append rec_6_1_2368_0_part0 rec_6_1_2368_0_part1 rfl rfl rfl

private theorem rec_6_1_2368_0 : fastPhase (bank 6 1).shape 179798 2368 1 1 6 1 0 = 682282407765565101838 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_1_2368_0_join0

private theorem rec_6_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2368 1 1 6 1 1) 0 128 = 665050719762493829062 := by decide +kernel
private theorem rec_6_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2368 1 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2368 1 1 6 1 1) 0 130 = 665050719762493829062 :=
  phaseBlock_append rec_6_1_2368_1_part0 rec_6_1_2368_1_part1 rfl rfl rfl

private theorem rec_6_1_2368_1 : fastPhase (bank 6 1).shape 179798 2368 1 1 6 1 1 = 665050719762493829062 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_1_2368_1_join0

private theorem rec_6_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2369 1 1 6 1 0) 0 128 = 682285874879618328480 := by decide +kernel
private theorem rec_6_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2369 1 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2369 1 1 6 1 0) 0 130 = 682285874879618328480 :=
  phaseBlock_append rec_6_1_2369_0_part0 rec_6_1_2369_0_part1 rfl rfl rfl

private theorem rec_6_1_2369_0 : fastPhase (bank 6 1).shape 179798 2369 1 1 6 1 0 = 682285874879618328480 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_1_2369_0_join0

private theorem rec_6_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2369 1 1 6 1 1) 0 128 = 665054054861380483932 := by decide +kernel
private theorem rec_6_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2369 1 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 1).shape 179798 2369 1 1 6 1 1) 0 130 = 665054054861380483932 :=
  phaseBlock_append rec_6_1_2369_1_part0 rec_6_1_2369_1_part1 rfl rfl rfl

private theorem rec_6_1_2369_1 : fastPhase (bank 6 1).shape 179798 2369 1 1 6 1 1 = 665054054861380483932 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_1_2369_1_join0

theorem receipt_6_1 : Checked (bank 6 1) 1 6 1 := by
  refine checked_from_values (bank 6 1) 1 6 1
    (P3_7_1.checked (bank 6 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_1_2368_0 rec_6_1_2368_1 rec_6_1_2369_0 rec_6_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2368 2 1 6 1 0) 0 128 = 741467960806796167532 := by decide +kernel
private theorem rec_6_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2368 2 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2368 2 1 6 1 0) 0 130 = 741467960806796167532 :=
  phaseBlock_append rec_6_2_2368_0_part0 rec_6_2_2368_0_part1 rfl rfl rfl

private theorem rec_6_2_2368_0 : fastPhase (bank 6 2).shape 179798 2368 2 1 6 1 0 = 741467960806796167532 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_2_2368_0_join0

private theorem rec_6_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2368 2 1 6 1 1) 0 128 = 722752036725954530932 := by decide +kernel
private theorem rec_6_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2368 2 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2368 2 1 6 1 1) 0 130 = 722752036725954530932 :=
  phaseBlock_append rec_6_2_2368_1_part0 rec_6_2_2368_1_part1 rfl rfl rfl

private theorem rec_6_2_2368_1 : fastPhase (bank 6 2).shape 179798 2368 2 1 6 1 1 = 722752036725954530932 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_2_2368_1_join0

private theorem rec_6_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2369 2 1 6 1 0) 0 128 = 741471692946005642628 := by decide +kernel
private theorem rec_6_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2369 2 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2369 2 1 6 1 0) 0 130 = 741471692946005642628 :=
  phaseBlock_append rec_6_2_2369_0_part0 rec_6_2_2369_0_part1 rfl rfl rfl

private theorem rec_6_2_2369_0 : fastPhase (bank 6 2).shape 179798 2369 2 1 6 1 0 = 741471692946005642628 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_2_2369_0_join0

private theorem rec_6_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2369 2 1 6 1 1) 0 128 = 722755626582970350678 := by decide +kernel
private theorem rec_6_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2369 2 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 2).shape 179798 2369 2 1 6 1 1) 0 130 = 722755626582970350678 :=
  phaseBlock_append rec_6_2_2369_1_part0 rec_6_2_2369_1_part1 rfl rfl rfl

private theorem rec_6_2_2369_1 : fastPhase (bank 6 2).shape 179798 2369 2 1 6 1 1 = 722755626582970350678 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_2_2369_1_join0

theorem receipt_6_2 : Checked (bank 6 2) 2 6 1 := by
  refine checked_from_values (bank 6 2) 2 6 1
    (P3_7_1.checked (bank 6 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_2_2368_0 rec_6_2_2368_1 rec_6_2_2369_0 rec_6_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2368 3 1 6 1 0) 0 128 = 808876512165856985494 := by decide +kernel
private theorem rec_6_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2368 3 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2368 3 1 6 1 0) 0 130 = 808876512165856985494 :=
  phaseBlock_append rec_6_3_2368_0_part0 rec_6_3_2368_0_part1 rfl rfl rfl

private theorem rec_6_3_2368_0 : fastPhase (bank 6 3).shape 179798 2368 3 1 6 1 0 = 808876512165856985494 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_3_2368_0_join0

private theorem rec_6_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2368 3 1 6 1 1) 0 128 = 788470614561609217302 := by decide +kernel
private theorem rec_6_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2368 3 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2368 3 1 6 1 1) 0 130 = 788470614561609217302 :=
  phaseBlock_append rec_6_3_2368_1_part0 rec_6_3_2368_1_part1 rfl rfl rfl

private theorem rec_6_3_2368_1 : fastPhase (bank 6 3).shape 179798 2368 3 1 6 1 1 = 788470614561609217302 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_3_2368_1_join0

private theorem rec_6_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2369 3 1 6 1 0) 0 128 = 808880544612520049978 := by decide +kernel
private theorem rec_6_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2369 3 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2369 3 1 6 1 0) 0 130 = 808880544612520049978 :=
  phaseBlock_append rec_6_3_2369_0_part0 rec_6_3_2369_0_part1 rfl rfl rfl

private theorem rec_6_3_2369_0 : fastPhase (bank 6 3).shape 179798 2369 3 1 6 1 0 = 808880544612520049978 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_3_2369_0_join0

private theorem rec_6_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2369 3 1 6 1 1) 0 128 = 788474493082630231992 := by decide +kernel
private theorem rec_6_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2369 3 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 3).shape 179798 2369 3 1 6 1 1) 0 130 = 788474493082630231992 :=
  phaseBlock_append rec_6_3_2369_1_part0 rec_6_3_2369_1_part1 rfl rfl rfl

private theorem rec_6_3_2369_1 : fastPhase (bank 6 3).shape 179798 2369 3 1 6 1 1 = 788474493082630231992 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_3_2369_1_join0

theorem receipt_6_3 : Checked (bank 6 3) 3 6 1 := by
  refine checked_from_values (bank 6 3) 3 6 1
    (P3_7_1.checked (bank 6 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_3_2368_0 rec_6_3_2368_1 rec_6_3_2369_0 rec_6_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2368 4 1 6 1 0) 0 128 = 886050465947463975032 := by decide +kernel
private theorem rec_6_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2368 4 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2368 4 1 6 1 0) 0 130 = 886050465947463975032 :=
  phaseBlock_append rec_6_4_2368_0_part0 rec_6_4_2368_0_part1 rfl rfl rfl

private theorem rec_6_4_2368_0 : fastPhase (bank 6 4).shape 179798 2368 4 1 6 1 0 = 886050465947463975032 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_4_2368_0_join0

private theorem rec_6_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2368 4 1 6 1 1) 0 128 = 863710317060503232232 := by decide +kernel
private theorem rec_6_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2368 4 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2368 4 1 6 1 1) 0 130 = 863710317060503232232 :=
  phaseBlock_append rec_6_4_2368_1_part0 rec_6_4_2368_1_part1 rfl rfl rfl

private theorem rec_6_4_2368_1 : fastPhase (bank 6 4).shape 179798 2368 4 1 6 1 1 = 863710317060503232232 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_4_2368_1_join0

private theorem rec_6_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2369 4 1 6 1 0) 0 128 = 886054840408718867628 := by decide +kernel
private theorem rec_6_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2369 4 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2369 4 1 6 1 0) 0 130 = 886054840408718867628 :=
  phaseBlock_append rec_6_4_2369_0_part0 rec_6_4_2369_0_part1 rfl rfl rfl

private theorem rec_6_4_2369_0 : fastPhase (bank 6 4).shape 179798 2369 4 1 6 1 0 = 886054840408718867628 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_4_2369_0_join0

private theorem rec_6_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2369 4 1 6 1 1) 0 128 = 863714524324308261078 := by decide +kernel
private theorem rec_6_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2369 4 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 4).shape 179798 2369 4 1 6 1 1) 0 130 = 863714524324308261078 :=
  phaseBlock_append rec_6_4_2369_1_part0 rec_6_4_2369_1_part1 rfl rfl rfl

private theorem rec_6_4_2369_1 : fastPhase (bank 6 4).shape 179798 2369 4 1 6 1 1 = 863714524324308261078 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_4_2369_1_join0

theorem receipt_6_4 : Checked (bank 6 4) 4 6 1 := by
  refine checked_from_values (bank 6 4) 4 6 1
    (P3_7_1.checked (bank 6 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_4_2368_0 rec_6_4_2368_1 rec_6_4_2369_0 rec_6_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2368 5 1 6 1 0) 0 128 = 974326189191342831613 := by decide +kernel
private theorem rec_6_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2368 5 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2368 5 1 6 1 0) 0 130 = 974326189191342831613 :=
  phaseBlock_append rec_6_5_2368_0_part0 rec_6_5_2368_0_part1 rfl rfl rfl

private theorem rec_6_5_2368_0 : fastPhase (bank 6 5).shape 179798 2368 5 1 6 1 0 = 974326189191342831613 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_5_2368_0_join0

private theorem rec_6_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2368 5 1 6 1 1) 0 128 = 949774168534562958181 := by decide +kernel
private theorem rec_6_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2368 5 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2368 5 1 6 1 1) 0 130 = 949774168534562958181 :=
  phaseBlock_append rec_6_5_2368_1_part0 rec_6_5_2368_1_part1 rfl rfl rfl

private theorem rec_6_5_2368_1 : fastPhase (bank 6 5).shape 179798 2368 5 1 6 1 1 = 949774168534562958181 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_5_2368_1_join0

private theorem rec_6_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2369 5 1 6 1 0) 0 128 = 974330952500305158150 := by decide +kernel
private theorem rec_6_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2369 5 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2369 5 1 6 1 0) 0 130 = 974330952500305158150 :=
  phaseBlock_append rec_6_5_2369_0_part0 rec_6_5_2369_0_part1 rfl rfl rfl

private theorem rec_6_5_2369_0 : fastPhase (bank 6 5).shape 179798 2369 5 1 6 1 0 = 974330952500305158150 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_5_2369_0_join0

private theorem rec_6_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2369 5 1 6 1 1) 0 128 = 949778749541549742444 := by decide +kernel
private theorem rec_6_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2369 5 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 5).shape 179798 2369 5 1 6 1 1) 0 130 = 949778749541549742444 :=
  phaseBlock_append rec_6_5_2369_1_part0 rec_6_5_2369_1_part1 rfl rfl rfl

private theorem rec_6_5_2369_1 : fastPhase (bank 6 5).shape 179798 2369 5 1 6 1 1 = 949778749541549742444 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_5_2369_1_join0

theorem receipt_6_5 : Checked (bank 6 5) 5 6 1 := by
  refine checked_from_values (bank 6 5) 5 6 1
    (P3_7_1.checked (bank 6 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_5_2368_0 rec_6_5_2368_1 rec_6_5_2369_0 rec_6_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2368 7 1 6 1 0) 0 128 = 1195978283322696244588 := by decide +kernel
private theorem rec_6_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2368 7 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2368 7 1 6 1 0) 0 130 = 1195978283322696244588 :=
  phaseBlock_append rec_6_6_2368_0_part0 rec_6_6_2368_0_part1 rfl rfl rfl

private theorem rec_6_6_2368_0 : fastPhase (bank 6 6).shape 179798 2368 7 1 6 1 0 = 1195978283322696244588 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_6_2368_0_join0

private theorem rec_6_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2368 7 1 6 1 1) 0 128 = 1165874870015942676028 := by decide +kernel
private theorem rec_6_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2368 7 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2368 7 1 6 1 1) 0 130 = 1165874870015942676028 :=
  phaseBlock_append rec_6_6_2368_1_part0 rec_6_6_2368_1_part1 rfl rfl rfl

private theorem rec_6_6_2368_1 : fastPhase (bank 6 6).shape 179798 2368 7 1 6 1 1 = 1165874870015942676028 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_6_2368_1_join0

private theorem rec_6_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2369 7 1 6 1 0) 0 128 = 1195984014908689321602 := by decide +kernel
private theorem rec_6_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2369 7 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2369 7 1 6 1 0) 0 130 = 1195984014908689321602 :=
  phaseBlock_append rec_6_6_2369_0_part0 rec_6_6_2369_0_part1 rfl rfl rfl

private theorem rec_6_6_2369_0 : fastPhase (bank 6 6).shape 179798 2369 7 1 6 1 0 = 1195984014908689321602 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_6_2369_0_join0

private theorem rec_6_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2369 7 1 6 1 1) 0 128 = 1165880381636282010552 := by decide +kernel
private theorem rec_6_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2369 7 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 6).shape 179798 2369 7 1 6 1 1) 0 130 = 1165880381636282010552 :=
  phaseBlock_append rec_6_6_2369_1_part0 rec_6_6_2369_1_part1 rfl rfl rfl

private theorem rec_6_6_2369_1 : fastPhase (bank 6 6).shape 179798 2369 7 1 6 1 1 = 1165880381636282010552 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_6_2369_1_join0

theorem receipt_6_6 : Checked (bank 6 6) 7 6 1 := by
  refine checked_from_values (bank 6 6) 7 6 1
    (P3_7_1.checked (bank 6 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_6_2368_0 rec_6_6_2368_1 rec_6_6_2369_0 rec_6_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2368 10 1 6 1 0) 0 128 = 1701228088552949117168 := by decide +kernel
private theorem rec_6_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2368 10 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2368 10 1 6 1 0) 0 130 = 1701228088552949117168 :=
  phaseBlock_append rec_6_7_2368_0_part0 rec_6_7_2368_0_part1 rfl rfl rfl

private theorem rec_6_7_2368_0 : fastPhase (bank 6 7).shape 179798 2368 10 1 6 1 0 = 1701228088552949117168 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_7_2368_0_join0

private theorem rec_6_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2368 10 1 6 1 1) 0 128 = 1658479650464043936088 := by decide +kernel
private theorem rec_6_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2368 10 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2368 10 1 6 1 1) 0 130 = 1658479650464043936088 :=
  phaseBlock_append rec_6_7_2368_1_part0 rec_6_7_2368_1_part1 rfl rfl rfl

private theorem rec_6_7_2368_1 : fastPhase (bank 6 7).shape 179798 2368 10 1 6 1 1 = 1658479650464043936088 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_7_2368_1_join0

private theorem rec_6_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2369 10 1 6 1 0) 0 128 = 1701235995326203458052 := by decide +kernel
private theorem rec_6_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2369 10 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2369 10 1 6 1 0) 0 130 = 1701235995326203458052 :=
  phaseBlock_append rec_6_7_2369_0_part0 rec_6_7_2369_0_part1 rfl rfl rfl

private theorem rec_6_7_2369_0 : fastPhase (bank 6 7).shape 179798 2369 10 1 6 1 0 = 1701235995326203458052 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_7_2369_0_join0

private theorem rec_6_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2369 10 1 6 1 1) 0 128 = 1658487252454689467342 := by decide +kernel
private theorem rec_6_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2369 10 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 7).shape 179798 2369 10 1 6 1 1) 0 130 = 1658487252454689467342 :=
  phaseBlock_append rec_6_7_2369_1_part0 rec_6_7_2369_1_part1 rfl rfl rfl

private theorem rec_6_7_2369_1 : fastPhase (bank 6 7).shape 179798 2369 10 1 6 1 1 = 1658487252454689467342 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_7_2369_1_join0

theorem receipt_6_7 : Checked (bank 6 7) 10 6 1 := by
  refine checked_from_values (bank 6 7) 10 6 1
    (P3_7_1.checked (bank 6 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_7_2368_0 rec_6_7_2368_1 rec_6_7_2369_0 rec_6_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2368 16 1 6 1 0) 0 128 = 13059104124026628983399 := by decide +kernel
private theorem rec_6_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2368 16 1 6 1 0) 128 63 = 0 := by decide +kernel
private theorem rec_6_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2368 16 1 6 1 0) 0 191 = 13059104124026628983399 :=
  phaseBlock_append rec_6_8_2368_0_part0 rec_6_8_2368_0_part1 rfl rfl rfl

private theorem rec_6_8_2368_0 : fastPhase (bank 6 8).shape 179798 2368 16 1 6 1 0 = 13059104124026628983399 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_6_8_2368_0_join0

private theorem rec_6_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2368 16 1 6 1 1) 0 128 = 12835197275954480021527 := by decide +kernel
private theorem rec_6_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2368 16 1 6 1 1) 128 63 = 0 := by decide +kernel
private theorem rec_6_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2368 16 1 6 1 1) 0 191 = 12835197275954480021527 :=
  phaseBlock_append rec_6_8_2368_1_part0 rec_6_8_2368_1_part1 rfl rfl rfl

private theorem rec_6_8_2368_1 : fastPhase (bank 6 8).shape 179798 2368 16 1 6 1 1 = 12835197275954480021527 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_6_8_2368_1_join0

private theorem rec_6_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2369 16 1 6 1 0) 0 128 = 13059164114596636804506 := by decide +kernel
private theorem rec_6_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2369 16 1 6 1 0) 128 63 = 0 := by decide +kernel
private theorem rec_6_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2369 16 1 6 1 0) 0 191 = 13059164114596636804506 :=
  phaseBlock_append rec_6_8_2369_0_part0 rec_6_8_2369_0_part1 rfl rfl rfl

private theorem rec_6_8_2369_0 : fastPhase (bank 6 8).shape 179798 2369 16 1 6 1 0 = 13059164114596636804506 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_6_8_2369_0_join0

private theorem rec_6_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2369 16 1 6 1 1) 0 128 = 12835255683217799209980 := by decide +kernel
private theorem rec_6_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2369 16 1 6 1 1) 128 63 = 0 := by decide +kernel
private theorem rec_6_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 8).shape 179798 2369 16 1 6 1 1) 0 191 = 12835255683217799209980 :=
  phaseBlock_append rec_6_8_2369_1_part0 rec_6_8_2369_1_part1 rfl rfl rfl

private theorem rec_6_8_2369_1 : fastPhase (bank 6 8).shape 179798 2369 16 1 6 1 1 = 12835255683217799209980 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_6_8_2369_1_join0

theorem receipt_6_8 : Checked (bank 6 8) 16 6 1 := by
  refine checked_from_values (bank 6 8) 16 6 1
    (P3_7_1.checked (bank 6 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_8_2368_0 rec_6_8_2368_1 rec_6_8_2369_0 rec_6_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2368 10 1 6 1 0) 0 128 = 1701228088552949117168 := by decide +kernel
private theorem rec_6_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2368 10 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2368 10 1 6 1 0) 0 130 = 1701228088552949117168 :=
  phaseBlock_append rec_6_9_2368_0_part0 rec_6_9_2368_0_part1 rfl rfl rfl

private theorem rec_6_9_2368_0 : fastPhase (bank 6 9).shape 179798 2368 10 1 6 1 0 = 1701228088552949117168 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_9_2368_0_join0

private theorem rec_6_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2368 10 1 6 1 1) 0 128 = 1658479650464043936088 := by decide +kernel
private theorem rec_6_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2368 10 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2368 10 1 6 1 1) 0 130 = 1658479650464043936088 :=
  phaseBlock_append rec_6_9_2368_1_part0 rec_6_9_2368_1_part1 rfl rfl rfl

private theorem rec_6_9_2368_1 : fastPhase (bank 6 9).shape 179798 2368 10 1 6 1 1 = 1658479650464043936088 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_9_2368_1_join0

private theorem rec_6_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2369 10 1 6 1 0) 0 128 = 1701235995326203458052 := by decide +kernel
private theorem rec_6_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2369 10 1 6 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_6_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2369 10 1 6 1 0) 0 130 = 1701235995326203458052 :=
  phaseBlock_append rec_6_9_2369_0_part0 rec_6_9_2369_0_part1 rfl rfl rfl

private theorem rec_6_9_2369_0 : fastPhase (bank 6 9).shape 179798 2369 10 1 6 1 0 = 1701235995326203458052 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_9_2369_0_join0

private theorem rec_6_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2369 10 1 6 1 1) 0 128 = 1658487252454689467342 := by decide +kernel
private theorem rec_6_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2369 10 1 6 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_6_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 9).shape 179798 2369 10 1 6 1 1) 0 130 = 1658487252454689467342 :=
  phaseBlock_append rec_6_9_2369_1_part0 rec_6_9_2369_1_part1 rfl rfl rfl

private theorem rec_6_9_2369_1 : fastPhase (bank 6 9).shape 179798 2369 10 1 6 1 1 = 1658487252454689467342 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_6_9_2369_1_join0

theorem receipt_6_9 : Checked (bank 6 9) 10 6 1 := by
  refine checked_from_values (bank 6 9) 10 6 1
    (P3_7_1.checked (bank 6 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_9_2368_0 rec_6_9_2368_1 rec_6_9_2369_0 rec_6_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2368 20 1 6 1 0) 0 128 = 18115437662024048020184 := by decide +kernel
private theorem rec_6_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2368 20 1 6 1 0) 128 63 = 0 := by decide +kernel
private theorem rec_6_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2368 20 1 6 1 0) 0 191 = 18115437662024048020184 :=
  phaseBlock_append rec_6_10_2368_0_part0 rec_6_10_2368_0_part1 rfl rfl rfl

private theorem rec_6_10_2368_0 : fastPhase (bank 6 10).shape 179798 2368 20 1 6 1 0 = 18115437662024048020184 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_6_10_2368_0_join0

private theorem rec_6_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2368 20 1 6 1 1) 0 128 = 17805313007233099230520 := by decide +kernel
private theorem rec_6_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2368 20 1 6 1 1) 128 63 = 0 := by decide +kernel
private theorem rec_6_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2368 20 1 6 1 1) 0 191 = 17805313007233099230520 :=
  phaseBlock_append rec_6_10_2368_1_part0 rec_6_10_2368_1_part1 rfl rfl rfl

private theorem rec_6_10_2368_1 : fastPhase (bank 6 10).shape 179798 2368 20 1 6 1 1 = 17805313007233099230520 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_6_10_2368_1_join0

private theorem rec_6_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2369 20 1 6 1 0) 0 128 = 18115518513766161887958 := by decide +kernel
private theorem rec_6_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2369 20 1 6 1 0) 128 63 = 0 := by decide +kernel
private theorem rec_6_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2369 20 1 6 1 0) 0 191 = 18115518513766161887958 :=
  phaseBlock_append rec_6_10_2369_0_part0 rec_6_10_2369_0_part1 rfl rfl rfl

private theorem rec_6_10_2369_0 : fastPhase (bank 6 10).shape 179798 2369 20 1 6 1 0 = 18115518513766161887958 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_6_10_2369_0_join0

private theorem rec_6_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2369 20 1 6 1 1) 0 128 = 17805391715704436751420 := by decide +kernel
private theorem rec_6_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2369 20 1 6 1 1) 128 63 = 0 := by decide +kernel
private theorem rec_6_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 10).shape 179798 2369 20 1 6 1 1) 0 191 = 17805391715704436751420 :=
  phaseBlock_append rec_6_10_2369_1_part0 rec_6_10_2369_1_part1 rfl rfl rfl

private theorem rec_6_10_2369_1 : fastPhase (bank 6 10).shape 179798 2369 20 1 6 1 1 = 17805391715704436751420 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_6_10_2369_1_join0

theorem receipt_6_10 : Checked (bank 6 10) 20 6 1 := by
  refine checked_from_values (bank 6 10) 20 6 1
    (P3_7_1.checked (bank 6 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_10_2368_0 rec_6_10_2368_1 rec_6_10_2369_0 rec_6_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2368 32 1 6 1 0) 0 128 = 143722456459274689704800 := by decide +kernel
private theorem rec_6_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2368 32 1 6 1 0) 128 128 = 8215116845756450116669 := by decide +kernel
private theorem rec_6_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2368 32 1 6 1 0) 256 22 = 0 := by decide +kernel
private theorem rec_6_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2368 32 1 6 1 0) 128 150 = 8215116845756450116669 :=
  phaseBlock_append rec_6_11_2368_0_part1 rec_6_11_2368_0_part2 rfl rfl rfl
private theorem rec_6_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2368 32 1 6 1 0) 0 278 = 151937573305031139821469 :=
  phaseBlock_append rec_6_11_2368_0_part0 rec_6_11_2368_0_join0 rfl rfl rfl

private theorem rec_6_11_2368_0 : fastPhase (bank 6 11).shape 179798 2368 32 1 6 1 0 = 151937573305031139821469 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_6_11_2368_0_join1

private theorem rec_6_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2368 32 1 6 1 1) 0 128 = 142314470631171229565408 := by decide +kernel
private theorem rec_6_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2368 32 1 6 1 1) 128 128 = 7825328895627913741678 := by decide +kernel
private theorem rec_6_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2368 32 1 6 1 1) 256 22 = 0 := by decide +kernel
private theorem rec_6_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2368 32 1 6 1 1) 128 150 = 7825328895627913741678 :=
  phaseBlock_append rec_6_11_2368_1_part1 rec_6_11_2368_1_part2 rfl rfl rfl
private theorem rec_6_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2368 32 1 6 1 1) 0 278 = 150139799526799143307086 :=
  phaseBlock_append rec_6_11_2368_1_part0 rec_6_11_2368_1_join0 rfl rfl rfl

private theorem rec_6_11_2368_1 : fastPhase (bank 6 11).shape 179798 2368 32 1 6 1 1 = 150139799526799143307086 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_6_11_2368_1_join1

private theorem rec_6_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2369 32 1 6 1 0) 0 128 = 143723126702182377017280 := by decide +kernel
private theorem rec_6_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2369 32 1 6 1 0) 128 128 = 8215113729988662474894 := by decide +kernel
private theorem rec_6_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2369 32 1 6 1 0) 256 22 = 0 := by decide +kernel
private theorem rec_6_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2369 32 1 6 1 0) 128 150 = 8215113729988662474894 :=
  phaseBlock_append rec_6_11_2369_0_part1 rec_6_11_2369_0_part2 rfl rfl rfl
private theorem rec_6_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2369 32 1 6 1 0) 0 278 = 151938240432171039492174 :=
  phaseBlock_append rec_6_11_2369_0_part0 rec_6_11_2369_0_join0 rfl rfl rfl

private theorem rec_6_11_2369_0 : fastPhase (bank 6 11).shape 179798 2369 32 1 6 1 0 = 151938240432171039492174 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_6_11_2369_0_join1

private theorem rec_6_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2369 32 1 6 1 1) 0 128 = 142315128534385591297344 := by decide +kernel
private theorem rec_6_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2369 32 1 6 1 1) 128 128 = 7825325843032075797141 := by decide +kernel
private theorem rec_6_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2369 32 1 6 1 1) 256 22 = 0 := by decide +kernel
private theorem rec_6_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2369 32 1 6 1 1) 128 150 = 7825325843032075797141 :=
  phaseBlock_append rec_6_11_2369_1_part1 rec_6_11_2369_1_part2 rfl rfl rfl
private theorem rec_6_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 6 11).shape 179798 2369 32 1 6 1 1) 0 278 = 150140454377417667094485 :=
  phaseBlock_append rec_6_11_2369_1_part0 rec_6_11_2369_1_join0 rfl rfl rfl

private theorem rec_6_11_2369_1 : fastPhase (bank 6 11).shape 179798 2369 32 1 6 1 1 = 150140454377417667094485 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_6_11_2369_1_join1

theorem receipt_6_11 : Checked (bank 6 11) 32 6 1 := by
  refine checked_from_values (bank 6 11) 32 6 1
    (P3_7_1.checked (bank 6 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_11_2368_0 rec_6_11_2368_1 rec_6_11_2369_0 rec_6_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2368 31 1 6 1 0) 0 128 = 135716315988913794712544 := by decide +kernel
private theorem rec_6_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2368 31 1 6 1 0) 128 128 = 7754055822582148682071 := by decide +kernel
private theorem rec_6_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2368 31 1 6 1 0) 256 22 = 0 := by decide +kernel
private theorem rec_6_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2368 31 1 6 1 0) 128 150 = 7754055822582148682071 :=
  phaseBlock_append rec_6_12_2368_0_part1 rec_6_12_2368_0_part2 rfl rfl rfl
private theorem rec_6_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2368 31 1 6 1 0) 0 278 = 143470371811495943394615 :=
  phaseBlock_append rec_6_12_2368_0_part0 rec_6_12_2368_0_join0 rfl rfl rfl

private theorem rec_6_12_2368_0 : fastPhase (bank 6 12).shape 179798 2368 31 1 6 1 0 = 143470371811495943394615 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_6_12_2368_0_join1

private theorem rec_6_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2368 31 1 6 1 1) 0 128 = 134386214269050132945632 := by decide +kernel
private theorem rec_6_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2368 31 1 6 1 1) 128 128 = 7386119579331744116824 := by decide +kernel
private theorem rec_6_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2368 31 1 6 1 1) 256 22 = 0 := by decide +kernel
private theorem rec_6_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2368 31 1 6 1 1) 128 150 = 7386119579331744116824 :=
  phaseBlock_append rec_6_12_2368_1_part1 rec_6_12_2368_1_part2 rfl rfl rfl
private theorem rec_6_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2368 31 1 6 1 1) 0 278 = 141772333848381877062456 :=
  phaseBlock_append rec_6_12_2368_1_part0 rec_6_12_2368_1_join0 rfl rfl rfl

private theorem rec_6_12_2368_1 : fastPhase (bank 6 12).shape 179798 2368 31 1 6 1 1 = 141772333848381877062456 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_6_12_2368_1_join1

private theorem rec_6_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2369 31 1 6 1 0) 0 128 = 135716951979969084063840 := by decide +kernel
private theorem rec_6_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2369 31 1 6 1 0) 128 128 = 7754053008763360696047 := by decide +kernel
private theorem rec_6_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2369 31 1 6 1 0) 256 22 = 0 := by decide +kernel
private theorem rec_6_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2369 31 1 6 1 0) 128 150 = 7754053008763360696047 :=
  phaseBlock_append rec_6_12_2369_0_part1 rec_6_12_2369_0_part2 rfl rfl rfl
private theorem rec_6_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2369 31 1 6 1 0) 0 278 = 143471004988732444759887 :=
  phaseBlock_append rec_6_12_2369_0_part0 rec_6_12_2369_0_join0 rfl rfl rfl

private theorem rec_6_12_2369_0 : fastPhase (bank 6 12).shape 179798 2369 31 1 6 1 0 = 143471004988732444759887 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_6_12_2369_0_join1

private theorem rec_6_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2369 31 1 6 1 1) 0 128 = 134386838564389728434208 := by decide +kernel
private theorem rec_6_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2369 31 1 6 1 1) 128 128 = 7386116818859037024246 := by decide +kernel
private theorem rec_6_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2369 31 1 6 1 1) 256 22 = 0 := by decide +kernel
private theorem rec_6_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2369 31 1 6 1 1) 128 150 = 7386116818859037024246 :=
  phaseBlock_append rec_6_12_2369_1_part1 rec_6_12_2369_1_part2 rfl rfl rfl
private theorem rec_6_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 6 12).shape 179798 2369 31 1 6 1 1) 0 278 = 141772955383248765458454 :=
  phaseBlock_append rec_6_12_2369_1_part0 rec_6_12_2369_1_join0 rfl rfl rfl

private theorem rec_6_12_2369_1 : fastPhase (bank 6 12).shape 179798 2369 31 1 6 1 1 = 141772955383248765458454 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_6_12_2369_1_join1

theorem receipt_6_12 : Checked (bank 6 12) 31 6 1 := by
  refine checked_from_values (bank 6 12) 31 6 1
    (P3_7_1.checked (bank 6 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_12_2368_0 rec_6_12_2368_1 rec_6_12_2369_0 rec_6_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2368 44 1 6 1 0) 0 128 = 647199214783297065973536 := by decide +kernel
private theorem rec_6_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2368 44 1 6 1 0) 128 128 = 136412552865311941231904 := by decide +kernel
private theorem rec_6_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2368 44 1 6 1 0) 256 114 = 0 := by decide +kernel
private theorem rec_6_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2368 44 1 6 1 0) 128 242 = 136412552865311941231904 :=
  phaseBlock_append rec_6_13_2368_0_part1 rec_6_13_2368_0_part2 rfl rfl rfl
private theorem rec_6_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2368 44 1 6 1 0) 0 370 = 783611767648609007205440 :=
  phaseBlock_append rec_6_13_2368_0_part0 rec_6_13_2368_0_join0 rfl rfl rfl

private theorem rec_6_13_2368_0 : fastPhase (bank 6 13).shape 179798 2368 44 1 6 1 0 = 783611767648609007205440 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_6_13_2368_0_join1

private theorem rec_6_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2368 44 1 6 1 1) 0 128 = 643125424666822321697760 := by decide +kernel
private theorem rec_6_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2368 44 1 6 1 1) 128 128 = 133520113873334863154766 := by decide +kernel
private theorem rec_6_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2368 44 1 6 1 1) 256 114 = 0 := by decide +kernel
private theorem rec_6_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2368 44 1 6 1 1) 128 242 = 133520113873334863154766 :=
  phaseBlock_append rec_6_13_2368_1_part1 rec_6_13_2368_1_part2 rfl rfl rfl
private theorem rec_6_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2368 44 1 6 1 1) 0 370 = 776645538540157184852526 :=
  phaseBlock_append rec_6_13_2368_1_part0 rec_6_13_2368_1_join0 rfl rfl rfl

private theorem rec_6_13_2368_1 : fastPhase (bank 6 13).shape 179798 2368 44 1 6 1 1 = 776645538540157184852526 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_6_13_2368_1_join1

private theorem rec_6_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2369 44 1 6 1 0) 0 128 = 647202565403590709666880 := by decide +kernel
private theorem rec_6_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2369 44 1 6 1 0) 128 128 = 136412625368149364209327 := by decide +kernel
private theorem rec_6_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2369 44 1 6 1 0) 256 114 = 0 := by decide +kernel
private theorem rec_6_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2369 44 1 6 1 0) 128 242 = 136412625368149364209327 :=
  phaseBlock_append rec_6_13_2369_0_part1 rec_6_13_2369_0_part2 rfl rfl rfl
private theorem rec_6_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2369 44 1 6 1 0) 0 370 = 783615190771740073876207 :=
  phaseBlock_append rec_6_13_2369_0_part0 rec_6_13_2369_0_join0 rfl rfl rfl

private theorem rec_6_13_2369_0 : fastPhase (bank 6 13).shape 179798 2369 44 1 6 1 0 = 783615190771740073876207 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_6_13_2369_0_join1

private theorem rec_6_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2369 44 1 6 1 1) 0 128 = 643128730763802948637056 := by decide +kernel
private theorem rec_6_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2369 44 1 6 1 1) 128 128 = 133520183478570398095839 := by decide +kernel
private theorem rec_6_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2369 44 1 6 1 1) 256 114 = 0 := by decide +kernel
private theorem rec_6_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2369 44 1 6 1 1) 128 242 = 133520183478570398095839 :=
  phaseBlock_append rec_6_13_2369_1_part1 rec_6_13_2369_1_part2 rfl rfl rfl
private theorem rec_6_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 6 13).shape 179798 2369 44 1 6 1 1) 0 370 = 776648914242373346732895 :=
  phaseBlock_append rec_6_13_2369_1_part0 rec_6_13_2369_1_join0 rfl rfl rfl

private theorem rec_6_13_2369_1 : fastPhase (bank 6 13).shape 179798 2369 44 1 6 1 1 = 776648914242373346732895 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_6_13_2369_1_join1

theorem receipt_6_13 : Checked (bank 6 13) 44 6 1 := by
  refine checked_from_values (bank 6 13) 44 6 1
    (P3_7_1.checked (bank 6 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_13_2368_0 rec_6_13_2368_1 rec_6_13_2369_0 rec_6_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 0 128 = 12007518171697668126672576 := by decide +kernel
private theorem rec_6_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 128 128 = 7402323112564548344170176 := by decide +kernel
private theorem rec_6_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 256 128 = 2844241044305306886768320 := by decide +kernel
private theorem rec_6_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 384 128 = 129958862054972136909562 := by decide +kernel
private theorem rec_6_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 512 128 = 0 := by decide +kernel
private theorem rec_6_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 640 38 = 0 := by decide +kernel
private theorem rec_6_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 128 256 = 10246564156869855230938496 :=
  phaseBlock_append rec_6_14_2368_0_part1 rec_6_14_2368_0_part2 rfl rfl rfl
private theorem rec_6_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 0 384 = 22254082328567523357611072 :=
  phaseBlock_append rec_6_14_2368_0_part0 rec_6_14_2368_0_join0 rfl rfl rfl
private theorem rec_6_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 512 166 = 0 :=
  phaseBlock_append rec_6_14_2368_0_part4 rec_6_14_2368_0_part5 rfl rfl rfl
private theorem rec_6_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 384 294 = 129958862054972136909562 :=
  phaseBlock_append rec_6_14_2368_0_part3 rec_6_14_2368_0_join2 rfl rfl rfl
private theorem rec_6_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 0) 0 678 = 22384041190622495494520634 :=
  phaseBlock_append rec_6_14_2368_0_join1 rec_6_14_2368_0_join3 rfl rfl rfl

private theorem rec_6_14_2368_0 : fastPhase (bank 6 14).shape 179798 2368 76 1 6 1 0 = 22384041190622495494520634 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_6_14_2368_0_join4

private theorem rec_6_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 0 128 = 11974767239967223522362688 := by decide +kernel
private theorem rec_6_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 128 128 = 7365110714914010778748224 := by decide +kernel
private theorem rec_6_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 256 128 = 2811997372760013273564480 := by decide +kernel
private theorem rec_6_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 384 128 = 123208186298024286538038 := by decide +kernel
private theorem rec_6_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 512 128 = 0 := by decide +kernel
private theorem rec_6_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 640 38 = 0 := by decide +kernel
private theorem rec_6_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 128 256 = 10177108087674024052312704 :=
  phaseBlock_append rec_6_14_2368_1_part1 rec_6_14_2368_1_part2 rfl rfl rfl
private theorem rec_6_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 0 384 = 22151875327641247574675392 :=
  phaseBlock_append rec_6_14_2368_1_part0 rec_6_14_2368_1_join0 rfl rfl rfl
private theorem rec_6_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 512 166 = 0 :=
  phaseBlock_append rec_6_14_2368_1_part4 rec_6_14_2368_1_part5 rfl rfl rfl
private theorem rec_6_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 384 294 = 123208186298024286538038 :=
  phaseBlock_append rec_6_14_2368_1_part3 rec_6_14_2368_1_join2 rfl rfl rfl
private theorem rec_6_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2368 76 1 6 1 1) 0 678 = 22275083513939271861213430 :=
  phaseBlock_append rec_6_14_2368_1_join1 rec_6_14_2368_1_join3 rfl rfl rfl

private theorem rec_6_14_2368_1 : fastPhase (bank 6 14).shape 179798 2368 76 1 6 1 1 = 22275083513939271861213430 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_6_14_2368_1_join4

private theorem rec_6_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 0 128 = 12007595291218429503110016 := by decide +kernel
private theorem rec_6_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 128 128 = 7402343762497092868717440 := by decide +kernel
private theorem rec_6_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 256 128 = 2844242069656493879327616 := by decide +kernel
private theorem rec_6_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 384 128 = 129958713709708010966136 := by decide +kernel
private theorem rec_6_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 512 128 = 0 := by decide +kernel
private theorem rec_6_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 640 38 = 0 := by decide +kernel
private theorem rec_6_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 128 256 = 10246585832153586748045056 :=
  phaseBlock_append rec_6_14_2369_0_part1 rec_6_14_2369_0_part2 rfl rfl rfl
private theorem rec_6_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 0 384 = 22254181123372016251155072 :=
  phaseBlock_append rec_6_14_2369_0_part0 rec_6_14_2369_0_join0 rfl rfl rfl
private theorem rec_6_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 512 166 = 0 :=
  phaseBlock_append rec_6_14_2369_0_part4 rec_6_14_2369_0_part5 rfl rfl rfl
private theorem rec_6_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 384 294 = 129958713709708010966136 :=
  phaseBlock_append rec_6_14_2369_0_part3 rec_6_14_2369_0_join2 rfl rfl rfl
private theorem rec_6_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 0) 0 678 = 22384139837081724262121208 :=
  phaseBlock_append rec_6_14_2369_0_join1 rec_6_14_2369_0_join3 rfl rfl rfl

private theorem rec_6_14_2369_0 : fastPhase (bank 6 14).shape 179798 2369 76 1 6 1 0 = 22384139837081724262121208 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_6_14_2369_0_join4

private theorem rec_6_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 0 128 = 11974843851318471676250240 := by decide +kernel
private theorem rec_6_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 128 128 = 7365131152424473357977728 := by decide +kernel
private theorem rec_6_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 256 128 = 2811998364177921958365312 := by decide +kernel
private theorem rec_6_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 384 128 = 123208045046986249666024 := by decide +kernel
private theorem rec_6_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 512 128 = 0 := by decide +kernel
private theorem rec_6_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 640 38 = 0 := by decide +kernel
private theorem rec_6_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 128 256 = 10177129516602395316343040 :=
  phaseBlock_append rec_6_14_2369_1_part1 rec_6_14_2369_1_part2 rfl rfl rfl
private theorem rec_6_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 0 384 = 22151973367920866992593280 :=
  phaseBlock_append rec_6_14_2369_1_part0 rec_6_14_2369_1_join0 rfl rfl rfl
private theorem rec_6_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 512 166 = 0 :=
  phaseBlock_append rec_6_14_2369_1_part4 rec_6_14_2369_1_part5 rfl rfl rfl
private theorem rec_6_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 384 294 = 123208045046986249666024 :=
  phaseBlock_append rec_6_14_2369_1_part3 rec_6_14_2369_1_join2 rfl rfl rfl
private theorem rec_6_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 6 14).shape 179798 2369 76 1 6 1 1) 0 678 = 22275181412967853242259304 :=
  phaseBlock_append rec_6_14_2369_1_join1 rec_6_14_2369_1_join3 rfl rfl rfl

private theorem rec_6_14_2369_1 : fastPhase (bank 6 14).shape 179798 2369 76 1 6 1 1 = 22275181412967853242259304 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_6_14_2369_1_join4

theorem receipt_6_14 : Checked (bank 6 14) 76 6 1 := by
  refine checked_from_values (bank 6 14) 76 6 1
    (P3_7_1.checked (bank 6 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_14_2368_0 rec_6_14_2368_1 rec_6_14_2369_0 rec_6_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 0 128 = 57297378339357672200586656 := by decide +kernel
private theorem rec_6_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 128 128 = 42395151571019603273790880 := by decide +kernel
private theorem rec_6_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 256 128 = 26433132087675596908045728 := by decide +kernel
private theorem rec_6_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 384 128 = 11571259365138499295122848 := by decide +kernel
private theorem rec_6_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 512 128 = 1208996960553537264209492 := by decide +kernel
private theorem rec_6_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 640 128 = 0 := by decide +kernel
private theorem rec_6_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 768 128 = 0 := by decide +kernel
private theorem rec_6_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 896 29 = 0 := by decide +kernel
private theorem rec_6_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 0 256 = 99692529910377275474377536 :=
  phaseBlock_append rec_6_15_2368_0_part0 rec_6_15_2368_0_part1 rfl rfl rfl
private theorem rec_6_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 256 256 = 38004391452814096203168576 :=
  phaseBlock_append rec_6_15_2368_0_part2 rec_6_15_2368_0_part3 rfl rfl rfl
private theorem rec_6_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 0 512 = 137696921363191371677546112 :=
  phaseBlock_append rec_6_15_2368_0_join0 rec_6_15_2368_0_join1 rfl rfl rfl
private theorem rec_6_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 512 256 = 1208996960553537264209492 :=
  phaseBlock_append rec_6_15_2368_0_part4 rec_6_15_2368_0_part5 rfl rfl rfl
private theorem rec_6_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 768 157 = 0 :=
  phaseBlock_append rec_6_15_2368_0_part6 rec_6_15_2368_0_part7 rfl rfl rfl
private theorem rec_6_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 512 413 = 1208996960553537264209492 :=
  phaseBlock_append rec_6_15_2368_0_join3 rec_6_15_2368_0_join4 rfl rfl rfl
private theorem rec_6_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 0) 0 925 = 138905918323744908941755604 :=
  phaseBlock_append rec_6_15_2368_0_join2 rec_6_15_2368_0_join5 rfl rfl rfl

private theorem rec_6_15_2368_0 : fastPhase (bank 6 15).shape 179798 2368 105 1 6 1 0 = 138905918323744908941755604 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_6_15_2368_0_join6

private theorem rec_6_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 0 128 = 57191775792769717956181920 := by decide +kernel
private theorem rec_6_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 128 128 = 42272353731010857315962784 := by decide +kernel
private theorem rec_6_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 256 128 = 26310344473259730487746464 := by decide +kernel
private theorem rec_6_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 384 128 = 11465183826597980437131168 := by decide +kernel
private theorem rec_6_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 512 128 = 1170040875175747518336631 := by decide +kernel
private theorem rec_6_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 640 128 = 0 := by decide +kernel
private theorem rec_6_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 768 128 = 0 := by decide +kernel
private theorem rec_6_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 896 29 = 0 := by decide +kernel
private theorem rec_6_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 0 256 = 99464129523780575272144704 :=
  phaseBlock_append rec_6_15_2368_1_part0 rec_6_15_2368_1_part1 rfl rfl rfl
private theorem rec_6_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 256 256 = 37775528299857710924877632 :=
  phaseBlock_append rec_6_15_2368_1_part2 rec_6_15_2368_1_part3 rfl rfl rfl
private theorem rec_6_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 0 512 = 137239657823638286197022336 :=
  phaseBlock_append rec_6_15_2368_1_join0 rec_6_15_2368_1_join1 rfl rfl rfl
private theorem rec_6_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 512 256 = 1170040875175747518336631 :=
  phaseBlock_append rec_6_15_2368_1_part4 rec_6_15_2368_1_part5 rfl rfl rfl
private theorem rec_6_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 768 157 = 0 :=
  phaseBlock_append rec_6_15_2368_1_part6 rec_6_15_2368_1_part7 rfl rfl rfl
private theorem rec_6_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 512 413 = 1170040875175747518336631 :=
  phaseBlock_append rec_6_15_2368_1_join3 rec_6_15_2368_1_join4 rfl rfl rfl
private theorem rec_6_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2368 105 1 6 1 1) 0 925 = 138409698698814033715358967 :=
  phaseBlock_append rec_6_15_2368_1_join2 rec_6_15_2368_1_join5 rfl rfl rfl

private theorem rec_6_15_2368_1 : fastPhase (bank 6 15).shape 179798 2368 105 1 6 1 1 = 138409698698814033715358967 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_6_15_2368_1_join6

private theorem rec_6_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 0 128 = 57297774972172598115602016 := by decide +kernel
private theorem rec_6_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 128 128 = 42395319484970277741731424 := by decide +kernel
private theorem rec_6_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 256 128 = 26433178593418783356464736 := by decide +kernel
private theorem rec_6_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 384 128 = 11571260394279685801655904 := by decide +kernel
private theorem rec_6_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 512 128 = 1208995686047731017376857 := by decide +kernel
private theorem rec_6_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 640 128 = 0 := by decide +kernel
private theorem rec_6_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 768 128 = 0 := by decide +kernel
private theorem rec_6_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 896 29 = 0 := by decide +kernel
private theorem rec_6_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 0 256 = 99693094457142875857333440 :=
  phaseBlock_append rec_6_15_2369_0_part0 rec_6_15_2369_0_part1 rfl rfl rfl
private theorem rec_6_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 256 256 = 38004438987698469158120640 :=
  phaseBlock_append rec_6_15_2369_0_part2 rec_6_15_2369_0_part3 rfl rfl rfl
private theorem rec_6_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 0 512 = 137697533444841345015454080 :=
  phaseBlock_append rec_6_15_2369_0_join0 rec_6_15_2369_0_join1 rfl rfl rfl
private theorem rec_6_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 512 256 = 1208995686047731017376857 :=
  phaseBlock_append rec_6_15_2369_0_part4 rec_6_15_2369_0_part5 rfl rfl rfl
private theorem rec_6_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 768 157 = 0 :=
  phaseBlock_append rec_6_15_2369_0_part6 rec_6_15_2369_0_part7 rfl rfl rfl
private theorem rec_6_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 512 413 = 1208995686047731017376857 :=
  phaseBlock_append rec_6_15_2369_0_join3 rec_6_15_2369_0_join4 rfl rfl rfl
private theorem rec_6_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 0) 0 925 = 138906529130889076032830937 :=
  phaseBlock_append rec_6_15_2369_0_join2 rec_6_15_2369_0_join5 rfl rfl rfl

private theorem rec_6_15_2369_0 : fastPhase (bank 6 15).shape 179798 2369 105 1 6 1 0 = 138906529130889076032830937 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_6_15_2369_0_join6

private theorem rec_6_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 0 128 = 57192170575504642440840672 := by decide +kernel
private theorem rec_6_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 128 128 = 42272520597287625007486432 := by decide +kernel
private theorem rec_6_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 256 128 = 26310390519591254228952544 := by decide +kernel
private theorem rec_6_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 384 128 = 11465184776663045954860512 := by decide +kernel
private theorem rec_6_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 512 128 = 1170039637791279119179231 := by decide +kernel
private theorem rec_6_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 640 128 = 0 := by decide +kernel
private theorem rec_6_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 768 128 = 0 := by decide +kernel
private theorem rec_6_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 896 29 = 0 := by decide +kernel
private theorem rec_6_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 0 256 = 99464691172792267448327104 :=
  phaseBlock_append rec_6_15_2369_1_part0 rec_6_15_2369_1_part1 rfl rfl rfl
private theorem rec_6_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 256 256 = 37775575296254300183813056 :=
  phaseBlock_append rec_6_15_2369_1_part2 rec_6_15_2369_1_part3 rfl rfl rfl
private theorem rec_6_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 0 512 = 137240266469046567632140160 :=
  phaseBlock_append rec_6_15_2369_1_join0 rec_6_15_2369_1_join1 rfl rfl rfl
private theorem rec_6_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 512 256 = 1170039637791279119179231 :=
  phaseBlock_append rec_6_15_2369_1_part4 rec_6_15_2369_1_part5 rfl rfl rfl
private theorem rec_6_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 768 157 = 0 :=
  phaseBlock_append rec_6_15_2369_1_part6 rec_6_15_2369_1_part7 rfl rfl rfl
private theorem rec_6_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 512 413 = 1170039637791279119179231 :=
  phaseBlock_append rec_6_15_2369_1_join3 rec_6_15_2369_1_join4 rfl rfl rfl
private theorem rec_6_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 6 15).shape 179798 2369 105 1 6 1 1) 0 925 = 138410306106837846751319391 :=
  phaseBlock_append rec_6_15_2369_1_join2 rec_6_15_2369_1_join5 rfl rfl rfl

private theorem rec_6_15_2369_1 : fastPhase (bank 6 15).shape 179798 2369 105 1 6 1 1 = 138410306106837846751319391 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_6_15_2369_1_join6

theorem receipt_6_15 : Checked (bank 6 15) 105 6 1 := by
  refine checked_from_values (bank 6 15) 105 6 1
    (P3_7_1.checked (bank 6 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_15_2368_0 rec_6_15_2368_1 rec_6_15_2369_0 rec_6_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_6_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 0 128 = 97999865927812669353886976 := by decide +kernel
private theorem rec_6_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 128 128 = 72643292614203136335357184 := by decide +kernel
private theorem rec_6_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 256 128 = 45373903432157338595247360 := by decide +kernel
private theorem rec_6_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 384 128 = 19897181951855382411699456 := by decide +kernel
private theorem rec_6_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 512 128 = 2081835581479624309957130 := by decide +kernel
private theorem rec_6_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 640 128 = 0 := by decide +kernel
private theorem rec_6_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 768 128 = 0 := by decide +kernel
private theorem rec_6_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 896 29 = 0 := by decide +kernel
private theorem rec_6_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 0 256 = 170643158542015805689244160 :=
  phaseBlock_append rec_6_16_2368_0_part0 rec_6_16_2368_0_part1 rfl rfl rfl
private theorem rec_6_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 256 256 = 65271085384012721006946816 :=
  phaseBlock_append rec_6_16_2368_0_part2 rec_6_16_2368_0_part3 rfl rfl rfl
private theorem rec_6_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 0 512 = 235914243926028526696190976 :=
  phaseBlock_append rec_6_16_2368_0_join0 rec_6_16_2368_0_join1 rfl rfl rfl
private theorem rec_6_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 512 256 = 2081835581479624309957130 :=
  phaseBlock_append rec_6_16_2368_0_part4 rec_6_16_2368_0_part5 rfl rfl rfl
private theorem rec_6_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 768 157 = 0 :=
  phaseBlock_append rec_6_16_2368_0_part6 rec_6_16_2368_0_part7 rfl rfl rfl
private theorem rec_6_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 512 413 = 2081835581479624309957130 :=
  phaseBlock_append rec_6_16_2368_0_join3 rec_6_16_2368_0_join4 rfl rfl rfl
private theorem rec_6_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 0) 0 925 = 237996079507508151006148106 :=
  phaseBlock_append rec_6_16_2368_0_join2 rec_6_16_2368_0_join5 rfl rfl rfl

private theorem rec_6_16_2368_0 : fastPhase (bank 6 16).shape 179798 2368 138 1 6 1 0 = 237996079507508151006148106 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_6_16_2368_0_join6

private theorem rec_6_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 0 128 = 97820644080073058072355648 := by decide +kernel
private theorem rec_6_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 128 128 = 72433902517261746144568128 := by decide +kernel
private theorem rec_6_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 256 128 = 45163758591842416454361920 := by decide +kernel
private theorem rec_6_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 384 128 = 19715036175399085554164544 := by decide +kernel
private theorem rec_6_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 512 128 = 2014775631657596689357846 := by decide +kernel
private theorem rec_6_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 640 128 = 0 := by decide +kernel
private theorem rec_6_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 768 128 = 0 := by decide +kernel
private theorem rec_6_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 896 29 = 0 := by decide +kernel
private theorem rec_6_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 0 256 = 170254546597334804216923776 :=
  phaseBlock_append rec_6_16_2368_1_part0 rec_6_16_2368_1_part1 rfl rfl rfl
private theorem rec_6_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 256 256 = 64878794767241502008526464 :=
  phaseBlock_append rec_6_16_2368_1_part2 rec_6_16_2368_1_part3 rfl rfl rfl
private theorem rec_6_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 0 512 = 235133341364576306225450240 :=
  phaseBlock_append rec_6_16_2368_1_join0 rec_6_16_2368_1_join1 rfl rfl rfl
private theorem rec_6_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 512 256 = 2014775631657596689357846 :=
  phaseBlock_append rec_6_16_2368_1_part4 rec_6_16_2368_1_part5 rfl rfl rfl
private theorem rec_6_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 768 157 = 0 :=
  phaseBlock_append rec_6_16_2368_1_part6 rec_6_16_2368_1_part7 rfl rfl rfl
private theorem rec_6_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 512 413 = 2014775631657596689357846 :=
  phaseBlock_append rec_6_16_2368_1_join3 rec_6_16_2368_1_join4 rfl rfl rfl
private theorem rec_6_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2368 138 1 6 1 1) 0 925 = 237148116996233902914808086 :=
  phaseBlock_append rec_6_16_2368_1_join2 rec_6_16_2368_1_join5 rfl rfl rfl

private theorem rec_6_16_2368_1 : fastPhase (bank 6 16).shape 179798 2368 138 1 6 1 1 = 237148116996233902914808086 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_6_16_2368_1_join6

private theorem rec_6_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 0 128 = 98000520018225961882333056 := by decide +kernel
private theorem rec_6_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 128 128 = 72643564813952808657563520 := by decide +kernel
private theorem rec_6_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 256 128 = 45373974742339225171963776 := by decide +kernel
private theorem rec_6_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 384 128 = 19897180380735518504529792 := by decide +kernel
private theorem rec_6_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 512 128 = 2081833066683818074314186 := by decide +kernel
private theorem rec_6_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 640 128 = 0 := by decide +kernel
private theorem rec_6_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 768 128 = 0 := by decide +kernel
private theorem rec_6_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 896 29 = 0 := by decide +kernel
private theorem rec_6_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 0 256 = 170644084832178770539896576 :=
  phaseBlock_append rec_6_16_2369_0_part0 rec_6_16_2369_0_part1 rfl rfl rfl
private theorem rec_6_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 256 256 = 65271155123074743676493568 :=
  phaseBlock_append rec_6_16_2369_0_part2 rec_6_16_2369_0_part3 rfl rfl rfl
private theorem rec_6_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 0 512 = 235915239955253514216390144 :=
  phaseBlock_append rec_6_16_2369_0_join0 rec_6_16_2369_0_join1 rfl rfl rfl
private theorem rec_6_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 512 256 = 2081833066683818074314186 :=
  phaseBlock_append rec_6_16_2369_0_part4 rec_6_16_2369_0_part5 rfl rfl rfl
private theorem rec_6_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 768 157 = 0 :=
  phaseBlock_append rec_6_16_2369_0_part6 rec_6_16_2369_0_part7 rfl rfl rfl
private theorem rec_6_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 512 413 = 2081833066683818074314186 :=
  phaseBlock_append rec_6_16_2369_0_join3 rec_6_16_2369_0_join4 rfl rfl rfl
private theorem rec_6_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 0) 0 925 = 237997073021937332290704330 :=
  phaseBlock_append rec_6_16_2369_0_join2 rec_6_16_2369_0_join5 rfl rfl rfl

private theorem rec_6_16_2369_0 : fastPhase (bank 6 16).shape 179798 2369 138 1 6 1 0 = 237997073021937332290704330 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_6_16_2369_0_join6

private theorem rec_6_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 0 128 = 97821295091566997514794880 := by decide +kernel
private theorem rec_6_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 128 128 = 72434172987761764316338048 := by decide +kernel
private theorem rec_6_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 256 128 = 45163829162160169838376832 := by decide +kernel
private theorem rec_6_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 384 128 = 19715034501626347596289920 := by decide +kernel
private theorem rec_6_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 512 128 = 2014773191290318422322990 := by decide +kernel
private theorem rec_6_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 640 128 = 0 := by decide +kernel
private theorem rec_6_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 768 128 = 0 := by decide +kernel
private theorem rec_6_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 896 29 = 0 := by decide +kernel
private theorem rec_6_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 0 256 = 170255468079328761831132928 :=
  phaseBlock_append rec_6_16_2369_1_part0 rec_6_16_2369_1_part1 rfl rfl rfl
private theorem rec_6_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 256 256 = 64878863663786517434666752 :=
  phaseBlock_append rec_6_16_2369_1_part2 rec_6_16_2369_1_part3 rfl rfl rfl
private theorem rec_6_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 0 512 = 235134331743115279265799680 :=
  phaseBlock_append rec_6_16_2369_1_join0 rec_6_16_2369_1_join1 rfl rfl rfl
private theorem rec_6_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 512 256 = 2014773191290318422322990 :=
  phaseBlock_append rec_6_16_2369_1_part4 rec_6_16_2369_1_part5 rfl rfl rfl
private theorem rec_6_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 768 157 = 0 :=
  phaseBlock_append rec_6_16_2369_1_part6 rec_6_16_2369_1_part7 rfl rfl rfl
private theorem rec_6_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 512 413 = 2014773191290318422322990 :=
  phaseBlock_append rec_6_16_2369_1_join3 rec_6_16_2369_1_join4 rfl rfl rfl
private theorem rec_6_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 6 16).shape 179798 2369 138 1 6 1 1) 0 925 = 237149104934405597688122670 :=
  phaseBlock_append rec_6_16_2369_1_join2 rec_6_16_2369_1_join5 rfl rfl rfl

private theorem rec_6_16_2369_1 : fastPhase (bank 6 16).shape 179798 2369 138 1 6 1 1 = 237149104934405597688122670 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_6_16_2369_1_join6

theorem receipt_6_16 : Checked (bank 6 16) 138 6 1 := by
  refine checked_from_values (bank 6 16) 138 6 1
    (P3_7_1.checked (bank 6 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_6_16_2368_0 rec_6_16_2368_1 rec_6_16_2369_0 rec_6_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect6_checked (i : Fin 17) (hi : i ≠ 0) :
    Checked (bank 6 i) (reserve i) (excess 6) (seed 6) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact receipt_6_1
  · exact receipt_6_2
  · exact receipt_6_3
  · exact receipt_6_4
  · exact receipt_6_5
  · exact receipt_6_6
  · exact receipt_6_7
  · exact receipt_6_8
  · exact receipt_6_9
  · exact receipt_6_10
  · exact receipt_6_11
  · exact receipt_6_12
  · exact receipt_6_13
  · exact receipt_6_14
  · exact receipt_6_15
  · exact receipt_6_16

end Lower6961.Lo.RescueSource
