import ProximityPrize.SubmissionLower.R6961LoRescueSourceSchedule
import ProximityPrize.SubmissionLower.R6963LoFastLayerNat
import ProximityPrize.SubmissionLower.R6961LoRescuePoolMoments0
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt0
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt1
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt2
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt3
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt4
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt5
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt6
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt7
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt8
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt9
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt10
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt11

set_option Elab.async false

-- merged module R6961LoRescueSourceReceipt12
section Merged_R6961LoRescueSourceReceipt12

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


private theorem rec_12_0_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2368 0 1 6 11 0) 0 128 = 390755049862724342152 := by decide +kernel
private theorem rec_12_0_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2368 0 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_0_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2368 0 1 6 11 0) 0 130 = 390755049862724342152 :=
  phaseBlock_append rec_12_0_2368_0_part0 rec_12_0_2368_0_part1 rfl rfl rfl

private theorem rec_12_0_2368_0 : fastPhase (bank 12 0).shape 179798 2368 0 1 6 11 0 = 390755049862724342152 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_0_2368_0_join0

private theorem rec_12_0_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2368 0 1 6 11 1) 0 128 = 379096435546808027496 := by decide +kernel
private theorem rec_12_0_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2368 0 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_0_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2368 0 1 6 11 1) 0 130 = 379096435546808027496 :=
  phaseBlock_append rec_12_0_2368_1_part0 rec_12_0_2368_1_part1 rfl rfl rfl

private theorem rec_12_0_2368_1 : fastPhase (bank 12 0).shape 179798 2368 0 1 6 11 1 = 379096435546808027496 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_0_2368_1_join0

private theorem rec_12_0_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2369 0 1 6 11 0) 0 128 = 390757184931989986292 := by decide +kernel
private theorem rec_12_0_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2369 0 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_0_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2369 0 1 6 11 0) 0 130 = 390757184931989986292 :=
  phaseBlock_append rec_12_0_2369_0_part0 rec_12_0_2369_0_part1 rfl rfl rfl

private theorem rec_12_0_2369_0 : fastPhase (bank 12 0).shape 179798 2369 0 1 6 11 0 = 390757184931989986292 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_0_2369_0_join0

private theorem rec_12_0_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2369 0 1 6 11 1) 0 128 = 379098477641038918854 := by decide +kernel
private theorem rec_12_0_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2369 0 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_0_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 0).shape 179798 2369 0 1 6 11 1) 0 130 = 379098477641038918854 :=
  phaseBlock_append rec_12_0_2369_1_part0 rec_12_0_2369_1_part1 rfl rfl rfl

private theorem rec_12_0_2369_1 : fastPhase (bank 12 0).shape 179798 2369 0 1 6 11 1 = 379098477641038918854 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_0_2369_1_join0

theorem receipt_12_0 : Checked (bank 12 0) 0 6 11 := by
  refine checked_from_values (bank 12 0) 0 6 11
    (P3_7_1.checked (bank 12 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_0_2368_0 rec_12_0_2368_1 rec_12_0_2369_0 rec_12_0_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2368 1 1 6 11 0) 0 128 = 425656233597370994120 := by decide +kernel
private theorem rec_12_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2368 1 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2368 1 1 6 11 0) 0 130 = 425656233597370994120 :=
  phaseBlock_append rec_12_1_2368_0_part0 rec_12_1_2368_0_part1 rfl rfl rfl

private theorem rec_12_1_2368_0 : fastPhase (bank 12 1).shape 179798 2368 1 1 6 11 0 = 425656233597370994120 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_1_2368_0_join0

private theorem rec_12_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2368 1 1 6 11 1) 0 128 = 413045762952451897768 := by decide +kernel
private theorem rec_12_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2368 1 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2368 1 1 6 11 1) 0 130 = 413045762952451897768 :=
  phaseBlock_append rec_12_1_2368_1_part0 rec_12_1_2368_1_part1 rfl rfl rfl

private theorem rec_12_1_2368_1 : fastPhase (bank 12 1).shape 179798 2368 1 1 6 11 1 = 413045762952451897768 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_1_2368_1_join0

private theorem rec_12_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2369 1 1 6 11 0) 0 128 = 425658532659263238426 := by decide +kernel
private theorem rec_12_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2369 1 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2369 1 1 6 11 0) 0 130 = 425658532659263238426 :=
  phaseBlock_append rec_12_1_2369_0_part0 rec_12_1_2369_0_part1 rfl rfl rfl

private theorem rec_12_1_2369_0 : fastPhase (bank 12 1).shape 179798 2369 1 1 6 11 0 = 425658532659263238426 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_1_2369_0_join0

private theorem rec_12_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2369 1 1 6 11 1) 0 128 = 413047962306170667060 := by decide +kernel
private theorem rec_12_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2369 1 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 1).shape 179798 2369 1 1 6 11 1) 0 130 = 413047962306170667060 :=
  phaseBlock_append rec_12_1_2369_1_part0 rec_12_1_2369_1_part1 rfl rfl rfl

private theorem rec_12_1_2369_1 : fastPhase (bank 12 1).shape 179798 2369 1 1 6 11 1 = 413047962306170667060 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_1_2369_1_join0

theorem receipt_12_1 : Checked (bank 12 1) 1 6 11 := by
  refine checked_from_values (bank 12 1) 1 6 11
    (P3_7_1.checked (bank 12 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_1_2368_0 rec_12_1_2368_1 rec_12_1_2369_0 rec_12_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2368 2 1 6 11 0) 0 128 = 465255072445774879254 := by decide +kernel
private theorem rec_12_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2368 2 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2368 2 1 6 11 0) 0 130 = 465255072445774879254 :=
  phaseBlock_append rec_12_2_2368_0_part0 rec_12_2_2368_0_part1 rfl rfl rfl

private theorem rec_12_2_2368_0 : fastPhase (bank 12 2).shape 179798 2368 2 1 6 11 0 = 465255072445774879254 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_2_2368_0_join0

private theorem rec_12_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2368 2 1 6 11 1) 0 128 = 451568644065869028062 := by decide +kernel
private theorem rec_12_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2368 2 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2368 2 1 6 11 1) 0 130 = 451568644065869028062 :=
  phaseBlock_append rec_12_2_2368_1_part0 rec_12_2_2368_1_part1 rfl rfl rfl

private theorem rec_12_2_2368_1 : fastPhase (bank 12 2).shape 179798 2368 2 1 6 11 1 = 451568644065869028062 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_2_2368_1_join0

private theorem rec_12_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2369 2 1 6 11 0) 0 128 = 465257556246084160860 := by decide +kernel
private theorem rec_12_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2369 2 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2369 2 1 6 11 0) 0 130 = 465257556246084160860 :=
  phaseBlock_append rec_12_2_2369_0_part0 rec_12_2_2369_0_part1 rfl rfl rfl

private theorem rec_12_2_2369_0 : fastPhase (bank 12 2).shape 179798 2369 2 1 6 11 0 = 465257556246084160860 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_2_2369_0_join0

private theorem rec_12_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2369 2 1 6 11 1) 0 128 = 451571020582903752034 := by decide +kernel
private theorem rec_12_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2369 2 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 2).shape 179798 2369 2 1 6 11 1) 0 130 = 451571020582903752034 :=
  phaseBlock_append rec_12_2_2369_1_part0 rec_12_2_2369_1_part1 rfl rfl rfl

private theorem rec_12_2_2369_1 : fastPhase (bank 12 2).shape 179798 2369 2 1 6 11 1 = 451571020582903752034 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_2_2369_1_join0

theorem receipt_12_2 : Checked (bank 12 2) 2 6 11 := by
  refine checked_from_values (bank 12 2) 2 6 11
    (P3_7_1.checked (bank 12 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_2_2368_0 rec_12_2_2368_1 rec_12_2_2369_0 rec_12_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2368 3 1 6 11 0) 0 128 = 510276215692781502769 := by decide +kernel
private theorem rec_12_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2368 3 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2368 3 1 6 11 0) 0 130 = 510276215692781502769 :=
  phaseBlock_append rec_12_3_2368_0_part0 rec_12_3_2368_0_part1 rfl rfl rfl

private theorem rec_12_3_2368_0 : fastPhase (bank 12 3).shape 179798 2368 3 1 6 11 0 = 510276215692781502769 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_3_2368_0_join0

private theorem rec_12_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2368 3 1 6 11 1) 0 128 = 495371035835878217257 := by decide +kernel
private theorem rec_12_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2368 3 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2368 3 1 6 11 1) 0 130 = 495371035835878217257 :=
  phaseBlock_append rec_12_3_2368_1_part0 rec_12_3_2368_1_part1 rfl rfl rfl

private theorem rec_12_3_2368_1 : fastPhase (bank 12 3).shape 179798 2368 3 1 6 11 1 = 495371035835878217257 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_3_2368_1_join0

private theorem rec_12_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2369 3 1 6 11 0) 0 128 = 510278907952668171198 := by decide +kernel
private theorem rec_12_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2369 3 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2369 3 1 6 11 0) 0 130 = 510278907952668171198 :=
  phaseBlock_append rec_12_3_2369_0_part0 rec_12_3_2369_0_part1 rfl rfl rfl

private theorem rec_12_3_2369_0 : fastPhase (bank 12 3).shape 179798 2369 3 1 6 11 0 = 510278907952668171198 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_3_2369_0_join0

private theorem rec_12_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2369 3 1 6 11 1) 0 128 = 495373612275402837852 := by decide +kernel
private theorem rec_12_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2369 3 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 3).shape 179798 2369 3 1 6 11 1) 0 130 = 495373612275402837852 :=
  phaseBlock_append rec_12_3_2369_1_part0 rec_12_3_2369_1_part1 rfl rfl rfl

private theorem rec_12_3_2369_1 : fastPhase (bank 12 3).shape 179798 2369 3 1 6 11 1 = 495373612275402837852 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_3_2369_1_join0

theorem receipt_12_3 : Checked (bank 12 3) 3 6 11 := by
  refine checked_from_values (bank 12 3) 3 6 11
    (P3_7_1.checked (bank 12 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_3_2368_0 rec_12_3_2368_1 rec_12_3_2369_0 rec_12_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2368 4 1 6 11 0) 0 128 = 561857408409412849636 := by decide +kernel
private theorem rec_12_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2368 4 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2368 4 1 6 11 0) 0 130 = 561857408409412849636 :=
  phaseBlock_append rec_12_4_2368_0_part0 rec_12_4_2368_0_part1 rfl rfl rfl

private theorem rec_12_4_2368_0 : fastPhase (bank 12 4).shape 179798 2368 4 1 6 11 0 = 561857408409412849636 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_4_2368_0_join0

private theorem rec_12_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2368 4 1 6 11 1) 0 128 = 545561053877550915964 := by decide +kernel
private theorem rec_12_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2368 4 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2368 4 1 6 11 1) 0 130 = 545561053877550915964 :=
  phaseBlock_append rec_12_4_2368_1_part0 rec_12_4_2368_1_part1 rfl rfl rfl

private theorem rec_12_4_2368_1 : fastPhase (bank 12 4).shape 179798 2368 4 1 6 11 1 = 545561053877550915964 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_4_2368_1_join0

private theorem rec_12_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2369 4 1 6 11 0) 0 128 = 561860337767056983564 := by decide +kernel
private theorem rec_12_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2369 4 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2369 4 1 6 11 0) 0 130 = 561860337767056983564 :=
  phaseBlock_append rec_12_4_2369_0_part0 rec_12_4_2369_0_part1 rfl rfl rfl

private theorem rec_12_4_2369_0 : fastPhase (bank 12 4).shape 179798 2369 4 1 6 11 0 = 561860337767056983564 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_4_2369_0_join0

private theorem rec_12_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2369 4 1 6 11 1) 0 128 = 545563857717367434738 := by decide +kernel
private theorem rec_12_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2369 4 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 4).shape 179798 2369 4 1 6 11 1) 0 130 = 545563857717367434738 :=
  phaseBlock_append rec_12_4_2369_1_part0 rec_12_4_2369_1_part1 rfl rfl rfl

private theorem rec_12_4_2369_1 : fastPhase (bank 12 4).shape 179798 2369 4 1 6 11 1 = 545563857717367434738 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_4_2369_1_join0

theorem receipt_12_4 : Checked (bank 12 4) 4 6 11 := by
  refine checked_from_values (bank 12 4) 4 6 11
    (P3_7_1.checked (bank 12 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_4_2368_0 rec_12_4_2368_1 rec_12_4_2369_0 rec_12_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2368 5 1 6 11 0) 0 128 = 621643280609484571977 := by decide +kernel
private theorem rec_12_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2368 5 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2368 5 1 6 11 0) 0 130 = 621643280609484571977 :=
  phaseBlock_append rec_12_5_2368_0_part0 rec_12_5_2368_0_part1 rfl rfl rfl

private theorem rec_12_5_2368_0 : fastPhase (bank 12 5).shape 179798 2368 5 1 6 11 0 = 621643280609484571977 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_5_2368_0_join0

private theorem rec_12_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2368 5 1 6 11 1) 0 128 = 603740426063464480121 := by decide +kernel
private theorem rec_12_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2368 5 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2368 5 1 6 11 1) 0 130 = 603740426063464480121 :=
  phaseBlock_append rec_12_5_2368_1_part0 rec_12_5_2368_1_part1 rfl rfl rfl

private theorem rec_12_5_2368_1 : fastPhase (bank 12 5).shape 179798 2368 5 1 6 11 1 = 603740426063464480121 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_5_2368_1_join0

private theorem rec_12_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2369 5 1 6 11 0) 0 128 = 621646482920229433212 := by decide +kernel
private theorem rec_12_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2369 5 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2369 5 1 6 11 0) 0 130 = 621646482920229433212 :=
  phaseBlock_append rec_12_5_2369_0_part0 rec_12_5_2369_0_part1 rfl rfl rfl

private theorem rec_12_5_2369_0 : fastPhase (bank 12 5).shape 179798 2369 5 1 6 11 0 = 621646482920229433212 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_5_2369_0_join0

private theorem rec_12_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2369 5 1 6 11 1) 0 128 = 603743491707662453524 := by decide +kernel
private theorem rec_12_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2369 5 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 5).shape 179798 2369 5 1 6 11 1) 0 130 = 603743491707662453524 :=
  phaseBlock_append rec_12_5_2369_1_part0 rec_12_5_2369_1_part1 rfl rfl rfl

private theorem rec_12_5_2369_1 : fastPhase (bank 12 5).shape 179798 2369 5 1 6 11 1 = 603743491707662453524 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_5_2369_1_join0

theorem receipt_12_5 : Checked (bank 12 5) 5 6 11 := by
  refine checked_from_values (bank 12 5) 5 6 11
    (P3_7_1.checked (bank 12 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_5_2368_0 rec_12_5_2368_1 rec_12_5_2369_0 rec_12_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2368 7 1 6 11 0) 0 128 = 771179430672787036019 := by decide +kernel
private theorem rec_12_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2368 7 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2368 7 1 6 11 0) 0 130 = 771179430672787036019 :=
  phaseBlock_append rec_12_6_2368_0_part0 rec_12_6_2368_0_part1 rfl rfl rfl

private theorem rec_12_6_2368_0 : fastPhase (bank 12 6).shape 179798 2368 7 1 6 11 0 = 771179430672787036019 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_6_2368_0_join0

private theorem rec_12_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2368 7 1 6 11 1) 0 128 = 749281131801227889043 := by decide +kernel
private theorem rec_12_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2368 7 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2368 7 1 6 11 1) 0 130 = 749281131801227889043 :=
  phaseBlock_append rec_12_6_2368_1_part0 rec_12_6_2368_1_part1 rfl rfl rfl

private theorem rec_12_6_2368_1 : fastPhase (bank 12 6).shape 179798 2368 7 1 6 11 1 = 749281131801227889043 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_6_2368_1_join0

private theorem rec_12_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2369 7 1 6 11 0) 0 128 = 771183307562963040508 := by decide +kernel
private theorem rec_12_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2369 7 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2369 7 1 6 11 0) 0 130 = 771183307562963040508 :=
  phaseBlock_append rec_12_6_2369_0_part0 rec_12_6_2369_0_part1 rfl rfl rfl

private theorem rec_12_6_2369_0 : fastPhase (bank 12 6).shape 179798 2369 7 1 6 11 0 = 771183307562963040508 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_6_2369_0_join0

private theorem rec_12_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2369 7 1 6 11 1) 0 128 = 749284844523911768660 := by decide +kernel
private theorem rec_12_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2369 7 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 6).shape 179798 2369 7 1 6 11 1) 0 130 = 749284844523911768660 :=
  phaseBlock_append rec_12_6_2369_1_part0 rec_12_6_2369_1_part1 rfl rfl rfl

private theorem rec_12_6_2369_1 : fastPhase (bank 12 6).shape 179798 2369 7 1 6 11 1 = 749284844523911768660 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_6_2369_1_join0

theorem receipt_12_6 : Checked (bank 12 6) 7 6 11 := by
  refine checked_from_values (bank 12 6) 7 6 11
    (P3_7_1.checked (bank 12 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_6_2368_0 rec_12_6_2368_1 rec_12_6_2369_0 rec_12_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2368 10 1 6 11 0) 0 128 = 1115520859615807595153 := by decide +kernel
private theorem rec_12_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2368 10 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2368 10 1 6 11 0) 0 130 = 1115520859615807595153 :=
  phaseBlock_append rec_12_7_2368_0_part0 rec_12_7_2368_0_part1 rfl rfl rfl

private theorem rec_12_7_2368_0 : fastPhase (bank 12 7).shape 179798 2368 10 1 6 11 0 = 1115520859615807595153 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_7_2368_0_join0

private theorem rec_12_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2368 10 1 6 11 1) 0 128 = 1084508644740947064841 := by decide +kernel
private theorem rec_12_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2368 10 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2368 10 1 6 11 1) 0 130 = 1084508644740947064841 :=
  phaseBlock_append rec_12_7_2368_1_part0 rec_12_7_2368_1_part1 rfl rfl rfl

private theorem rec_12_7_2368_1 : fastPhase (bank 12 7).shape 179798 2368 10 1 6 11 1 = 1084508644740947064841 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_7_2368_1_join0

private theorem rec_12_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2369 10 1 6 11 0) 0 128 = 1115526260764032006120 := by decide +kernel
private theorem rec_12_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2369 10 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2369 10 1 6 11 0) 0 130 = 1115526260764032006120 :=
  phaseBlock_append rec_12_7_2369_0_part0 rec_12_7_2369_0_part1 rfl rfl rfl

private theorem rec_12_7_2369_0 : fastPhase (bank 12 7).shape 179798 2369 10 1 6 11 0 = 1115526260764032006120 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_7_2369_0_join0

private theorem rec_12_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2369 10 1 6 11 1) 0 128 = 1084513819790411990124 := by decide +kernel
private theorem rec_12_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2369 10 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 7).shape 179798 2369 10 1 6 11 1) 0 130 = 1084513819790411990124 :=
  phaseBlock_append rec_12_7_2369_1_part0 rec_12_7_2369_1_part1 rfl rfl rfl

private theorem rec_12_7_2369_1 : fastPhase (bank 12 7).shape 179798 2369 10 1 6 11 1 = 1084513819790411990124 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_7_2369_1_join0

theorem receipt_12_7 : Checked (bank 12 7) 10 6 11 := by
  refine checked_from_values (bank 12 7) 10 6 11
    (P3_7_1.checked (bank 12 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_7_2368_0 rec_12_7_2368_1 rec_12_7_2369_0 rec_12_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2368 16 1 6 11 0) 0 128 = 8449476263338934070532 := by decide +kernel
private theorem rec_12_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2368 16 1 6 11 0) 128 63 = 0 := by decide +kernel
private theorem rec_12_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2368 16 1 6 11 0) 0 191 = 8449476263338934070532 :=
  phaseBlock_append rec_12_8_2368_0_part0 rec_12_8_2368_0_part1 rfl rfl rfl

private theorem rec_12_8_2368_0 : fastPhase (bank 12 8).shape 179798 2368 16 1 6 11 0 = 8449476263338934070532 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_12_8_2368_0_join0

private theorem rec_12_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2368 16 1 6 11 1) 0 128 = 8286616965558024448772 := by decide +kernel
private theorem rec_12_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2368 16 1 6 11 1) 128 63 = 0 := by decide +kernel
private theorem rec_12_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2368 16 1 6 11 1) 0 191 = 8286616965558024448772 :=
  phaseBlock_append rec_12_8_2368_1_part0 rec_12_8_2368_1_part1 rfl rfl rfl

private theorem rec_12_8_2368_1 : fastPhase (bank 12 8).shape 179798 2368 16 1 6 11 1 = 8286616965558024448772 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_12_8_2368_1_join0

private theorem rec_12_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2369 16 1 6 11 0) 0 128 = 8449516963877527099922 := by decide +kernel
private theorem rec_12_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2369 16 1 6 11 0) 128 63 = 0 := by decide +kernel
private theorem rec_12_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2369 16 1 6 11 0) 0 191 = 8449516963877527099922 :=
  phaseBlock_append rec_12_8_2369_0_part0 rec_12_8_2369_0_part1 rfl rfl rfl

private theorem rec_12_8_2369_0 : fastPhase (bank 12 8).shape 179798 2369 16 1 6 11 0 = 8449516963877527099922 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_12_8_2369_0_join0

private theorem rec_12_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2369 16 1 6 11 1) 0 128 = 8286656484551945186284 := by decide +kernel
private theorem rec_12_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2369 16 1 6 11 1) 128 63 = 0 := by decide +kernel
private theorem rec_12_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 8).shape 179798 2369 16 1 6 11 1) 0 191 = 8286656484551945186284 :=
  phaseBlock_append rec_12_8_2369_1_part0 rec_12_8_2369_1_part1 rfl rfl rfl

private theorem rec_12_8_2369_1 : fastPhase (bank 12 8).shape 179798 2369 16 1 6 11 1 = 8286656484551945186284 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_12_8_2369_1_join0

theorem receipt_12_8 : Checked (bank 12 8) 16 6 11 := by
  refine checked_from_values (bank 12 8) 16 6 11
    (P3_7_1.checked (bank 12 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_8_2368_0 rec_12_8_2368_1 rec_12_8_2369_0 rec_12_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2368 10 1 6 11 0) 0 128 = 1115520859615807595153 := by decide +kernel
private theorem rec_12_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2368 10 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2368 10 1 6 11 0) 0 130 = 1115520859615807595153 :=
  phaseBlock_append rec_12_9_2368_0_part0 rec_12_9_2368_0_part1 rfl rfl rfl

private theorem rec_12_9_2368_0 : fastPhase (bank 12 9).shape 179798 2368 10 1 6 11 0 = 1115520859615807595153 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_9_2368_0_join0

private theorem rec_12_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2368 10 1 6 11 1) 0 128 = 1084508644740947064841 := by decide +kernel
private theorem rec_12_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2368 10 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2368 10 1 6 11 1) 0 130 = 1084508644740947064841 :=
  phaseBlock_append rec_12_9_2368_1_part0 rec_12_9_2368_1_part1 rfl rfl rfl

private theorem rec_12_9_2368_1 : fastPhase (bank 12 9).shape 179798 2368 10 1 6 11 1 = 1084508644740947064841 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_9_2368_1_join0

private theorem rec_12_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2369 10 1 6 11 0) 0 128 = 1115526260764032006120 := by decide +kernel
private theorem rec_12_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2369 10 1 6 11 0) 128 2 = 0 := by decide +kernel
private theorem rec_12_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2369 10 1 6 11 0) 0 130 = 1115526260764032006120 :=
  phaseBlock_append rec_12_9_2369_0_part0 rec_12_9_2369_0_part1 rfl rfl rfl

private theorem rec_12_9_2369_0 : fastPhase (bank 12 9).shape 179798 2369 10 1 6 11 0 = 1115526260764032006120 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_9_2369_0_join0

private theorem rec_12_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2369 10 1 6 11 1) 0 128 = 1084513819790411990124 := by decide +kernel
private theorem rec_12_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2369 10 1 6 11 1) 128 2 = 0 := by decide +kernel
private theorem rec_12_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 9).shape 179798 2369 10 1 6 11 1) 0 130 = 1084513819790411990124 :=
  phaseBlock_append rec_12_9_2369_1_part0 rec_12_9_2369_1_part1 rfl rfl rfl

private theorem rec_12_9_2369_1 : fastPhase (bank 12 9).shape 179798 2369 10 1 6 11 1 = 1084513819790411990124 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_12_9_2369_1_join0

theorem receipt_12_9 : Checked (bank 12 9) 10 6 11 := by
  refine checked_from_values (bank 12 9) 10 6 11
    (P3_7_1.checked (bank 12 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_9_2368_0 rec_12_9_2368_1 rec_12_9_2369_0 rec_12_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2368 20 1 6 11 0) 0 128 = 11899613590737085887054 := by decide +kernel
private theorem rec_12_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2368 20 1 6 11 0) 128 63 = 0 := by decide +kernel
private theorem rec_12_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2368 20 1 6 11 0) 0 191 = 11899613590737085887054 :=
  phaseBlock_append rec_12_10_2368_0_part0 rec_12_10_2368_0_part1 rfl rfl rfl

private theorem rec_12_10_2368_0 : fastPhase (bank 12 10).shape 179798 2368 20 1 6 11 0 = 11899613590737085887054 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_12_10_2368_0_join0

private theorem rec_12_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2368 20 1 6 11 1) 0 128 = 11674619598808614124206 := by decide +kernel
private theorem rec_12_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2368 20 1 6 11 1) 128 63 = 0 := by decide +kernel
private theorem rec_12_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2368 20 1 6 11 1) 0 191 = 11674619598808614124206 :=
  phaseBlock_append rec_12_10_2368_1_part0 rec_12_10_2368_1_part1 rfl rfl rfl

private theorem rec_12_10_2368_1 : fastPhase (bank 12 10).shape 179798 2368 20 1 6 11 1 = 11674619598808614124206 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_12_10_2368_1_join0

private theorem rec_12_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2369 20 1 6 11 0) 0 128 = 11899668926170259510562 := by decide +kernel
private theorem rec_12_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2369 20 1 6 11 0) 128 63 = 0 := by decide +kernel
private theorem rec_12_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2369 20 1 6 11 0) 0 191 = 11899668926170259510562 :=
  phaseBlock_append rec_12_10_2369_0_part0 rec_12_10_2369_0_part1 rfl rfl rfl

private theorem rec_12_10_2369_0 : fastPhase (bank 12 10).shape 179798 2369 20 1 6 11 0 = 11899668926170259510562 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_12_10_2369_0_join0

private theorem rec_12_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2369 20 1 6 11 1) 0 128 = 11674673343849585935988 := by decide +kernel
private theorem rec_12_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2369 20 1 6 11 1) 128 63 = 0 := by decide +kernel
private theorem rec_12_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 10).shape 179798 2369 20 1 6 11 1) 0 191 = 11674673343849585935988 :=
  phaseBlock_append rec_12_10_2369_1_part0 rec_12_10_2369_1_part1 rfl rfl rfl

private theorem rec_12_10_2369_1 : fastPhase (bank 12 10).shape 179798 2369 20 1 6 11 1 = 11674673343849585935988 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_12_10_2369_1_join0

theorem receipt_12_10 : Checked (bank 12 10) 20 6 11 := by
  refine checked_from_values (bank 12 10) 20 6 11
    (P3_7_1.checked (bank 12 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_10_2368_0 rec_12_10_2368_1 rec_12_10_2369_0 rec_12_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2368 32 1 6 11 0) 0 128 = 94807444561930793371072 := by decide +kernel
private theorem rec_12_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2368 32 1 6 11 0) 128 128 = 4460810795509239659488 := by decide +kernel
private theorem rec_12_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2368 32 1 6 11 0) 256 22 = 0 := by decide +kernel
private theorem rec_12_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2368 32 1 6 11 0) 128 150 = 4460810795509239659488 :=
  phaseBlock_append rec_12_11_2368_0_part1 rec_12_11_2368_0_part2 rfl rfl rfl
private theorem rec_12_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2368 32 1 6 11 0) 0 278 = 99268255357440033030560 :=
  phaseBlock_append rec_12_11_2368_0_part0 rec_12_11_2368_0_join0 rfl rfl rfl

private theorem rec_12_11_2368_0 : fastPhase (bank 12 11).shape 179798 2368 32 1 6 11 0 = 99268255357440033030560 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_12_11_2368_0_join1

private theorem rec_12_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2368 32 1 6 11 1) 0 128 = 93720899046588784135680 := by decide +kernel
private theorem rec_12_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2368 32 1 6 11 1) 128 128 = 4242591308110074644774 := by decide +kernel
private theorem rec_12_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2368 32 1 6 11 1) 256 22 = 0 := by decide +kernel
private theorem rec_12_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2368 32 1 6 11 1) 128 150 = 4242591308110074644774 :=
  phaseBlock_append rec_12_11_2368_1_part1 rec_12_11_2368_1_part2 rfl rfl rfl
private theorem rec_12_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2368 32 1 6 11 1) 0 278 = 97963490354698858780454 :=
  phaseBlock_append rec_12_11_2368_1_part0 rec_12_11_2368_1_join0 rfl rfl rfl

private theorem rec_12_11_2368_1 : fastPhase (bank 12 11).shape 179798 2368 32 1 6 11 1 = 97963490354698858780454 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_12_11_2368_1_join1

private theorem rec_12_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2369 32 1 6 11 0) 0 128 = 94807901560567278313792 := by decide +kernel
private theorem rec_12_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2369 32 1 6 11 0) 128 128 = 4460809145548786202900 := by decide +kernel
private theorem rec_12_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2369 32 1 6 11 0) 256 22 = 0 := by decide +kernel
private theorem rec_12_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2369 32 1 6 11 0) 128 150 = 4460809145548786202900 :=
  phaseBlock_append rec_12_11_2369_0_part1 rec_12_11_2369_0_part2 rfl rfl rfl
private theorem rec_12_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2369 32 1 6 11 0) 0 278 = 99268710706116064516692 :=
  phaseBlock_append rec_12_11_2369_0_part0 rec_12_11_2369_0_join0 rfl rfl rfl

private theorem rec_12_11_2369_0 : fastPhase (bank 12 11).shape 179798 2369 32 1 6 11 0 = 99268710706116064516692 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_12_11_2369_0_join1

private theorem rec_12_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2369 32 1 6 11 1) 0 128 = 93721346885769667326336 := by decide +kernel
private theorem rec_12_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2369 32 1 6 11 1) 128 128 = 4242589691307352770238 := by decide +kernel
private theorem rec_12_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2369 32 1 6 11 1) 256 22 = 0 := by decide +kernel
private theorem rec_12_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2369 32 1 6 11 1) 128 150 = 4242589691307352770238 :=
  phaseBlock_append rec_12_11_2369_1_part1 rec_12_11_2369_1_part2 rfl rfl rfl
private theorem rec_12_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 12 11).shape 179798 2369 32 1 6 11 1) 0 278 = 97963936577077020096574 :=
  phaseBlock_append rec_12_11_2369_1_part0 rec_12_11_2369_1_join0 rfl rfl rfl

private theorem rec_12_11_2369_1 : fastPhase (bank 12 11).shape 179798 2369 32 1 6 11 1 = 97963936577077020096574 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_12_11_2369_1_join1

theorem receipt_12_11 : Checked (bank 12 11) 32 6 11 := by
  refine checked_from_values (bank 12 11) 32 6 11
    (P3_7_1.checked (bank 12 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_11_2368_0 rec_12_11_2368_1 rec_12_11_2369_0 rec_12_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2368 31 1 6 11 0) 0 128 = 89331491571375517220768 := by decide +kernel
private theorem rec_12_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2368 31 1 6 11 0) 128 128 = 4174950794089210740913 := by decide +kernel
private theorem rec_12_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2368 31 1 6 11 0) 256 22 = 0 := by decide +kernel
private theorem rec_12_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2368 31 1 6 11 0) 128 150 = 4174950794089210740913 :=
  phaseBlock_append rec_12_12_2368_0_part1 rec_12_12_2368_0_part2 rfl rfl rfl
private theorem rec_12_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2368 31 1 6 11 0) 0 278 = 93506442365464727961681 :=
  phaseBlock_append rec_12_12_2368_0_part0 rec_12_12_2368_0_join0 rfl rfl rfl

private theorem rec_12_12_2368_0 : fastPhase (bank 12 12).shape 179798 2368 31 1 6 11 0 = 93506442365464727961681 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_12_12_2368_0_join1

private theorem rec_12_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2368 31 1 6 11 1) 0 128 = 88302834016390227535136 := by decide +kernel
private theorem rec_12_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2368 31 1 6 11 1) 128 128 = 3970492471077654798892 := by decide +kernel
private theorem rec_12_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2368 31 1 6 11 1) 256 22 = 0 := by decide +kernel
private theorem rec_12_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2368 31 1 6 11 1) 128 150 = 3970492471077654798892 :=
  phaseBlock_append rec_12_12_2368_1_part1 rec_12_12_2368_1_part2 rfl rfl rfl
private theorem rec_12_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2368 31 1 6 11 1) 0 278 = 92273326487467882334028 :=
  phaseBlock_append rec_12_12_2368_1_part0 rec_12_12_2368_1_join0 rfl rfl rfl

private theorem rec_12_12_2368_1 : fastPhase (bank 12 12).shape 179798 2368 31 1 6 11 1 = 92273326487467882334028 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_12_12_2368_1_join1

private theorem rec_12_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2369 31 1 6 11 0) 0 128 = 89331924642850098769824 := by decide +kernel
private theorem rec_12_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2369 31 1 6 11 0) 128 128 = 4174949319662771202861 := by decide +kernel
private theorem rec_12_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2369 31 1 6 11 0) 256 22 = 0 := by decide +kernel
private theorem rec_12_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2369 31 1 6 11 0) 128 150 = 4174949319662771202861 :=
  phaseBlock_append rec_12_12_2369_0_part1 rec_12_12_2369_0_part2 rfl rfl rfl
private theorem rec_12_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2369 31 1 6 11 0) 0 278 = 93506873962512869972685 :=
  phaseBlock_append rec_12_12_2369_0_part0 rec_12_12_2369_0_join0 rfl rfl rfl

private theorem rec_12_12_2369_0 : fastPhase (bank 12 12).shape 179798 2369 31 1 6 11 0 = 93506873962512869972685 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_12_12_2369_0_join1

private theorem rec_12_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2369 31 1 6 11 1) 0 128 = 88303258395585098683488 := by decide +kernel
private theorem rec_12_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2369 31 1 6 11 1) 128 128 = 3970491024157807998618 := by decide +kernel
private theorem rec_12_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2369 31 1 6 11 1) 256 22 = 0 := by decide +kernel
private theorem rec_12_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2369 31 1 6 11 1) 128 150 = 3970491024157807998618 :=
  phaseBlock_append rec_12_12_2369_1_part1 rec_12_12_2369_1_part2 rfl rfl rfl
private theorem rec_12_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 12 12).shape 179798 2369 31 1 6 11 1) 0 278 = 92273749419742906682106 :=
  phaseBlock_append rec_12_12_2369_1_part0 rec_12_12_2369_1_join0 rfl rfl rfl

private theorem rec_12_12_2369_1 : fastPhase (bank 12 12).shape 179798 2369 31 1 6 11 1 = 92273749419742906682106 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_12_12_2369_1_join1

theorem receipt_12_12 : Checked (bank 12 12) 31 6 11 := by
  refine checked_from_values (bank 12 12) 31 6 11
    (P3_7_1.checked (bank 12 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_12_2368_0 rec_12_12_2368_1 rec_12_12_2369_0 rec_12_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2368 44 1 6 11 0) 0 128 = 433129374270660004769728 := by decide +kernel
private theorem rec_12_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2368 44 1 6 11 0) 128 128 = 76998808262865600510454 := by decide +kernel
private theorem rec_12_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2368 44 1 6 11 0) 256 114 = 0 := by decide +kernel
private theorem rec_12_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2368 44 1 6 11 0) 128 242 = 76998808262865600510454 :=
  phaseBlock_append rec_12_13_2368_0_part1 rec_12_13_2368_0_part2 rfl rfl rfl
private theorem rec_12_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2368 44 1 6 11 0) 0 370 = 510128182533525605280182 :=
  phaseBlock_append rec_12_13_2368_0_part0 rec_12_13_2368_0_join0 rfl rfl rfl

private theorem rec_12_13_2368_0 : fastPhase (bank 12 13).shape 179798 2368 44 1 6 11 0 = 510128182533525605280182 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_12_13_2368_0_join1

private theorem rec_12_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2368 44 1 6 11 1) 0 128 = 429790032316530275254464 := by decide +kernel
private theorem rec_12_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2368 44 1 6 11 1) 128 128 = 75277307570254788889099 := by decide +kernel
private theorem rec_12_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2368 44 1 6 11 1) 256 114 = 0 := by decide +kernel
private theorem rec_12_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2368 44 1 6 11 1) 128 242 = 75277307570254788889099 :=
  phaseBlock_append rec_12_13_2368_1_part1 rec_12_13_2368_1_part2 rfl rfl rfl
private theorem rec_12_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2368 44 1 6 11 1) 0 370 = 505067339886785064143563 :=
  phaseBlock_append rec_12_13_2368_1_part0 rec_12_13_2368_1_join0 rfl rfl rfl

private theorem rec_12_13_2368_1 : fastPhase (bank 12 13).shape 179798 2368 44 1 6 11 1 = 505067339886785064143563 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_12_13_2368_1_join1

private theorem rec_12_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2369 44 1 6 11 0) 0 128 = 433131663765526685753952 := by decide +kernel
private theorem rec_12_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2369 44 1 6 11 0) 128 128 = 76998851465063009458647 := by decide +kernel
private theorem rec_12_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2369 44 1 6 11 0) 256 114 = 0 := by decide +kernel
private theorem rec_12_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2369 44 1 6 11 0) 128 242 = 76998851465063009458647 :=
  phaseBlock_append rec_12_13_2369_0_part1 rec_12_13_2369_0_part2 rfl rfl rfl
private theorem rec_12_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2369 44 1 6 11 0) 0 370 = 510130515230589695212599 :=
  phaseBlock_append rec_12_13_2369_0_part0 rec_12_13_2369_0_join0 rfl rfl rfl

private theorem rec_12_13_2369_0 : fastPhase (bank 12 13).shape 179798 2369 44 1 6 11 0 = 510130515230589695212599 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_12_13_2369_0_join1

private theorem rec_12_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2369 44 1 6 11 1) 0 128 = 429792288265160262900000 := by decide +kernel
private theorem rec_12_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2369 44 1 6 11 1) 128 128 = 75277348995168648268842 := by decide +kernel
private theorem rec_12_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2369 44 1 6 11 1) 256 114 = 0 := by decide +kernel
private theorem rec_12_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2369 44 1 6 11 1) 128 242 = 75277348995168648268842 :=
  phaseBlock_append rec_12_13_2369_1_part1 rec_12_13_2369_1_part2 rfl rfl rfl
private theorem rec_12_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 12 13).shape 179798 2369 44 1 6 11 1) 0 370 = 505069637260328911168842 :=
  phaseBlock_append rec_12_13_2369_1_part0 rec_12_13_2369_1_join0 rfl rfl rfl

private theorem rec_12_13_2369_1 : fastPhase (bank 12 13).shape 179798 2369 44 1 6 11 1 = 505069637260328911168842 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_12_13_2369_1_join1

theorem receipt_12_13 : Checked (bank 12 13) 44 6 11 := by
  refine checked_from_values (bank 12 13) 44 6 11
    (P3_7_1.checked (bank 12 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_13_2368_0 rec_12_13_2368_1 rec_12_13_2369_0 rec_12_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 0 128 = 8269176693859883175790848 := by decide +kernel
private theorem rec_12_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 128 128 = 4508192818808956629100800 := by decide +kernel
private theorem rec_12_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 256 128 = 1526776152869117121267968 := by decide +kernel
private theorem rec_12_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 384 128 = 62759693705763764926150 := by decide +kernel
private theorem rec_12_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 512 128 = 0 := by decide +kernel
private theorem rec_12_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 640 38 = 0 := by decide +kernel
private theorem rec_12_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 128 256 = 6034968971678073750368768 :=
  phaseBlock_append rec_12_14_2368_0_part1 rec_12_14_2368_0_part2 rfl rfl rfl
private theorem rec_12_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 0 384 = 14304145665537956926159616 :=
  phaseBlock_append rec_12_14_2368_0_part0 rec_12_14_2368_0_join0 rfl rfl rfl
private theorem rec_12_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 512 166 = 0 :=
  phaseBlock_append rec_12_14_2368_0_part4 rec_12_14_2368_0_part5 rfl rfl rfl
private theorem rec_12_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 384 294 = 62759693705763764926150 :=
  phaseBlock_append rec_12_14_2368_0_part3 rec_12_14_2368_0_join2 rfl rfl rfl
private theorem rec_12_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 0) 0 678 = 14366905359243720691085766 :=
  phaseBlock_append rec_12_14_2368_0_join1 rec_12_14_2368_0_join3 rfl rfl rfl

private theorem rec_12_14_2368_0 : fastPhase (bank 12 14).shape 179798 2368 76 1 6 11 0 = 14366905359243720691085766 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_12_14_2368_0_join4

private theorem rec_12_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 0 128 = 8238934323994132687603456 := by decide +kernel
private theorem rec_12_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 128 128 = 4481112154655737171535616 := by decide +kernel
private theorem rec_12_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 256 128 = 1508046944551952862938880 := by decide +kernel
private theorem rec_12_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 384 128 = 59449306022839084524846 := by decide +kernel
private theorem rec_12_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 512 128 = 0 := by decide +kernel
private theorem rec_12_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 640 38 = 0 := by decide +kernel
private theorem rec_12_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 128 256 = 5989159099207690034474496 :=
  phaseBlock_append rec_12_14_2368_1_part1 rec_12_14_2368_1_part2 rfl rfl rfl
private theorem rec_12_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 0 384 = 14228093423201822722077952 :=
  phaseBlock_append rec_12_14_2368_1_part0 rec_12_14_2368_1_join0 rfl rfl rfl
private theorem rec_12_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 512 166 = 0 :=
  phaseBlock_append rec_12_14_2368_1_part4 rec_12_14_2368_1_part5 rfl rfl rfl
private theorem rec_12_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 384 294 = 59449306022839084524846 :=
  phaseBlock_append rec_12_14_2368_1_part3 rec_12_14_2368_1_join2 rfl rfl rfl
private theorem rec_12_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2368 76 1 6 11 1) 0 678 = 14287542729224661806602798 :=
  phaseBlock_append rec_12_14_2368_1_join1 rec_12_14_2368_1_join3 rfl rfl rfl

private theorem rec_12_14_2368_1 : fastPhase (bank 12 14).shape 179798 2368 76 1 6 11 1 = 14287542729224661806602798 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_12_14_2368_1_join4

private theorem rec_12_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 0 128 = 8269230174536351488136448 := by decide +kernel
private theorem rec_12_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 128 128 = 4508205537086174150350080 := by decide +kernel
private theorem rec_12_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 256 128 = 1526776735690340953675008 := by decide +kernel
private theorem rec_12_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 384 128 = 62759622192340993179600 := by decide +kernel
private theorem rec_12_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 512 128 = 0 := by decide +kernel
private theorem rec_12_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 640 38 = 0 := by decide +kernel
private theorem rec_12_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 128 256 = 6034982272776515104025088 :=
  phaseBlock_append rec_12_14_2369_0_part1 rec_12_14_2369_0_part2 rfl rfl rfl
private theorem rec_12_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 0 384 = 14304212447312866592161536 :=
  phaseBlock_append rec_12_14_2369_0_part0 rec_12_14_2369_0_join0 rfl rfl rfl
private theorem rec_12_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 512 166 = 0 :=
  phaseBlock_append rec_12_14_2369_0_part4 rec_12_14_2369_0_part5 rfl rfl rfl
private theorem rec_12_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 384 294 = 62759622192340993179600 :=
  phaseBlock_append rec_12_14_2369_0_part3 rec_12_14_2369_0_join2 rfl rfl rfl
private theorem rec_12_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 0) 0 678 = 14366972069505207585341136 :=
  phaseBlock_append rec_12_14_2369_0_join1 rec_12_14_2369_0_join3 rfl rfl rfl

private theorem rec_12_14_2369_0 : fastPhase (bank 12 14).shape 179798 2369 76 1 6 11 0 = 14366972069505207585341136 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_12_14_2369_0_join4

private theorem rec_12_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 0 128 = 8238987403219639576302272 := by decide +kernel
private theorem rec_12_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 128 128 = 4481124730155707406201536 := by decide +kernel
private theorem rec_12_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 256 128 = 1508047508111558206247616 := by decide +kernel
private theorem rec_12_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 384 128 = 59449237982240513545678 := by decide +kernel
private theorem rec_12_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 512 128 = 0 := by decide +kernel
private theorem rec_12_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 640 38 = 0 := by decide +kernel
private theorem rec_12_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 128 256 = 5989172238267265612449152 :=
  phaseBlock_append rec_12_14_2369_1_part1 rec_12_14_2369_1_part2 rfl rfl rfl
private theorem rec_12_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 0 384 = 14228159641486905188751424 :=
  phaseBlock_append rec_12_14_2369_1_part0 rec_12_14_2369_1_join0 rfl rfl rfl
private theorem rec_12_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 512 166 = 0 :=
  phaseBlock_append rec_12_14_2369_1_part4 rec_12_14_2369_1_part5 rfl rfl rfl
private theorem rec_12_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 384 294 = 59449237982240513545678 :=
  phaseBlock_append rec_12_14_2369_1_part3 rec_12_14_2369_1_join2 rfl rfl rfl
private theorem rec_12_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 12 14).shape 179798 2369 76 1 6 11 1) 0 678 = 14287608879469145702297102 :=
  phaseBlock_append rec_12_14_2369_1_join1 rec_12_14_2369_1_join3 rfl rfl rfl

private theorem rec_12_14_2369_1 : fastPhase (bank 12 14).shape 179798 2369 76 1 6 11 1 = 14287608879469145702297102 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_12_14_2369_1_join4

theorem receipt_12_14 : Checked (bank 12 14) 76 6 11 := by
  refine checked_from_values (bank 12 14) 76 6 11
    (P3_7_1.checked (bank 12 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_14_2368_0 rec_12_14_2368_1 rec_12_14_2369_0 rec_12_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 0 128 = 40001557537947514117395296 := by decide +kernel
private theorem rec_12_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 128 128 = 27012133801780125461324640 := by decide +kernel
private theorem rec_12_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 256 128 = 15303843440097945142473568 := by decide +kernel
private theorem rec_12_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 384 128 = 6072775409356894355473248 := by decide +kernel
private theorem rec_12_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 512 128 = 583499346345417687993422 := by decide +kernel
private theorem rec_12_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 640 128 = 0 := by decide +kernel
private theorem rec_12_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 768 128 = 0 := by decide +kernel
private theorem rec_12_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 896 29 = 0 := by decide +kernel
private theorem rec_12_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 0 256 = 67013691339727639578719936 :=
  phaseBlock_append rec_12_15_2368_0_part0 rec_12_15_2368_0_part1 rfl rfl rfl
private theorem rec_12_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 256 256 = 21376618849454839497946816 :=
  phaseBlock_append rec_12_15_2368_0_part2 rec_12_15_2368_0_part3 rfl rfl rfl
private theorem rec_12_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 0 512 = 88390310189182479076666752 :=
  phaseBlock_append rec_12_15_2368_0_join0 rec_12_15_2368_0_join1 rfl rfl rfl
private theorem rec_12_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 512 256 = 583499346345417687993422 :=
  phaseBlock_append rec_12_15_2368_0_part4 rec_12_15_2368_0_part5 rfl rfl rfl
private theorem rec_12_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 768 157 = 0 :=
  phaseBlock_append rec_12_15_2368_0_part6 rec_12_15_2368_0_part7 rfl rfl rfl
private theorem rec_12_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 512 413 = 583499346345417687993422 :=
  phaseBlock_append rec_12_15_2368_0_join3 rec_12_15_2368_0_join4 rfl rfl rfl
private theorem rec_12_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 0) 0 925 = 88973809535527896764660174 :=
  phaseBlock_append rec_12_15_2368_0_join2 rec_12_15_2368_0_join5 rfl rfl rfl

private theorem rec_12_15_2368_0 : fastPhase (bank 12 15).shape 179798 2368 105 1 6 11 0 = 88973809535527896764660174 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_12_15_2368_0_join6

private theorem rec_12_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 0 128 = 39900017960886010273119200 := by decide +kernel
private theorem rec_12_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 128 128 = 26914192067042742145330144 := by decide +kernel
private theorem rec_12_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 256 128 = 15221129918475501585406944 := by decide +kernel
private theorem rec_12_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 384 128 = 6012580072405431787719648 := by decide +kernel
private theorem rec_12_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 512 128 = 564346700634562010859101 := by decide +kernel
private theorem rec_12_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 640 128 = 0 := by decide +kernel
private theorem rec_12_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 768 128 = 0 := by decide +kernel
private theorem rec_12_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 896 29 = 0 := by decide +kernel
private theorem rec_12_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 0 256 = 66814210027928752418449344 :=
  phaseBlock_append rec_12_15_2368_1_part0 rec_12_15_2368_1_part1 rfl rfl rfl
private theorem rec_12_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 256 256 = 21233709990880933373126592 :=
  phaseBlock_append rec_12_15_2368_1_part2 rec_12_15_2368_1_part3 rfl rfl rfl
private theorem rec_12_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 0 512 = 88047920018809685791575936 :=
  phaseBlock_append rec_12_15_2368_1_join0 rec_12_15_2368_1_join1 rfl rfl rfl
private theorem rec_12_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 512 256 = 564346700634562010859101 :=
  phaseBlock_append rec_12_15_2368_1_part4 rec_12_15_2368_1_part5 rfl rfl rfl
private theorem rec_12_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 768 157 = 0 :=
  phaseBlock_append rec_12_15_2368_1_part6 rec_12_15_2368_1_part7 rfl rfl rfl
private theorem rec_12_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 512 413 = 564346700634562010859101 :=
  phaseBlock_append rec_12_15_2368_1_join3 rec_12_15_2368_1_join4 rfl rfl rfl
private theorem rec_12_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2368 105 1 6 11 1) 0 925 = 88612266719444247802435037 :=
  phaseBlock_append rec_12_15_2368_1_join2 rec_12_15_2368_1_join5 rfl rfl rfl

private theorem rec_12_15_2368_1 : fastPhase (bank 12 15).shape 179798 2368 105 1 6 11 1 = 88612266719444247802435037 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_12_15_2368_1_join6

private theorem rec_12_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 0 128 = 40001835479076116828831616 := by decide +kernel
private theorem rec_12_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 128 128 = 27012241325030147669983104 := by decide +kernel
private theorem rec_12_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 256 128 = 15303870606874346017931136 := by decide +kernel
private theorem rec_12_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 384 128 = 6072776023711287539597184 := by decide +kernel
private theorem rec_12_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 512 128 = 583498732812890607416742 := by decide +kernel
private theorem rec_12_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 640 128 = 0 := by decide +kernel
private theorem rec_12_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 768 128 = 0 := by decide +kernel
private theorem rec_12_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 896 29 = 0 := by decide +kernel
private theorem rec_12_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 0 256 = 67014076804106264498814720 :=
  phaseBlock_append rec_12_15_2369_0_part0 rec_12_15_2369_0_part1 rfl rfl rfl
private theorem rec_12_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 256 256 = 21376646630585633557528320 :=
  phaseBlock_append rec_12_15_2369_0_part2 rec_12_15_2369_0_part3 rfl rfl rfl
private theorem rec_12_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 0 512 = 88390723434691898056343040 :=
  phaseBlock_append rec_12_15_2369_0_join0 rec_12_15_2369_0_join1 rfl rfl rfl
private theorem rec_12_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 512 256 = 583498732812890607416742 :=
  phaseBlock_append rec_12_15_2369_0_part4 rec_12_15_2369_0_part5 rfl rfl rfl
private theorem rec_12_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 768 157 = 0 :=
  phaseBlock_append rec_12_15_2369_0_part6 rec_12_15_2369_0_part7 rfl rfl rfl
private theorem rec_12_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 512 413 = 583498732812890607416742 :=
  phaseBlock_append rec_12_15_2369_0_join3 rec_12_15_2369_0_join4 rfl rfl rfl
private theorem rec_12_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 0) 0 925 = 88974222167504788663759782 :=
  phaseBlock_append rec_12_15_2369_0_join2 rec_12_15_2369_0_join5 rfl rfl rfl

private theorem rec_12_15_2369_0 : fastPhase (bank 12 15).shape 179798 2369 105 1 6 11 0 = 88974222167504788663759782 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_12_15_2369_0_join6

private theorem rec_12_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 0 128 = 39900294413791841450659392 := by decide +kernel
private theorem rec_12_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 128 128 = 26914298842224668726947392 := by decide +kernel
private theorem rec_12_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 256 128 = 15221156797288477404024384 := by decide +kernel
private theorem rec_12_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 384 128 = 6012580643964018117652032 := by decide +kernel
private theorem rec_12_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 512 128 = 564346105302543622571286 := by decide +kernel
private theorem rec_12_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 640 128 = 0 := by decide +kernel
private theorem rec_12_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 768 128 = 0 := by decide +kernel
private theorem rec_12_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 896 29 = 0 := by decide +kernel
private theorem rec_12_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 0 256 = 66814593256016510177606784 :=
  phaseBlock_append rec_12_15_2369_1_part0 rec_12_15_2369_1_part1 rfl rfl rfl
private theorem rec_12_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 256 256 = 21233737441252495521676416 :=
  phaseBlock_append rec_12_15_2369_1_part2 rec_12_15_2369_1_part3 rfl rfl rfl
private theorem rec_12_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 0 512 = 88048330697269005699283200 :=
  phaseBlock_append rec_12_15_2369_1_join0 rec_12_15_2369_1_join1 rfl rfl rfl
private theorem rec_12_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 512 256 = 564346105302543622571286 :=
  phaseBlock_append rec_12_15_2369_1_part4 rec_12_15_2369_1_part5 rfl rfl rfl
private theorem rec_12_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 768 157 = 0 :=
  phaseBlock_append rec_12_15_2369_1_part6 rec_12_15_2369_1_part7 rfl rfl rfl
private theorem rec_12_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 512 413 = 564346105302543622571286 :=
  phaseBlock_append rec_12_15_2369_1_join3 rec_12_15_2369_1_join4 rfl rfl rfl
private theorem rec_12_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 12 15).shape 179798 2369 105 1 6 11 1) 0 925 = 88612676802571549321854486 :=
  phaseBlock_append rec_12_15_2369_1_join2 rec_12_15_2369_1_join5 rfl rfl rfl

private theorem rec_12_15_2369_1 : fastPhase (bank 12 15).shape 179798 2369 105 1 6 11 1 = 88612676802571549321854486 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_12_15_2369_1_join6

theorem receipt_12_15 : Checked (bank 12 15) 105 6 11 := by
  refine checked_from_values (bank 12 15) 105 6 11
    (P3_7_1.checked (bank 12 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_15_2368_0 rec_12_15_2368_1 rec_12_15_2369_0 rec_12_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_12_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 0 128 = 68784438026245081765143648 := by decide +kernel
private theorem rec_12_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 128 128 = 47576477694155587003249760 := by decide +kernel
private theorem rec_12_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 256 128 = 27664265430327176548222048 := by decide +kernel
private theorem rec_12_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 384 128 = 11284535825670957655299168 := by decide +kernel
private theorem rec_12_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 512 128 = 1110981828111985032095374 := by decide +kernel
private theorem rec_12_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 640 128 = 0 := by decide +kernel
private theorem rec_12_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 768 128 = 0 := by decide +kernel
private theorem rec_12_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 896 29 = 0 := by decide +kernel
private theorem rec_12_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 0 256 = 116360915720400668768393408 :=
  phaseBlock_append rec_12_16_2368_0_part0 rec_12_16_2368_0_part1 rfl rfl rfl
private theorem rec_12_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 256 256 = 38948801255998134203521216 :=
  phaseBlock_append rec_12_16_2368_0_part2 rec_12_16_2368_0_part3 rfl rfl rfl
private theorem rec_12_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 0 512 = 155309716976398802971914624 :=
  phaseBlock_append rec_12_16_2368_0_join0 rec_12_16_2368_0_join1 rfl rfl rfl
private theorem rec_12_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 512 256 = 1110981828111985032095374 :=
  phaseBlock_append rec_12_16_2368_0_part4 rec_12_16_2368_0_part5 rfl rfl rfl
private theorem rec_12_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 768 157 = 0 :=
  phaseBlock_append rec_12_16_2368_0_part6 rec_12_16_2368_0_part7 rfl rfl rfl
private theorem rec_12_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 512 413 = 1110981828111985032095374 :=
  phaseBlock_append rec_12_16_2368_0_join3 rec_12_16_2368_0_join4 rfl rfl rfl
private theorem rec_12_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 0) 0 925 = 156420698804510788004009998 :=
  phaseBlock_append rec_12_16_2368_0_join2 rec_12_16_2368_0_join5 rfl rfl rfl

private theorem rec_12_16_2368_0 : fastPhase (bank 12 16).shape 179798 2368 138 1 6 11 0 = 156420698804510788004009998 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_12_16_2368_0_join6

private theorem rec_12_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 0 128 = 68622187663908705507820256 := by decide +kernel
private theorem rec_12_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 128 128 = 47413227878219663690314464 := by decide +kernel
private theorem rec_12_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 256 128 = 27520545272882537812402912 := by decide +kernel
private theorem rec_12_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 384 128 = 11175083192075583884104416 := by decide +kernel
private theorem rec_12_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 512 128 = 1074712349732037195516229 := by decide +kernel
private theorem rec_12_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 640 128 = 0 := by decide +kernel
private theorem rec_12_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 768 128 = 0 := by decide +kernel
private theorem rec_12_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 896 29 = 0 := by decide +kernel
private theorem rec_12_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 0 256 = 116035415542128369198134720 :=
  phaseBlock_append rec_12_16_2368_1_part0 rec_12_16_2368_1_part1 rfl rfl rfl
private theorem rec_12_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 256 256 = 38695628464958121696507328 :=
  phaseBlock_append rec_12_16_2368_1_part2 rec_12_16_2368_1_part3 rfl rfl rfl
private theorem rec_12_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 0 512 = 154731044007086490894642048 :=
  phaseBlock_append rec_12_16_2368_1_join0 rec_12_16_2368_1_join1 rfl rfl rfl
private theorem rec_12_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 512 256 = 1074712349732037195516229 :=
  phaseBlock_append rec_12_16_2368_1_part4 rec_12_16_2368_1_part5 rfl rfl rfl
private theorem rec_12_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 768 157 = 0 :=
  phaseBlock_append rec_12_16_2368_1_part6 rec_12_16_2368_1_part7 rfl rfl rfl
private theorem rec_12_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 512 413 = 1074712349732037195516229 :=
  phaseBlock_append rec_12_16_2368_1_join3 rec_12_16_2368_1_join4 rfl rfl rfl
private theorem rec_12_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2368 138 1 6 11 1) 0 925 = 155805756356818528090158277 :=
  phaseBlock_append rec_12_16_2368_1_join2 rec_12_16_2368_1_join5 rfl rfl rfl

private theorem rec_12_16_2368_1 : fastPhase (bank 12 16).shape 179798 2368 138 1 6 11 1 = 155805756356818528090158277 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_12_16_2368_1_join6

private theorem rec_12_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 0 128 = 68784898463755077098841984 := by decide +kernel
private theorem rec_12_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 128 128 = 47576656669820865174529920 := by decide +kernel
private theorem rec_12_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 256 128 = 27664309228275912627464064 := by decide +kernel
private theorem rec_12_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 384 128 = 11284535034410442706970496 := by decide +kernel
private theorem rec_12_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 512 128 = 1110980488229078744816538 := by decide +kernel
private theorem rec_12_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 640 128 = 0 := by decide +kernel
private theorem rec_12_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 768 128 = 0 := by decide +kernel
private theorem rec_12_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 896 29 = 0 := by decide +kernel
private theorem rec_12_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 0 256 = 116361555133575942273371904 :=
  phaseBlock_append rec_12_16_2369_0_part0 rec_12_16_2369_0_part1 rfl rfl rfl
private theorem rec_12_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 256 256 = 38948844262686355334434560 :=
  phaseBlock_append rec_12_16_2369_0_part2 rec_12_16_2369_0_part3 rfl rfl rfl
private theorem rec_12_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 0 512 = 155310399396262297607806464 :=
  phaseBlock_append rec_12_16_2369_0_join0 rec_12_16_2369_0_join1 rfl rfl rfl
private theorem rec_12_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 512 256 = 1110980488229078744816538 :=
  phaseBlock_append rec_12_16_2369_0_part4 rec_12_16_2369_0_part5 rfl rfl rfl
private theorem rec_12_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 768 157 = 0 :=
  phaseBlock_append rec_12_16_2369_0_part6 rec_12_16_2369_0_part7 rfl rfl rfl
private theorem rec_12_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 512 413 = 1110980488229078744816538 :=
  phaseBlock_append rec_12_16_2369_0_join3 rec_12_16_2369_0_join4 rfl rfl rfl
private theorem rec_12_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 0) 0 925 = 156421379884491376352623002 :=
  phaseBlock_append rec_12_16_2369_0_join2 rec_12_16_2369_0_join5 rfl rfl rfl

private theorem rec_12_16_2369_0 : fastPhase (bank 12 16).shape 179798 2369 138 1 6 11 0 = 156421379884491376352623002 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_12_16_2369_0_join6

private theorem rec_12_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 0 128 = 68622645691886590890767808 := by decide +kernel
private theorem rec_12_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 128 128 = 47413405620267487231088064 := by decide +kernel
private theorem rec_12_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 256 128 = 27520588593232170283283904 := by decide +kernel
private theorem rec_12_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 384 128 = 11175082341892115318789568 := by decide +kernel
private theorem rec_12_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 512 128 = 1074711050035022818302090 := by decide +kernel
private theorem rec_12_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 640 128 = 0 := by decide +kernel
private theorem rec_12_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 768 128 = 0 := by decide +kernel
private theorem rec_12_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 896 29 = 0 := by decide +kernel
private theorem rec_12_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 0 256 = 116036051312154078121855872 :=
  phaseBlock_append rec_12_16_2369_1_part0 rec_12_16_2369_1_part1 rfl rfl rfl
private theorem rec_12_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 256 256 = 38695670935124285602073472 :=
  phaseBlock_append rec_12_16_2369_1_part2 rec_12_16_2369_1_part3 rfl rfl rfl
private theorem rec_12_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 0 512 = 154731722247278363723929344 :=
  phaseBlock_append rec_12_16_2369_1_join0 rec_12_16_2369_1_join1 rfl rfl rfl
private theorem rec_12_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 512 256 = 1074711050035022818302090 :=
  phaseBlock_append rec_12_16_2369_1_part4 rec_12_16_2369_1_part5 rfl rfl rfl
private theorem rec_12_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 768 157 = 0 :=
  phaseBlock_append rec_12_16_2369_1_part6 rec_12_16_2369_1_part7 rfl rfl rfl
private theorem rec_12_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 512 413 = 1074711050035022818302090 :=
  phaseBlock_append rec_12_16_2369_1_join3 rec_12_16_2369_1_join4 rfl rfl rfl
private theorem rec_12_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 12 16).shape 179798 2369 138 1 6 11 1) 0 925 = 155806433297313386542231434 :=
  phaseBlock_append rec_12_16_2369_1_join2 rec_12_16_2369_1_join5 rfl rfl rfl

private theorem rec_12_16_2369_1 : fastPhase (bank 12 16).shape 179798 2369 138 1 6 11 1 = 155806433297313386542231434 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_12_16_2369_1_join6

theorem receipt_12_16 : Checked (bank 12 16) 138 6 11 := by
  refine checked_from_values (bank 12 16) 138 6 11
    (P3_7_1.checked (bank 12 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_12_16_2368_0 rec_12_16_2368_1 rec_12_16_2369_0 rec_12_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect12_checked (i : Fin 17) :
    Checked (bank 12 i) (reserve i) (excess 12) (seed 12) := by
  fin_cases i
  · exact receipt_12_0
  · exact receipt_12_1
  · exact receipt_12_2
  · exact receipt_12_3
  · exact receipt_12_4
  · exact receipt_12_5
  · exact receipt_12_6
  · exact receipt_12_7
  · exact receipt_12_8
  · exact receipt_12_9
  · exact receipt_12_10
  · exact receipt_12_11
  · exact receipt_12_12
  · exact receipt_12_13
  · exact receipt_12_14
  · exact receipt_12_15
  · exact receipt_12_16

end Lower6961.Lo.RescueSource

end Merged_R6961LoRescueSourceReceipt12

-- merged module R6961LoRescueSource6961
section Merged_R6961LoRescueSource6961

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueSource
open P1_7 (Bank debit)
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)

theorem checked (rect : Fin 13) (i : Fin 17) (h : 7 ≤ rect.val ∨ i ≠ 0) :
    Checked (bank rect i) (reserve i) (excess rect) (seed rect) := by
  fin_cases rect
  · exact rect0_checked i (h.resolve_left (by decide))
  · exact rect1_checked i (h.resolve_left (by decide))
  · exact rect2_checked i (h.resolve_left (by decide))
  · exact rect3_checked i (h.resolve_left (by decide))
  · exact rect4_checked i (h.resolve_left (by decide))
  · exact rect5_checked i (h.resolve_left (by decide))
  · exact rect6_checked i (h.resolve_left (by decide))
  · exact rect7_checked i
  · exact rect8_checked i
  · exact rect9_checked i
  · exact rect10_checked i
  · exact rect11_checked i
  · exact rect12_checked i

theorem cutoff_fit {h : ℕ} (lo : 2368≤h) (hi : h≤2401) (rect : Fin 13) (i : Fin 17)
    (hok : 7 ≤ rect.val ∨ i ≠ 0) :
    cutoff h rect i+2*h*(reserve i)<(bank rect i).shape.m*179798 :=
  (checked rect i hok).cutoff_fit lo hi

theorem rescue_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2368≤h) (hi : h≤2401) (rect : Fin 13) (i : Fin 17) (hok : 7 ≤ rect.val ∨ i ≠ 0) {G : Jet}
    (irr : Irreducible G) (seeded : UsesSeed G) (slope : 1≤G.natDegree)
    (hs : seed rect≤seedDegree G) (hj : G.natDegree+excess rect≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬ G∣Q :=
  (checked rect i hok).avoids Crt word lo hi irr seeded slope hs hj

end Lower6961.Lo.RescueSource

end Merged_R6961LoRescueSource6961
