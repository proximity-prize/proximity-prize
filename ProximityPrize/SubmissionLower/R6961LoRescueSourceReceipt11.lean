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


private theorem rec_11_0_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2368 0 1 4 12 0) 0 128 = 796370150525090767668 := by decide +kernel
private theorem rec_11_0_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2368 0 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_0_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2368 0 1 4 12 0) 0 130 = 796370150525090767668 :=
  phaseBlock_append rec_11_0_2368_0_part0 rec_11_0_2368_0_part1 rfl rfl rfl

private theorem rec_11_0_2368_0 : fastPhase (bank 11 0).shape 179798 2368 0 1 4 12 0 = 796370150525090767668 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_0_2368_0_join0

private theorem rec_11_0_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2368 0 1 4 12 1) 0 128 = 776775862931334179556 := by decide +kernel
private theorem rec_11_0_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2368 0 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_0_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2368 0 1 4 12 1) 0 130 = 776775862931334179556 :=
  phaseBlock_append rec_11_0_2368_1_part0 rec_11_0_2368_1_part1 rfl rfl rfl

private theorem rec_11_0_2368_1 : fastPhase (bank 11 0).shape 179798 2368 0 1 4 12 1 = 776775862931334179556 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_0_2368_1_join0

private theorem rec_11_0_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2369 0 1 4 12 0) 0 128 = 796374615989278823640 := by decide +kernel
private theorem rec_11_0_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2369 0 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_0_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2369 0 1 4 12 0) 0 130 = 796374615989278823640 :=
  phaseBlock_append rec_11_0_2369_0_part0 rec_11_0_2369_0_part1 rfl rfl rfl

private theorem rec_11_0_2369_0 : fastPhase (bank 11 0).shape 179798 2369 0 1 4 12 0 = 796374615989278823640 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_0_2369_0_join0

private theorem rec_11_0_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2369 0 1 4 12 1) 0 128 = 776780180056279634844 := by decide +kernel
private theorem rec_11_0_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2369 0 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_0_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 0).shape 179798 2369 0 1 4 12 1) 0 130 = 776780180056279634844 :=
  phaseBlock_append rec_11_0_2369_1_part0 rec_11_0_2369_1_part1 rfl rfl rfl

private theorem rec_11_0_2369_1 : fastPhase (bank 11 0).shape 179798 2369 0 1 4 12 1 = 776780180056279634844 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_0_2369_1_join0

theorem receipt_11_0 : Checked (bank 11 0) 0 4 12 := by
  refine checked_from_values (bank 11 0) 0 4 12
    (P3_7_1.checked (bank 11 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_0_2368_0 rec_11_0_2368_1 rec_11_0_2369_0 rec_11_0_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2368 1 1 4 12 0) 0 128 = 907780083818764195395 := by decide +kernel
private theorem rec_11_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2368 1 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2368 1 1 4 12 0) 0 130 = 907780083818764195395 :=
  phaseBlock_append rec_11_1_2368_0_part0 rec_11_1_2368_0_part1 rfl rfl rfl

private theorem rec_11_1_2368_0 : fastPhase (bank 11 1).shape 179798 2368 1 1 4 12 0 = 907780083818764195395 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_1_2368_0_join0

private theorem rec_11_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2368 1 1 4 12 1) 0 128 = 885701566627368107883 := by decide +kernel
private theorem rec_11_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2368 1 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2368 1 1 4 12 1) 0 130 = 885701566627368107883 :=
  phaseBlock_append rec_11_1_2368_1_part0 rec_11_1_2368_1_part1 rfl rfl rfl

private theorem rec_11_1_2368_1 : fastPhase (bank 11 1).shape 179798 2368 1 1 4 12 1 = 885701566627368107883 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_1_2368_1_join0

private theorem rec_11_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2369 1 1 4 12 0) 0 128 = 907785105655107741696 := by decide +kernel
private theorem rec_11_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2369 1 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2369 1 1 4 12 0) 0 130 = 907785105655107741696 :=
  phaseBlock_append rec_11_1_2369_0_part0 rec_11_1_2369_0_part1 rfl rfl rfl

private theorem rec_11_1_2369_0 : fastPhase (bank 11 1).shape 179798 2369 1 1 4 12 0 = 907785105655107741696 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_1_2369_0_join0

private theorem rec_11_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2369 1 1 4 12 1) 0 128 = 885706423062157331550 := by decide +kernel
private theorem rec_11_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2369 1 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 1).shape 179798 2369 1 1 4 12 1) 0 130 = 885706423062157331550 :=
  phaseBlock_append rec_11_1_2369_1_part0 rec_11_1_2369_1_part1 rfl rfl rfl

private theorem rec_11_1_2369_1 : fastPhase (bank 11 1).shape 179798 2369 1 1 4 12 1 = 885706423062157331550 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_1_2369_1_join0

theorem receipt_11_1 : Checked (bank 11 1) 1 4 12 := by
  refine checked_from_values (bank 11 1) 1 4 12
    (P3_7_1.checked (bank 11 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_1_2368_0 rec_11_1_2368_1 rec_11_1_2369_0 rec_11_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2368 2 1 4 12 0) 0 128 = 1042909724052692530884 := by decide +kernel
private theorem rec_11_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2368 2 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2368 2 1 4 12 0) 0 130 = 1042909724052692530884 :=
  phaseBlock_append rec_11_2_2368_0_part0 rec_11_2_2368_0_part1 rfl rfl rfl

private theorem rec_11_2_2368_0 : fastPhase (bank 11 2).shape 179798 2368 2 1 4 12 0 = 1042909724052692530884 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_2_2368_0_join0

private theorem rec_11_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2368 2 1 4 12 1) 0 128 = 1017836567394333229812 := by decide +kernel
private theorem rec_11_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2368 2 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2368 2 1 4 12 1) 0 130 = 1017836567394333229812 :=
  phaseBlock_append rec_11_2_2368_1_part0 rec_11_2_2368_1_part1 rfl rfl rfl

private theorem rec_11_2_2368_1 : fastPhase (bank 11 2).shape 179798 2368 2 1 4 12 1 = 1017836567394333229812 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_2_2368_1_join0

private theorem rec_11_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2369 2 1 4 12 0) 0 128 = 1042915415160765153960 := by decide +kernel
private theorem rec_11_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2369 2 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2369 2 1 4 12 0) 0 130 = 1042915415160765153960 :=
  phaseBlock_append rec_11_2_2369_0_part0 rec_11_2_2369_0_part1 rfl rfl rfl

private theorem rec_11_2_2369_0 : fastPhase (bank 11 2).shape 179798 2369 2 1 4 12 0 = 1042915415160765153960 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_2_2369_0_join0

private theorem rec_11_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2369 2 1 4 12 1) 0 128 = 1017842072654351297844 := by decide +kernel
private theorem rec_11_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2369 2 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 2).shape 179798 2369 2 1 4 12 1) 0 130 = 1017842072654351297844 :=
  phaseBlock_append rec_11_2_2369_1_part0 rec_11_2_2369_1_part1 rfl rfl rfl

private theorem rec_11_2_2369_1 : fastPhase (bank 11 2).shape 179798 2369 2 1 4 12 1 = 1017842072654351297844 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_2_2369_1_join0

theorem receipt_11_2 : Checked (bank 11 2) 2 4 12 := by
  refine checked_from_values (bank 11 2) 2 4 12
    (P3_7_1.checked (bank 11 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_2_2368_0 rec_11_2_2368_1 rec_11_2_2369_0 rec_11_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2368 3 1 4 12 0) 0 128 = 1209771384188903783442 := by decide +kernel
private theorem rec_11_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2368 3 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2368 3 1 4 12 0) 0 130 = 1209771384188903783442 :=
  phaseBlock_append rec_11_3_2368_0_part0 rec_11_3_2368_0_part1 rfl rfl rfl

private theorem rec_11_3_2368_0 : fastPhase (bank 11 3).shape 179798 2368 3 1 4 12 0 = 1209771384188903783442 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_3_2368_0_join0

private theorem rec_11_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2368 3 1 4 12 1) 0 128 = 1181023024902316776690 := by decide +kernel
private theorem rec_11_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2368 3 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2368 3 1 4 12 1) 0 130 = 1181023024902316776690 :=
  phaseBlock_append rec_11_3_2368_1_part0 rec_11_3_2368_1_part1 rfl rfl rfl

private theorem rec_11_3_2368_1 : fastPhase (bank 11 3).shape 179798 2368 3 1 4 12 1 = 1181023024902316776690 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_3_2368_1_join0

private theorem rec_11_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2369 3 1 4 12 0) 0 128 = 1209777895200403315080 := by decide +kernel
private theorem rec_11_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2369 3 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2369 3 1 4 12 0) 0 130 = 1209777895200403315080 :=
  phaseBlock_append rec_11_3_2369_0_part0 rec_11_3_2369_0_part1 rfl rfl rfl

private theorem rec_11_3_2369_0 : fastPhase (bank 11 3).shape 179798 2369 3 1 4 12 0 = 1209777895200403315080 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_3_2369_0_join0

private theorem rec_11_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2369 3 1 4 12 1) 0 128 = 1181029325114198091564 := by decide +kernel
private theorem rec_11_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2369 3 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 3).shape 179798 2369 3 1 4 12 1) 0 130 = 1181029325114198091564 :=
  phaseBlock_append rec_11_3_2369_1_part0 rec_11_3_2369_1_part1 rfl rfl rfl

private theorem rec_11_3_2369_1 : fastPhase (bank 11 3).shape 179798 2369 3 1 4 12 1 = 1181029325114198091564 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_3_2369_1_join0

theorem receipt_11_3 : Checked (bank 11 3) 3 4 12 := by
  refine checked_from_values (bank 11 3) 3 4 12
    (P3_7_1.checked (bank 11 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_3_2368_0 rec_11_3_2368_1 rec_11_3_2369_0 rec_11_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2368 4 1 4 12 0) 0 128 = 1417706793901051119853 := by decide +kernel
private theorem rec_11_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2368 4 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2368 4 1 4 12 0) 0 130 = 1417706793901051119853 :=
  phaseBlock_append rec_11_4_2368_0_part0 rec_11_4_2368_0_part1 rfl rfl rfl

private theorem rec_11_4_2368_0 : fastPhase (bank 11 4).shape 179798 2368 4 1 4 12 0 = 1417706793901051119853 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_4_2368_0_join0

private theorem rec_11_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2368 4 1 4 12 1) 0 128 = 1384406567236538737061 := by decide +kernel
private theorem rec_11_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2368 4 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2368 4 1 4 12 1) 0 130 = 1384406567236538737061 :=
  phaseBlock_append rec_11_4_2368_1_part0 rec_11_4_2368_1_part1 rfl rfl rfl

private theorem rec_11_4_2368_1 : fastPhase (bank 11 4).shape 179798 2368 4 1 4 12 1 = 1384406567236538737061 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_4_2368_1_join0

private theorem rec_11_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2369 4 1 4 12 0) 0 128 = 1417714318158995967882 := by decide +kernel
private theorem rec_11_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2369 4 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2369 4 1 4 12 0) 0 130 = 1417714318158995967882 :=
  phaseBlock_append rec_11_4_2369_0_part0 rec_11_4_2369_0_part1 rfl rfl rfl

private theorem rec_11_4_2369_0 : fastPhase (bank 11 4).shape 179798 2369 4 1 4 12 0 = 1417714318158995967882 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_4_2369_0_join0

private theorem rec_11_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2369 4 1 4 12 1) 0 128 = 1384413849978719194906 := by decide +kernel
private theorem rec_11_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2369 4 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 4).shape 179798 2369 4 1 4 12 1) 0 130 = 1384413849978719194906 :=
  phaseBlock_append rec_11_4_2369_1_part0 rec_11_4_2369_1_part1 rfl rfl rfl

private theorem rec_11_4_2369_1 : fastPhase (bank 11 4).shape 179798 2369 4 1 4 12 1 = 1384413849978719194906 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_4_2369_1_join0

theorem receipt_11_4 : Checked (bank 11 4) 4 4 12 := by
  refine checked_from_values (bank 11 4) 4 4 12
    (P3_7_1.checked (bank 11 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_4_2368_0 rec_11_4_2368_1 rec_11_4_2369_0 rec_11_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2368 5 1 4 12 0) 0 128 = 1681924296559292662029 := by decide +kernel
private theorem rec_11_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2368 5 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2368 5 1 4 12 0) 0 130 = 1681924296559292662029 :=
  phaseBlock_append rec_11_5_2368_0_part0 rec_11_5_2368_0_part1 rfl rfl rfl

private theorem rec_11_5_2368_0 : fastPhase (bank 11 5).shape 179798 2368 5 1 4 12 0 = 1681924296559292662029 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_5_2368_0_join0

private theorem rec_11_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2368 5 1 4 12 1) 0 128 = 1642875382270930053957 := by decide +kernel
private theorem rec_11_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2368 5 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2368 5 1 4 12 1) 0 130 = 1642875382270930053957 :=
  phaseBlock_append rec_11_5_2368_1_part0 rec_11_5_2368_1_part1 rfl rfl rfl

private theorem rec_11_5_2368_1 : fastPhase (bank 11 5).shape 179798 2368 5 1 4 12 1 = 1642875382270930053957 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_5_2368_1_join0

private theorem rec_11_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2369 5 1 4 12 0) 0 128 = 1681933097844309352344 := by decide +kernel
private theorem rec_11_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2369 5 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2369 5 1 4 12 0) 0 130 = 1681933097844309352344 :=
  phaseBlock_append rec_11_5_2369_0_part0 rec_11_5_2369_0_part1 rfl rfl rfl

private theorem rec_11_5_2369_0 : fastPhase (bank 11 5).shape 179798 2369 5 1 4 12 0 = 1681933097844309352344 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_5_2369_0_join0

private theorem rec_11_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2369 5 1 4 12 1) 0 128 = 1642883903478979058178 := by decide +kernel
private theorem rec_11_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2369 5 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 5).shape 179798 2369 5 1 4 12 1) 0 130 = 1642883903478979058178 :=
  phaseBlock_append rec_11_5_2369_1_part0 rec_11_5_2369_1_part1 rfl rfl rfl

private theorem rec_11_5_2369_1 : fastPhase (bank 11 5).shape 179798 2369 5 1 4 12 1 = 1642883903478979058178 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_5_2369_1_join0

theorem receipt_11_5 : Checked (bank 11 5) 5 4 12 := by
  refine checked_from_values (bank 11 5) 5 4 12
    (P3_7_1.checked (bank 11 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_5_2368_0 rec_11_5_2368_1 rec_11_5_2369_0 rec_11_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2368 7 1 4 12 0) 0 128 = 2479450516360231982361 := by decide +kernel
private theorem rec_11_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2368 7 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2368 7 1 4 12 0) 0 130 = 2479450516360231982361 :=
  phaseBlock_append rec_11_6_2368_0_part0 rec_11_6_2368_0_part1 rfl rfl rfl

private theorem rec_11_6_2368_0 : fastPhase (bank 11 6).shape 179798 2368 7 1 4 12 0 = 2479450516360231982361 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_6_2368_0_join0

private theorem rec_11_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2368 7 1 4 12 1) 0 128 = 2423214686154852296529 := by decide +kernel
private theorem rec_11_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2368 7 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2368 7 1 4 12 1) 0 130 = 2423214686154852296529 :=
  phaseBlock_append rec_11_6_2368_1_part0 rec_11_6_2368_1_part1 rfl rfl rfl

private theorem rec_11_6_2368_1 : fastPhase (bank 11 6).shape 179798 2368 7 1 4 12 1 = 2423214686154852296529 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_6_2368_1_join0

private theorem rec_11_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2369 7 1 4 12 0) 0 128 = 2479463123126828051268 := by decide +kernel
private theorem rec_11_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2369 7 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2369 7 1 4 12 0) 0 130 = 2479463123126828051268 :=
  phaseBlock_append rec_11_6_2369_0_part0 rec_11_6_2369_0_part1 rfl rfl rfl

private theorem rec_11_6_2369_0 : fastPhase (bank 11 6).shape 179798 2369 7 1 4 12 0 = 2479463123126828051268 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_6_2369_0_join0

private theorem rec_11_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2369 7 1 4 12 1) 0 128 = 2423226898646647570842 := by decide +kernel
private theorem rec_11_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2369 7 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 6).shape 179798 2369 7 1 4 12 1) 0 130 = 2423226898646647570842 :=
  phaseBlock_append rec_11_6_2369_1_part0 rec_11_6_2369_1_part1 rfl rfl rfl

private theorem rec_11_6_2369_1 : fastPhase (bank 11 6).shape 179798 2369 7 1 4 12 1 = 2423226898646647570842 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_6_2369_1_join0

theorem receipt_11_6 : Checked (bank 11 6) 7 4 12 := by
  refine checked_from_values (bank 11 6) 7 4 12
    (P3_7_1.checked (bank 11 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_6_2368_0 rec_11_6_2368_1 rec_11_6_2369_0 rec_11_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2368 10 1 4 12 0) 0 128 = 5287009007780046672114 := by decide +kernel
private theorem rec_11_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2368 10 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2368 10 1 4 12 0) 0 130 = 5287009007780046672114 :=
  phaseBlock_append rec_11_7_2368_0_part0 rec_11_7_2368_0_part1 rfl rfl rfl

private theorem rec_11_7_2368_0 : fastPhase (bank 11 7).shape 179798 2368 10 1 4 12 0 = 5287009007780046672114 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_7_2368_0_join0

private theorem rec_11_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2368 10 1 4 12 1) 0 128 = 5171243018737207276242 := by decide +kernel
private theorem rec_11_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2368 10 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2368 10 1 4 12 1) 0 130 = 5171243018737207276242 :=
  phaseBlock_append rec_11_7_2368_1_part0 rec_11_7_2368_1_part1 rfl rfl rfl

private theorem rec_11_7_2368_1 : fastPhase (bank 11 7).shape 179798 2368 10 1 4 12 1 = 5171243018737207276242 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_7_2368_1_join0

private theorem rec_11_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2369 10 1 4 12 0) 0 128 = 5287034720862738891324 := by decide +kernel
private theorem rec_11_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2369 10 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2369 10 1 4 12 0) 0 130 = 5287034720862738891324 :=
  phaseBlock_append rec_11_7_2369_0_part0 rec_11_7_2369_0_part1 rfl rfl rfl

private theorem rec_11_7_2369_0 : fastPhase (bank 11 7).shape 179798 2369 10 1 4 12 0 = 5287034720862738891324 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_7_2369_0_join0

private theorem rec_11_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2369 10 1 4 12 1) 0 128 = 5171267948476150390008 := by decide +kernel
private theorem rec_11_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2369 10 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 7).shape 179798 2369 10 1 4 12 1) 0 130 = 5171267948476150390008 :=
  phaseBlock_append rec_11_7_2369_1_part0 rec_11_7_2369_1_part1 rfl rfl rfl

private theorem rec_11_7_2369_1 : fastPhase (bank 11 7).shape 179798 2369 10 1 4 12 1 = 5171267948476150390008 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_7_2369_1_join0

theorem receipt_11_7 : Checked (bank 11 7) 10 4 12 := by
  refine checked_from_values (bank 11 7) 10 4 12
    (P3_7_1.checked (bank 11 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_7_2368_0 rec_11_7_2368_1 rec_11_7_2369_0 rec_11_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2368 16 1 4 12 0) 0 128 = 28049576691938318986368 := by decide +kernel
private theorem rec_11_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2368 16 1 4 12 0) 128 63 = 721604524670398298220 := by decide +kernel
private theorem rec_11_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2368 16 1 4 12 0) 0 191 = 28771181216608717284588 :=
  phaseBlock_append rec_11_8_2368_0_part0 rec_11_8_2368_0_part1 rfl rfl rfl

private theorem rec_11_8_2368_0 : fastPhase (bank 11 8).shape 179798 2368 16 1 4 12 0 = 28771181216608717284588 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_11_8_2368_0_join0

private theorem rec_11_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2368 16 1 4 12 1) 0 128 = 27650105138678472584064 := by decide +kernel
private theorem rec_11_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2368 16 1 4 12 1) 128 63 = 679351095918510928908 := by decide +kernel
private theorem rec_11_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2368 16 1 4 12 1) 0 191 = 28329456234596983512972 :=
  phaseBlock_append rec_11_8_2368_1_part0 rec_11_8_2368_1_part1 rfl rfl rfl

private theorem rec_11_8_2368_1 : fastPhase (bank 11 8).shape 179798 2368 16 1 4 12 1 = 28329456234596983512972 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_11_8_2368_1_join0

private theorem rec_11_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2369 16 1 4 12 0) 0 128 = 28049717481473193305472 := by decide +kernel
private theorem rec_11_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2369 16 1 4 12 0) 128 63 = 721603829741367215556 := by decide +kernel
private theorem rec_11_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2369 16 1 4 12 0) 0 191 = 28771321311214560521028 :=
  phaseBlock_append rec_11_8_2369_0_part0 rec_11_8_2369_0_part1 rfl rfl rfl

private theorem rec_11_8_2369_0 : fastPhase (bank 11 8).shape 179798 2369 16 1 4 12 0 = 28771321311214560521028 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_11_8_2369_0_join0

private theorem rec_11_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2369 16 1 4 12 1) 0 128 = 27650242904954973891840 := by decide +kernel
private theorem rec_11_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2369 16 1 4 12 1) 128 63 = 679350436387793227800 := by decide +kernel
private theorem rec_11_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 8).shape 179798 2369 16 1 4 12 1) 0 191 = 28329593341342767119640 :=
  phaseBlock_append rec_11_8_2369_1_part0 rec_11_8_2369_1_part1 rfl rfl rfl

private theorem rec_11_8_2369_1 : fastPhase (bank 11 8).shape 179798 2369 16 1 4 12 1 = 28329593341342767119640 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_11_8_2369_1_join0

theorem receipt_11_8 : Checked (bank 11 8) 16 4 12 := by
  refine checked_from_values (bank 11 8) 16 4 12
    (P3_7_1.checked (bank 11 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_8_2368_0 rec_11_8_2368_1 rec_11_8_2369_0 rec_11_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2368 10 1 4 12 0) 0 128 = 5287009007780046672114 := by decide +kernel
private theorem rec_11_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2368 10 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2368 10 1 4 12 0) 0 130 = 5287009007780046672114 :=
  phaseBlock_append rec_11_9_2368_0_part0 rec_11_9_2368_0_part1 rfl rfl rfl

private theorem rec_11_9_2368_0 : fastPhase (bank 11 9).shape 179798 2368 10 1 4 12 0 = 5287009007780046672114 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_9_2368_0_join0

private theorem rec_11_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2368 10 1 4 12 1) 0 128 = 5171243018737207276242 := by decide +kernel
private theorem rec_11_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2368 10 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2368 10 1 4 12 1) 0 130 = 5171243018737207276242 :=
  phaseBlock_append rec_11_9_2368_1_part0 rec_11_9_2368_1_part1 rfl rfl rfl

private theorem rec_11_9_2368_1 : fastPhase (bank 11 9).shape 179798 2368 10 1 4 12 1 = 5171243018737207276242 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_9_2368_1_join0

private theorem rec_11_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2369 10 1 4 12 0) 0 128 = 5287034720862738891324 := by decide +kernel
private theorem rec_11_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2369 10 1 4 12 0) 128 2 = 0 := by decide +kernel
private theorem rec_11_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2369 10 1 4 12 0) 0 130 = 5287034720862738891324 :=
  phaseBlock_append rec_11_9_2369_0_part0 rec_11_9_2369_0_part1 rfl rfl rfl

private theorem rec_11_9_2369_0 : fastPhase (bank 11 9).shape 179798 2369 10 1 4 12 0 = 5287034720862738891324 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_9_2369_0_join0

private theorem rec_11_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2369 10 1 4 12 1) 0 128 = 5171267948476150390008 := by decide +kernel
private theorem rec_11_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2369 10 1 4 12 1) 128 2 = 0 := by decide +kernel
private theorem rec_11_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 9).shape 179798 2369 10 1 4 12 1) 0 130 = 5171267948476150390008 :=
  phaseBlock_append rec_11_9_2369_1_part0 rec_11_9_2369_1_part1 rfl rfl rfl

private theorem rec_11_9_2369_1 : fastPhase (bank 11 9).shape 179798 2369 10 1 4 12 1 = 5171267948476150390008 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_11_9_2369_1_join0

theorem receipt_11_9 : Checked (bank 11 9) 10 4 12 := by
  refine checked_from_values (bank 11 9) 10 4 12
    (P3_7_1.checked (bank 11 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_9_2368_0 rec_11_9_2368_1 rec_11_9_2369_0 rec_11_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2368 20 1 4 12 0) 0 128 = 57512431403903271622240 := by decide +kernel
private theorem rec_11_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2368 20 1 4 12 0) 128 63 = 1591070884813791979215 := by decide +kernel
private theorem rec_11_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2368 20 1 4 12 0) 0 191 = 59103502288717063601455 :=
  phaseBlock_append rec_11_10_2368_0_part0 rec_11_10_2368_0_part1 rfl rfl rfl

private theorem rec_11_10_2368_0 : fastPhase (bank 11 10).shape 179798 2368 20 1 4 12 0 = 59103502288717063601455 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_11_10_2368_0_join0

private theorem rec_11_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2368 20 1 4 12 1) 0 128 = 56725720372232249506272 := by decide +kernel
private theorem rec_11_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2368 20 1 4 12 1) 128 63 = 1498827104200613288351 := by decide +kernel
private theorem rec_11_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2368 20 1 4 12 1) 0 191 = 58224547476432862794623 :=
  phaseBlock_append rec_11_10_2368_1_part0 rec_11_10_2368_1_part1 rfl rfl rfl

private theorem rec_11_10_2368_1 : fastPhase (bank 11 10).shape 179798 2368 20 1 4 12 1 = 58224547476432862794623 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_11_10_2368_1_join0

private theorem rec_11_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2369 20 1 4 12 0) 0 128 = 57512709156324179707200 := by decide +kernel
private theorem rec_11_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2369 20 1 4 12 0) 128 63 = 1591069189381353879598 := by decide +kernel
private theorem rec_11_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2369 20 1 4 12 0) 0 191 = 59103778345705533586798 :=
  phaseBlock_append rec_11_10_2369_0_part0 rec_11_10_2369_0_part1 rfl rfl rfl

private theorem rec_11_10_2369_0 : fastPhase (bank 11 10).shape 179798 2369 20 1 4 12 0 = 59103778345705533586798 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_11_10_2369_0_join0

private theorem rec_11_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2369 20 1 4 12 1) 0 128 = 56725992286537390741824 := by decide +kernel
private theorem rec_11_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2369 20 1 4 12 1) 128 63 = 1498825495901611821338 := by decide +kernel
private theorem rec_11_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 10).shape 179798 2369 20 1 4 12 1) 0 191 = 58224817782439002563162 :=
  phaseBlock_append rec_11_10_2369_1_part0 rec_11_10_2369_1_part1 rfl rfl rfl

private theorem rec_11_10_2369_1 : fastPhase (bank 11 10).shape 179798 2369 20 1 4 12 1 = 58224817782439002563162 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_11_10_2369_1_join0

theorem receipt_11_10 : Checked (bank 11 10) 20 4 12 := by
  refine checked_from_values (bank 11 10) 20 4 12
    (P3_7_1.checked (bank 11 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_10_2368_0 rec_11_10_2368_1 rec_11_10_2369_0 rec_11_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2368 32 1 4 12 0) 0 128 = 370695249441946959442784 := by decide +kernel
private theorem rec_11_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2368 32 1 4 12 0) 128 128 = 63285601035857490518521 := by decide +kernel
private theorem rec_11_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2368 32 1 4 12 0) 256 22 = 0 := by decide +kernel
private theorem rec_11_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2368 32 1 4 12 0) 128 150 = 63285601035857490518521 :=
  phaseBlock_append rec_11_11_2368_0_part1 rec_11_11_2368_0_part2 rfl rfl rfl
private theorem rec_11_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2368 32 1 4 12 0) 0 278 = 433980850477804449961305 :=
  phaseBlock_append rec_11_11_2368_0_part0 rec_11_11_2368_0_join0 rfl rfl rfl

private theorem rec_11_11_2368_0 : fastPhase (bank 11 11).shape 179798 2368 32 1 4 12 0 = 433980850477804449961305 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_11_11_2368_0_join1

private theorem rec_11_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2368 32 1 4 12 1) 0 128 = 367587861144250945519648 := by decide +kernel
private theorem rec_11_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2368 32 1 4 12 1) 128 128 = 61896363501721141581782 := by decide +kernel
private theorem rec_11_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2368 32 1 4 12 1) 256 22 = 0 := by decide +kernel
private theorem rec_11_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2368 32 1 4 12 1) 128 150 = 61896363501721141581782 :=
  phaseBlock_append rec_11_11_2368_1_part1 rec_11_11_2368_1_part2 rfl rfl rfl
private theorem rec_11_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2368 32 1 4 12 1) 0 278 = 429484224645972087101430 :=
  phaseBlock_append rec_11_11_2368_1_part0 rec_11_11_2368_1_join0 rfl rfl rfl

private theorem rec_11_11_2368_1 : fastPhase (bank 11 11).shape 179798 2368 32 1 4 12 1 = 429484224645972087101430 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_11_11_2368_1_join1

private theorem rec_11_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2369 32 1 4 12 0) 0 128 = 370697233275285217504896 := by decide +kernel
private theorem rec_11_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2369 32 1 4 12 0) 128 128 = 63285619505713891174047 := by decide +kernel
private theorem rec_11_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2369 32 1 4 12 0) 256 22 = 0 := by decide +kernel
private theorem rec_11_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2369 32 1 4 12 0) 128 150 = 63285619505713891174047 :=
  phaseBlock_append rec_11_11_2369_0_part1 rec_11_11_2369_0_part2 rfl rfl rfl
private theorem rec_11_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2369 32 1 4 12 0) 0 278 = 433982852780999108678943 :=
  phaseBlock_append rec_11_11_2369_0_part0 rec_11_11_2369_0_join0 rfl rfl rfl

private theorem rec_11_11_2369_0 : fastPhase (bank 11 11).shape 179798 2369 32 1 4 12 0 = 433982852780999108678943 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_11_11_2369_0_join1

private theorem rec_11_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2369 32 1 4 12 1) 0 128 = 367589816761653119686336 := by decide +kernel
private theorem rec_11_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2369 32 1 4 12 1) 128 128 = 61896381060570802802460 := by decide +kernel
private theorem rec_11_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2369 32 1 4 12 1) 256 22 = 0 := by decide +kernel
private theorem rec_11_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2369 32 1 4 12 1) 128 150 = 61896381060570802802460 :=
  phaseBlock_append rec_11_11_2369_1_part1 rec_11_11_2369_1_part2 rfl rfl rfl
private theorem rec_11_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 11 11).shape 179798 2369 32 1 4 12 1) 0 278 = 429486197822223922488796 :=
  phaseBlock_append rec_11_11_2369_1_part0 rec_11_11_2369_1_join0 rfl rfl rfl

private theorem rec_11_11_2369_1 : fastPhase (bank 11 11).shape 179798 2369 32 1 4 12 1 = 429486197822223922488796 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_11_11_2369_1_join1

theorem receipt_11_11 : Checked (bank 11 11) 32 4 12 := by
  refine checked_from_values (bank 11 11) 32 4 12
    (P3_7_1.checked (bank 11 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_11_2368_0 rec_11_11_2368_1 rec_11_11_2369_0 rec_11_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2368 31 1 4 12 0) 0 128 = 326573637788618974706496 := by decide +kernel
private theorem rec_11_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2368 31 1 4 12 0) 128 128 = 55229214068523798264474 := by decide +kernel
private theorem rec_11_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2368 31 1 4 12 0) 256 22 = 0 := by decide +kernel
private theorem rec_11_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2368 31 1 4 12 0) 128 150 = 55229214068523798264474 :=
  phaseBlock_append rec_11_12_2368_0_part1 rec_11_12_2368_0_part2 rfl rfl rfl
private theorem rec_11_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2368 31 1 4 12 0) 0 278 = 381802851857142772970970 :=
  phaseBlock_append rec_11_12_2368_0_part0 rec_11_12_2368_0_join0 rfl rfl rfl

private theorem rec_11_12_2368_0 : fastPhase (bank 11 12).shape 179798 2368 31 1 4 12 0 = 381802851857142772970970 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_11_12_2368_0_join1

private theorem rec_11_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2368 31 1 4 12 1) 0 128 = 323811811965854136355776 := by decide +kernel
private theorem rec_11_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2368 31 1 4 12 1) 128 128 = 54013150692373115535876 := by decide +kernel
private theorem rec_11_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2368 31 1 4 12 1) 256 22 = 0 := by decide +kernel
private theorem rec_11_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2368 31 1 4 12 1) 128 150 = 54013150692373115535876 :=
  phaseBlock_append rec_11_12_2368_1_part1 rec_11_12_2368_1_part2 rfl rfl rfl
private theorem rec_11_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2368 31 1 4 12 1) 0 278 = 377824962658227251891652 :=
  phaseBlock_append rec_11_12_2368_1_part0 rec_11_12_2368_1_join0 rfl rfl rfl

private theorem rec_11_12_2368_1 : fastPhase (bank 11 12).shape 179798 2368 31 1 4 12 1 = 377824962658227251891652 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_11_12_2368_1_join1

private theorem rec_11_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2369 31 1 4 12 0) 0 128 = 326575395122483668990272 := by decide +kernel
private theorem rec_11_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2369 31 1 4 12 0) 128 128 = 55229231326501060283046 := by decide +kernel
private theorem rec_11_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2369 31 1 4 12 0) 256 22 = 0 := by decide +kernel
private theorem rec_11_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2369 31 1 4 12 0) 128 150 = 55229231326501060283046 :=
  phaseBlock_append rec_11_12_2369_0_part1 rec_11_12_2369_0_part2 rfl rfl rfl
private theorem rec_11_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2369 31 1 4 12 0) 0 278 = 381804626448984729273318 :=
  phaseBlock_append rec_11_12_2369_0_part0 rec_11_12_2369_0_join0 rfl rfl rfl

private theorem rec_11_12_2369_0 : fastPhase (bank 11 12).shape 179798 2369 31 1 4 12 0 = 381804626448984729273318 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_11_12_2369_0_join1

private theorem rec_11_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2369 31 1 4 12 1) 0 128 = 323813544205556463538752 := by decide +kernel
private theorem rec_11_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2369 31 1 4 12 1) 128 128 = 54013167125763895777212 := by decide +kernel
private theorem rec_11_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2369 31 1 4 12 1) 256 22 = 0 := by decide +kernel
private theorem rec_11_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2369 31 1 4 12 1) 128 150 = 54013167125763895777212 :=
  phaseBlock_append rec_11_12_2369_1_part1 rec_11_12_2369_1_part2 rfl rfl rfl
private theorem rec_11_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 11 12).shape 179798 2369 31 1 4 12 1) 0 278 = 377826711331320359315964 :=
  phaseBlock_append rec_11_12_2369_1_part0 rec_11_12_2369_1_join0 rfl rfl rfl

private theorem rec_11_12_2369_1 : fastPhase (bank 11 12).shape 179798 2369 31 1 4 12 1 = 377826711331320359315964 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_11_12_2369_1_join1

theorem receipt_11_12 : Checked (bank 11 12) 31 4 12 := by
  refine checked_from_values (bank 11 12) 31 4 12
    (P3_7_1.checked (bank 11 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_12_2368_0 rec_11_12_2368_1 rec_11_12_2369_0 rec_11_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2368 44 1 4 12 0) 0 128 = 1468619317385941573373664 := by decide +kernel
private theorem rec_11_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2368 44 1 4 12 0) 128 128 = 506593412102264507055840 := by decide +kernel
private theorem rec_11_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2368 44 1 4 12 0) 256 114 = 39463298247723365343426 := by decide +kernel
private theorem rec_11_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2368 44 1 4 12 0) 128 242 = 546056710349987872399266 :=
  phaseBlock_append rec_11_13_2368_0_part1 rec_11_13_2368_0_part2 rfl rfl rfl
private theorem rec_11_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2368 44 1 4 12 0) 0 370 = 2014676027735929445772930 :=
  phaseBlock_append rec_11_13_2368_0_part0 rec_11_13_2368_0_join0 rfl rfl rfl

private theorem rec_11_13_2368_0 : fastPhase (bank 11 13).shape 179798 2368 44 1 4 12 0 = 2014676027735929445772930 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_11_13_2368_0_join1

private theorem rec_11_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2368 44 1 4 12 1) 0 128 = 1460001264310534624795680 := by decide +kernel
private theorem rec_11_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2368 44 1 4 12 1) 128 128 = 500727737652305877634080 := by decide +kernel
private theorem rec_11_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2368 44 1 4 12 1) 256 114 = 38136273219224336325015 := by decide +kernel
private theorem rec_11_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2368 44 1 4 12 1) 128 242 = 538864010871530213959095 :=
  phaseBlock_append rec_11_13_2368_1_part1 rec_11_13_2368_1_part2 rfl rfl rfl
private theorem rec_11_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2368 44 1 4 12 1) 0 370 = 1998865275182064838754775 :=
  phaseBlock_append rec_11_13_2368_1_part0 rec_11_13_2368_1_join0 rfl rfl rfl

private theorem rec_11_13_2368_1 : fastPhase (bank 11 13).shape 179798 2368 44 1 4 12 1 = 1998865275182064838754775 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_11_13_2368_1_join1

private theorem rec_11_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2369 44 1 4 12 0) 0 128 = 1468627958247439803083136 := by decide +kernel
private theorem rec_11_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2369 44 1 4 12 0) 128 128 = 506594107465637355596160 := by decide +kernel
private theorem rec_11_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2369 44 1 4 12 0) 256 114 = 39463248062994419493504 := by decide +kernel
private theorem rec_11_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2369 44 1 4 12 0) 128 242 = 546057355528631775089664 :=
  phaseBlock_append rec_11_13_2369_0_part1 rec_11_13_2369_0_part2 rfl rfl rfl
private theorem rec_11_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2369 44 1 4 12 0) 0 370 = 2014685313776071578172800 :=
  phaseBlock_append rec_11_13_2369_0_part0 rec_11_13_2369_0_join0 rfl rfl rfl

private theorem rec_11_13_2369_0 : fastPhase (bank 11 13).shape 179798 2369 44 1 4 12 0 = 2014685313776071578172800 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_11_13_2369_0_join1

private theorem rec_11_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2369 44 1 4 12 1) 0 128 = 1460009815511895442313664 := by decide +kernel
private theorem rec_11_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2369 44 1 4 12 1) 128 128 = 500728418795057753526720 := by decide +kernel
private theorem rec_11_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2369 44 1 4 12 1) 256 114 = 38136224585463046316241 := by decide +kernel
private theorem rec_11_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2369 44 1 4 12 1) 128 242 = 538864643380520799842961 :=
  phaseBlock_append rec_11_13_2369_1_part1 rec_11_13_2369_1_part2 rfl rfl rfl
private theorem rec_11_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 11 13).shape 179798 2369 44 1 4 12 1) 0 370 = 1998874458892416242156625 :=
  phaseBlock_append rec_11_13_2369_1_part0 rec_11_13_2369_1_join0 rfl rfl rfl

private theorem rec_11_13_2369_1 : fastPhase (bank 11 13).shape 179798 2369 44 1 4 12 1 = 1998874458892416242156625 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_11_13_2369_1_join1

theorem receipt_11_13 : Checked (bank 11 13) 44 4 12 := by
  refine checked_from_values (bank 11 13) 44 4 12
    (P3_7_1.checked (bank 11 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_13_2368_0 rec_11_13_2368_1 rec_11_13_2369_0 rec_11_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 0 128 = 20536771870775426042629664 := by decide +kernel
private theorem rec_11_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 128 128 = 13002796118358280950742560 := by decide +kernel
private theorem rec_11_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 256 128 = 6810505881859969770450464 := by decide +kernel
private theorem rec_11_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 384 128 = 2486188923133975653277216 := by decide +kernel
private theorem rec_11_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 512 128 = 303275208721964417213071 := by decide +kernel
private theorem rec_11_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 640 38 = 0 := by decide +kernel
private theorem rec_11_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 128 256 = 19813302000218250721193024 :=
  phaseBlock_append rec_11_14_2368_0_part1 rec_11_14_2368_0_part2 rfl rfl rfl
private theorem rec_11_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 0 384 = 40350073870993676763822688 :=
  phaseBlock_append rec_11_14_2368_0_part0 rec_11_14_2368_0_join0 rfl rfl rfl
private theorem rec_11_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 512 166 = 303275208721964417213071 :=
  phaseBlock_append rec_11_14_2368_0_part4 rec_11_14_2368_0_part5 rfl rfl rfl
private theorem rec_11_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 384 294 = 2789464131855940070490287 :=
  phaseBlock_append rec_11_14_2368_0_part3 rec_11_14_2368_0_join2 rfl rfl rfl
private theorem rec_11_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 0) 0 678 = 43139538002849616834312975 :=
  phaseBlock_append rec_11_14_2368_0_join1 rec_11_14_2368_0_join3 rfl rfl rfl

private theorem rec_11_14_2368_0 : fastPhase (bank 11 14).shape 179798 2368 76 1 4 12 0 = 43139538002849616834312975 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_11_14_2368_0_join4

private theorem rec_11_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 0 128 = 20475150869617171101693856 := by decide +kernel
private theorem rec_11_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 128 128 = 12948626307207524300285856 := by decide +kernel
private theorem rec_11_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 256 128 = 6769112772252428101556128 := by decide +kernel
private theorem rec_11_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 384 128 = 2460642156241500128888736 := by decide +kernel
private theorem rec_11_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 512 128 = 295351925708992142694795 := by decide +kernel
private theorem rec_11_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 640 38 = 0 := by decide +kernel
private theorem rec_11_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 128 256 = 19717739079459952401841984 :=
  phaseBlock_append rec_11_14_2368_1_part1 rec_11_14_2368_1_part2 rfl rfl rfl
private theorem rec_11_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 0 384 = 40192889949077123503535840 :=
  phaseBlock_append rec_11_14_2368_1_part0 rec_11_14_2368_1_join0 rfl rfl rfl
private theorem rec_11_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 512 166 = 295351925708992142694795 :=
  phaseBlock_append rec_11_14_2368_1_part4 rec_11_14_2368_1_part5 rfl rfl rfl
private theorem rec_11_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 384 294 = 2755994081950492271583531 :=
  phaseBlock_append rec_11_14_2368_1_part3 rec_11_14_2368_1_join2 rfl rfl rfl
private theorem rec_11_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2368 76 1 4 12 1) 0 678 = 42948884031027615775119371 :=
  phaseBlock_append rec_11_14_2368_1_join1 rec_11_14_2368_1_join3 rfl rfl rfl

private theorem rec_11_14_2368_1 : fastPhase (bank 11 14).shape 179798 2368 76 1 4 12 1 = 42948884031027615775119371 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_11_14_2368_1_join4

private theorem rec_11_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 0 128 = 20536914911560392307948992 := by decide +kernel
private theorem rec_11_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 128 128 = 13002846867031466726645184 := by decide +kernel
private theorem rec_11_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 256 128 = 6810516442269982001921472 := by decide +kernel
private theorem rec_11_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 384 128 = 2486188213999461168979392 := by decide +kernel
private theorem rec_11_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 512 128 = 303274720359846841535766 := by decide +kernel
private theorem rec_11_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 640 38 = 0 := by decide +kernel
private theorem rec_11_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 128 256 = 19813363309301448728566656 :=
  phaseBlock_append rec_11_14_2369_0_part1 rec_11_14_2369_0_part2 rfl rfl rfl
private theorem rec_11_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 0 384 = 40350278220861841036515648 :=
  phaseBlock_append rec_11_14_2369_0_part0 rec_11_14_2369_0_join0 rfl rfl rfl
private theorem rec_11_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 512 166 = 303274720359846841535766 :=
  phaseBlock_append rec_11_14_2369_0_part4 rec_11_14_2369_0_part5 rfl rfl rfl
private theorem rec_11_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 384 294 = 2789462934359308010515158 :=
  phaseBlock_append rec_11_14_2369_0_part3 rec_11_14_2369_0_join2 rfl rfl rfl
private theorem rec_11_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 0) 0 678 = 43139741155221149047030806 :=
  phaseBlock_append rec_11_14_2369_0_join1 rec_11_14_2369_0_join3 rfl rfl rfl

private theorem rec_11_14_2369_0 : fastPhase (bank 11 14).shape 179798 2369 76 1 4 12 0 = 43139741155221149047030806 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_11_14_2369_0_join4

private theorem rec_11_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 0 128 = 20475293130798188573890368 := by decide +kernel
private theorem rec_11_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 128 128 = 12948676692916804274878272 := by decide +kernel
private theorem rec_11_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 256 128 = 6769123213890215573575488 := by decide +kernel
private theorem rec_11_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 384 128 = 2460641441618330427832128 := by decide +kernel
private theorem rec_11_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 512 128 = 295351449617898312701958 := by decide +kernel
private theorem rec_11_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 640 38 = 0 := by decide +kernel
private theorem rec_11_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 128 256 = 19717799906807019848453760 :=
  phaseBlock_append rec_11_14_2369_1_part1 rec_11_14_2369_1_part2 rfl rfl rfl
private theorem rec_11_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 0 384 = 40193093037605208422344128 :=
  phaseBlock_append rec_11_14_2369_1_part0 rec_11_14_2369_1_join0 rfl rfl rfl
private theorem rec_11_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 512 166 = 295351449617898312701958 :=
  phaseBlock_append rec_11_14_2369_1_part4 rec_11_14_2369_1_part5 rfl rfl rfl
private theorem rec_11_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 384 294 = 2755992891236228740534086 :=
  phaseBlock_append rec_11_14_2369_1_part3 rec_11_14_2369_1_join2 rfl rfl rfl
private theorem rec_11_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 11 14).shape 179798 2369 76 1 4 12 1) 0 678 = 42949085928841437162878214 :=
  phaseBlock_append rec_11_14_2369_1_join1 rec_11_14_2369_1_join3 rfl rfl rfl

private theorem rec_11_14_2369_1 : fastPhase (bank 11 14).shape 179798 2369 76 1 4 12 1 = 42949085928841437162878214 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_11_14_2369_1_join4

theorem receipt_11_14 : Checked (bank 11 14) 76 4 12 := by
  refine checked_from_values (bank 11 14) 76 4 12
    (P3_7_1.checked (bank 11 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_14_2368_0 rec_11_14_2368_1 rec_11_14_2369_0 rec_11_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 0 128 = 95606876553858653103862912 := by decide +kernel
private theorem rec_11_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 128 128 = 70126078439135584618280064 := by decide +kernel
private theorem rec_11_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 256 128 = 47276915948127497241474176 := by decide +kernel
private theorem rec_11_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 384 128 = 28233669053607153276777600 := by decide +kernel
private theorem rec_11_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 512 128 = 13784583242388970730370176 := by decide +kernel
private theorem rec_11_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 640 128 = 4369369474387075286365312 := by decide +kernel
private theorem rec_11_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 768 128 = 274919877648911121951564 := by decide +kernel
private theorem rec_11_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 896 29 = 0 := by decide +kernel
private theorem rec_11_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 0 256 = 165732954992994237722142976 :=
  phaseBlock_append rec_11_15_2368_0_part0 rec_11_15_2368_0_part1 rfl rfl rfl
private theorem rec_11_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 256 256 = 75510585001734650518251776 :=
  phaseBlock_append rec_11_15_2368_0_part2 rec_11_15_2368_0_part3 rfl rfl rfl
private theorem rec_11_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 0 512 = 241243539994728888240394752 :=
  phaseBlock_append rec_11_15_2368_0_join0 rec_11_15_2368_0_join1 rfl rfl rfl
private theorem rec_11_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 512 256 = 18153952716776046016735488 :=
  phaseBlock_append rec_11_15_2368_0_part4 rec_11_15_2368_0_part5 rfl rfl rfl
private theorem rec_11_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 768 157 = 274919877648911121951564 :=
  phaseBlock_append rec_11_15_2368_0_part6 rec_11_15_2368_0_part7 rfl rfl rfl
private theorem rec_11_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 512 413 = 18428872594424957138687052 :=
  phaseBlock_append rec_11_15_2368_0_join3 rec_11_15_2368_0_join4 rfl rfl rfl
private theorem rec_11_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 0) 0 925 = 259672412589153845379081804 :=
  phaseBlock_append rec_11_15_2368_0_join2 rec_11_15_2368_0_join5 rfl rfl rfl

private theorem rec_11_15_2368_0 : fastPhase (bank 11 15).shape 179798 2368 105 1 4 12 0 = 259672412589153845379081804 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_11_15_2368_0_join6

private theorem rec_11_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 0 128 = 95403202531540955652497792 := by decide +kernel
private theorem rec_11_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 128 128 = 69936746253674257504362880 := by decide +kernel
private theorem rec_11_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 256 128 = 47112840666564840949916032 := by decide +kernel
private theorem rec_11_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 384 128 = 28102584088245777896169856 := by decide +kernel
private theorem rec_11_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 512 128 = 13691334584592694786793856 := by decide +kernel
private theorem rec_11_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 640 128 = 4316209928381824577200512 := by decide +kernel
private theorem rec_11_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 768 128 = 264222270405412178168452 := by decide +kernel
private theorem rec_11_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 896 29 = 0 := by decide +kernel
private theorem rec_11_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 0 256 = 165339948785215213156860672 :=
  phaseBlock_append rec_11_15_2368_1_part0 rec_11_15_2368_1_part1 rfl rfl rfl
private theorem rec_11_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 256 256 = 75215424754810618846085888 :=
  phaseBlock_append rec_11_15_2368_1_part2 rec_11_15_2368_1_part3 rfl rfl rfl
private theorem rec_11_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 0 512 = 240555373540025832002946560 :=
  phaseBlock_append rec_11_15_2368_1_join0 rec_11_15_2368_1_join1 rfl rfl rfl
private theorem rec_11_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 512 256 = 18007544512974519363994368 :=
  phaseBlock_append rec_11_15_2368_1_part4 rec_11_15_2368_1_part5 rfl rfl rfl
private theorem rec_11_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 768 157 = 264222270405412178168452 :=
  phaseBlock_append rec_11_15_2368_1_part6 rec_11_15_2368_1_part7 rfl rfl rfl
private theorem rec_11_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 512 413 = 18271766783379931542162820 :=
  phaseBlock_append rec_11_15_2368_1_join3 rec_11_15_2368_1_join4 rfl rfl rfl
private theorem rec_11_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2368 105 1 4 12 1) 0 925 = 258827140323405763545109380 :=
  phaseBlock_append rec_11_15_2368_1_join2 rec_11_15_2368_1_join5 rfl rfl rfl

private theorem rec_11_15_2368_1 : fastPhase (bank 11 15).shape 179798 2368 105 1 4 12 1 = 258827140323405763545109380 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_11_15_2368_1_join6

private theorem rec_11_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 0 128 = 95607580104728920979944896 := by decide +kernel
private theorem rec_11_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 128 128 = 70126425402096150403208640 := by decide +kernel
private theorem rec_11_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 256 128 = 47277056556176941270136256 := by decide +kernel
private theorem rec_11_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 384 128 = 28233706662987831516665280 := by decide +kernel
private theorem rec_11_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 512 128 = 13784582580091079816558016 := by decide +kernel
private theorem rec_11_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 640 128 = 4369364246000832981521856 := by decide +kernel
private theorem rec_11_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 768 128 = 274919318240544889927674 := by decide +kernel
private theorem rec_11_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 896 29 = 0 := by decide +kernel
private theorem rec_11_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 0 256 = 165734005506825071383153536 :=
  phaseBlock_append rec_11_15_2369_0_part0 rec_11_15_2369_0_part1 rfl rfl rfl
private theorem rec_11_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 256 256 = 75510763219164772786801536 :=
  phaseBlock_append rec_11_15_2369_0_part2 rec_11_15_2369_0_part3 rfl rfl rfl
private theorem rec_11_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 0 512 = 241244768725989844169955072 :=
  phaseBlock_append rec_11_15_2369_0_join0 rec_11_15_2369_0_join1 rfl rfl rfl
private theorem rec_11_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 512 256 = 18153946826091912798079872 :=
  phaseBlock_append rec_11_15_2369_0_part4 rec_11_15_2369_0_part5 rfl rfl rfl
private theorem rec_11_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 768 157 = 274919318240544889927674 :=
  phaseBlock_append rec_11_15_2369_0_part6 rec_11_15_2369_0_part7 rfl rfl rfl
private theorem rec_11_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 512 413 = 18428866144332457688007546 :=
  phaseBlock_append rec_11_15_2369_0_join3 rec_11_15_2369_0_join4 rfl rfl rfl
private theorem rec_11_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 0) 0 925 = 259673634870322301857962618 :=
  phaseBlock_append rec_11_15_2369_0_join2 rec_11_15_2369_0_join5 rfl rfl rfl

private theorem rec_11_15_2369_0 : fastPhase (bank 11 15).shape 179798 2369 105 1 4 12 0 = 259673634870322301857962618 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_11_15_2369_0_join6

private theorem rec_11_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 0 128 = 95403903324719639976248384 := by decide +kernel
private theorem rec_11_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 128 128 = 69937091583030342908077120 := by decide +kernel
private theorem rec_11_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 256 128 = 47112980427897523874186304 := by decide +kernel
private theorem rec_11_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 384 128 = 28102621358887248865076288 := by decide +kernel
private theorem rec_11_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 512 128 = 13691333866449285745738816 := by decide +kernel
private theorem rec_11_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 640 128 = 4316204751323271655777344 := by decide +kernel
private theorem rec_11_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 768 128 = 264221732513767461122470 := by decide +kernel
private theorem rec_11_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 896 29 = 0 := by decide +kernel
private theorem rec_11_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 0 256 = 165340994907749982884325504 :=
  phaseBlock_append rec_11_15_2369_1_part0 rec_11_15_2369_1_part1 rfl rfl rfl
private theorem rec_11_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 256 256 = 75215601786784772739262592 :=
  phaseBlock_append rec_11_15_2369_1_part2 rec_11_15_2369_1_part3 rfl rfl rfl
private theorem rec_11_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 0 512 = 240556596694534755623588096 :=
  phaseBlock_append rec_11_15_2369_1_join0 rec_11_15_2369_1_join1 rfl rfl rfl
private theorem rec_11_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 512 256 = 18007538617772557401516160 :=
  phaseBlock_append rec_11_15_2369_1_part4 rec_11_15_2369_1_part5 rfl rfl rfl
private theorem rec_11_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 768 157 = 264221732513767461122470 :=
  phaseBlock_append rec_11_15_2369_1_part6 rec_11_15_2369_1_part7 rfl rfl rfl
private theorem rec_11_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 512 413 = 18271760350286324862638630 :=
  phaseBlock_append rec_11_15_2369_1_join3 rec_11_15_2369_1_join4 rfl rfl rfl
private theorem rec_11_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 11 15).shape 179798 2369 105 1 4 12 1) 0 925 = 258828357044821080486226726 :=
  phaseBlock_append rec_11_15_2369_1_join2 rec_11_15_2369_1_join5 rfl rfl rfl

private theorem rec_11_15_2369_1 : fastPhase (bank 11 15).shape 179798 2369 105 1 4 12 1 = 258828357044821080486226726 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_11_15_2369_1_join6

theorem receipt_11_15 : Checked (bank 11 15) 105 4 12 := by
  refine checked_from_values (bank 11 15) 105 4 12
    (P3_7_1.checked (bank 11 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_15_2368_0 rec_11_15_2368_1 rec_11_15_2369_0 rec_11_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_11_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 0 128 = 290176967327095973824674720 := by decide +kernel
private theorem rec_11_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 128 128 = 219347901231958071745219488 := by decide +kernel
private theorem rec_11_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 256 128 = 152649176950885375218637728 := by decide +kernel
private theorem rec_11_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 384 128 = 94264070285773860696370080 := by decide +kernel
private theorem rec_11_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 512 128 = 47667027241454116962499488 := by decide +kernel
private theorem rec_11_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 640 128 = 15661163984749397108837280 := by decide +kernel
private theorem rec_11_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 768 128 = 1016340894185169406610337 := by decide +kernel
private theorem rec_11_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 896 29 = 0 := by decide +kernel
private theorem rec_11_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 0 256 = 509524868559054045569894208 :=
  phaseBlock_append rec_11_16_2368_0_part0 rec_11_16_2368_0_part1 rfl rfl rfl
private theorem rec_11_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 256 256 = 246913247236659235915007808 :=
  phaseBlock_append rec_11_16_2368_0_part2 rec_11_16_2368_0_part3 rfl rfl rfl
private theorem rec_11_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 0 512 = 756438115795713281484902016 :=
  phaseBlock_append rec_11_16_2368_0_join0 rec_11_16_2368_0_join1 rfl rfl rfl
private theorem rec_11_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 512 256 = 63328191226203514071336768 :=
  phaseBlock_append rec_11_16_2368_0_part4 rec_11_16_2368_0_part5 rfl rfl rfl
private theorem rec_11_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 768 157 = 1016340894185169406610337 :=
  phaseBlock_append rec_11_16_2368_0_part6 rec_11_16_2368_0_part7 rfl rfl rfl
private theorem rec_11_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 512 413 = 64344532120388683477947105 :=
  phaseBlock_append rec_11_16_2368_0_join3 rec_11_16_2368_0_join4 rfl rfl rfl
private theorem rec_11_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 0) 0 925 = 820782647916101964962849121 :=
  phaseBlock_append rec_11_16_2368_0_join2 rec_11_16_2368_0_join5 rfl rfl rfl

private theorem rec_11_16_2368_0 : fastPhase (bank 11 16).shape 179798 2368 138 1 4 12 0 = 820782647916101964962849121 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_11_16_2368_0_join6

private theorem rec_11_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 0 128 = 289625174615698923078045024 := by decide +kernel
private theorem rec_11_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 128 128 = 218808550789651131465571680 := by decide +kernel
private theorem rec_11_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 256 128 = 152158166706629181368364384 := by decide +kernel
private theorem rec_11_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 384 128 = 93851581061976170553163104 := by decide +kernel
private theorem rec_11_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 512 128 = 47357816987770707953159520 := by decide +kernel
private theorem rec_11_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 640 128 = 15474862011884965643083104 := by decide +kernel
private theorem rec_11_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 768 128 = 977017374883598421718356 := by decide +kernel
private theorem rec_11_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 896 29 = 0 := by decide +kernel
private theorem rec_11_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 0 256 = 508433725405350054543616704 :=
  phaseBlock_append rec_11_16_2368_1_part0 rec_11_16_2368_1_part1 rfl rfl rfl
private theorem rec_11_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 256 256 = 246009747768605351921527488 :=
  phaseBlock_append rec_11_16_2368_1_part2 rec_11_16_2368_1_part3 rfl rfl rfl
private theorem rec_11_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 0 512 = 754443473173955406465144192 :=
  phaseBlock_append rec_11_16_2368_1_join0 rec_11_16_2368_1_join1 rfl rfl rfl
private theorem rec_11_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 512 256 = 62832678999655673596242624 :=
  phaseBlock_append rec_11_16_2368_1_part4 rec_11_16_2368_1_part5 rfl rfl rfl
private theorem rec_11_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 768 157 = 977017374883598421718356 :=
  phaseBlock_append rec_11_16_2368_1_part6 rec_11_16_2368_1_part7 rfl rfl rfl
private theorem rec_11_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 512 413 = 63809696374539272017960980 :=
  phaseBlock_append rec_11_16_2368_1_join3 rec_11_16_2368_1_join4 rfl rfl rfl
private theorem rec_11_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2368 138 1 4 12 1) 0 925 = 818253169548494678483105172 :=
  phaseBlock_append rec_11_16_2368_1_join2 rec_11_16_2368_1_join5 rfl rfl rfl

private theorem rec_11_16_2368_1 : fastPhase (bank 11 16).shape 179798 2368 138 1 4 12 1 = 818253169548494678483105172 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_11_16_2368_1_join6

private theorem rec_11_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 0 128 = 290179026927314240753324160 := by decide +kernel
private theorem rec_11_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 128 128 = 219348934669531982737199232 := by decide +kernel
private theorem rec_11_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 256 128 = 152649597997964471707193472 := by decide +kernel
private theorem rec_11_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 384 128 = 94264177116963513449992320 := by decide +kernel
private theorem rec_11_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 512 128 = 47667016169022807280144512 := by decide +kernel
private theorem rec_11_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 640 128 = 15661142554184113440182400 := by decide +kernel
private theorem rec_11_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 768 128 = 1016338662973891750003983 := by decide +kernel
private theorem rec_11_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 896 29 = 0 := by decide +kernel
private theorem rec_11_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 0 256 = 509527961596846223490523392 :=
  phaseBlock_append rec_11_16_2369_0_part0 rec_11_16_2369_0_part1 rfl rfl rfl
private theorem rec_11_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 256 256 = 246913775114927985157185792 :=
  phaseBlock_append rec_11_16_2369_0_part2 rec_11_16_2369_0_part3 rfl rfl rfl
private theorem rec_11_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 0 512 = 756441736711774208647709184 :=
  phaseBlock_append rec_11_16_2369_0_join0 rec_11_16_2369_0_join1 rfl rfl rfl
private theorem rec_11_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 512 256 = 63328158723206920720326912 :=
  phaseBlock_append rec_11_16_2369_0_part4 rec_11_16_2369_0_part5 rfl rfl rfl
private theorem rec_11_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 768 157 = 1016338662973891750003983 :=
  phaseBlock_append rec_11_16_2369_0_part6 rec_11_16_2369_0_part7 rfl rfl rfl
private theorem rec_11_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 512 413 = 64344497386180812470330895 :=
  phaseBlock_append rec_11_16_2369_0_join3 rec_11_16_2369_0_join4 rfl rfl rfl
private theorem rec_11_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 0) 0 925 = 820786234097955021118040079 :=
  phaseBlock_append rec_11_16_2369_0_join2 rec_11_16_2369_0_join5 rfl rfl rfl

private theorem rec_11_16_2369_0 : fastPhase (bank 11 16).shape 179798 2369 138 1 4 12 0 = 820786234097955021118040079 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_11_16_2369_0_join6

private theorem rec_11_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 0 128 = 289627226541740657878271040 := by decide +kernel
private theorem rec_11_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 128 128 = 218809579545489098745414720 := by decide +kernel
private theorem rec_11_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 256 128 = 152158585263663914921133120 := by decide +kernel
private theorem rec_11_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 384 128 = 93851686889477012234667072 := by decide +kernel
private theorem rec_11_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 512 128 = 47357805783620171179787328 := by decide +kernel
private theorem rec_11_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 640 128 = 15474840793671214314914880 := by decide +kernel
private theorem rec_11_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 768 128 = 977015229150741476822577 := by decide +kernel
private theorem rec_11_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 896 29 = 0 := by decide +kernel
private theorem rec_11_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 0 256 = 508436806087229756623685760 :=
  phaseBlock_append rec_11_16_2369_1_part0 rec_11_16_2369_1_part1 rfl rfl rfl
private theorem rec_11_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 256 256 = 246010272153140927155800192 :=
  phaseBlock_append rec_11_16_2369_1_part2 rec_11_16_2369_1_part3 rfl rfl rfl
private theorem rec_11_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 0 512 = 754447078240370683779485952 :=
  phaseBlock_append rec_11_16_2369_1_join0 rec_11_16_2369_1_join1 rfl rfl rfl
private theorem rec_11_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 512 256 = 62832646577291385494702208 :=
  phaseBlock_append rec_11_16_2369_1_part4 rec_11_16_2369_1_part5 rfl rfl rfl
private theorem rec_11_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 768 157 = 977015229150741476822577 :=
  phaseBlock_append rec_11_16_2369_1_part6 rec_11_16_2369_1_part7 rfl rfl rfl
private theorem rec_11_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 512 413 = 63809661806442126971524785 :=
  phaseBlock_append rec_11_16_2369_1_join3 rec_11_16_2369_1_join4 rfl rfl rfl
private theorem rec_11_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 11 16).shape 179798 2369 138 1 4 12 1) 0 925 = 818256740046812810751010737 :=
  phaseBlock_append rec_11_16_2369_1_join2 rec_11_16_2369_1_join5 rfl rfl rfl

private theorem rec_11_16_2369_1 : fastPhase (bank 11 16).shape 179798 2369 138 1 4 12 1 = 818256740046812810751010737 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_11_16_2369_1_join6

theorem receipt_11_16 : Checked (bank 11 16) 138 4 12 := by
  refine checked_from_values (bank 11 16) 138 4 12
    (P3_7_1.checked (bank 11 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_11_16_2368_0 rec_11_16_2368_1 rec_11_16_2369_0 rec_11_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect11_checked (i : Fin 17) :
    Checked (bank 11 i) (reserve i) (excess 11) (seed 11) := by
  fin_cases i
  · exact receipt_11_0
  · exact receipt_11_1
  · exact receipt_11_2
  · exact receipt_11_3
  · exact receipt_11_4
  · exact receipt_11_5
  · exact receipt_11_6
  · exact receipt_11_7
  · exact receipt_11_8
  · exact receipt_11_9
  · exact receipt_11_10
  · exact receipt_11_11
  · exact receipt_11_12
  · exact receipt_11_13
  · exact receipt_11_14
  · exact receipt_11_15
  · exact receipt_11_16

end Lower6961.Lo.RescueSource
