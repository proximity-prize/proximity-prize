import ProximityPrize.SubmissionLower.R6961LoRescueSourceSchedule
import ProximityPrize.SubmissionLower.R6963LoFastLayerNat
import ProximityPrize.SubmissionLower.R6961LoRescuePoolMoments0
import ProximityPrize.SubmissionLower.R6961LoRescuePoolMoments1

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


private theorem rec_8_0_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2368 0 1 0 41 0) 0 128 = 853945144856056731296 := by decide +kernel
private theorem rec_8_0_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2368 0 1 0 41 0) 128 63 = 0 := by decide +kernel
private theorem rec_8_0_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2368 0 1 0 41 0) 0 191 = 853945144856056731296 :=
  phaseBlock_append rec_8_0_2368_0_part0 rec_8_0_2368_0_part1 rfl rfl rfl

private theorem rec_8_0_2368_0 : fastPhase (bank 8 0).shape 179798 2368 0 1 0 41 0 = 853945144856056731296 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_8_0_2368_0_join0

private theorem rec_8_0_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2368 0 1 0 41 1) 0 128 = 817030104301307856960 := by decide +kernel
private theorem rec_8_0_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2368 0 1 0 41 1) 128 63 = 0 := by decide +kernel
private theorem rec_8_0_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2368 0 1 0 41 1) 0 191 = 817030104301307856960 :=
  phaseBlock_append rec_8_0_2368_1_part0 rec_8_0_2368_1_part1 rfl rfl rfl

private theorem rec_8_0_2368_1 : fastPhase (bank 8 0).shape 179798 2368 0 1 0 41 1 = 817030104301307856960 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_8_0_2368_1_join0

private theorem rec_8_0_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2369 0 1 0 41 0) 0 128 = 853952848989706996894 := by decide +kernel
private theorem rec_8_0_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2369 0 1 0 41 0) 128 63 = 0 := by decide +kernel
private theorem rec_8_0_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2369 0 1 0 41 0) 0 191 = 853952848989706996894 :=
  phaseBlock_append rec_8_0_2369_0_part0 rec_8_0_2369_0_part1 rfl rfl rfl

private theorem rec_8_0_2369_0 : fastPhase (bank 8 0).shape 179798 2369 0 1 0 41 0 = 853952848989706996894 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_8_0_2369_0_join0

private theorem rec_8_0_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2369 0 1 0 41 1) 0 128 = 817037489950725083040 := by decide +kernel
private theorem rec_8_0_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2369 0 1 0 41 1) 128 63 = 0 := by decide +kernel
private theorem rec_8_0_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 0).shape 179798 2369 0 1 0 41 1) 0 191 = 817037489950725083040 :=
  phaseBlock_append rec_8_0_2369_1_part0 rec_8_0_2369_1_part1 rfl rfl rfl

private theorem rec_8_0_2369_1 : fastPhase (bank 8 0).shape 179798 2369 0 1 0 41 1 = 817037489950725083040 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_8_0_2369_1_join0

theorem receipt_8_0 : Checked (bank 8 0) 0 0 41 := by
  refine checked_from_values (bank 8 0) 0 0 41
    (P3_7_1.checked (bank 8 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_0_2368_0 rec_8_0_2368_1 rec_8_0_2369_0 rec_8_0_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2368 1 1 0 41 0) 0 128 = 6797134592031587903790 := by decide +kernel
private theorem rec_8_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2368 1 1 0 41 0) 128 128 = 0 := by decide +kernel
private theorem rec_8_1_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2368 1 1 0 41 0) 256 22 = 0 := by decide +kernel
private theorem rec_8_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2368 1 1 0 41 0) 128 150 = 0 :=
  phaseBlock_append rec_8_1_2368_0_part1 rec_8_1_2368_0_part2 rfl rfl rfl
private theorem rec_8_1_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2368 1 1 0 41 0) 0 278 = 6797134592031587903790 :=
  phaseBlock_append rec_8_1_2368_0_part0 rec_8_1_2368_0_join0 rfl rfl rfl

private theorem rec_8_1_2368_0 : fastPhase (bank 8 1).shape 179798 2368 1 1 0 41 0 = 6797134592031587903790 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_1_2368_0_join1

private theorem rec_8_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2368 1 1 0 41 1) 0 128 = 6583611279516011574597 := by decide +kernel
private theorem rec_8_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2368 1 1 0 41 1) 128 128 = 0 := by decide +kernel
private theorem rec_8_1_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2368 1 1 0 41 1) 256 22 = 0 := by decide +kernel
private theorem rec_8_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2368 1 1 0 41 1) 128 150 = 0 :=
  phaseBlock_append rec_8_1_2368_1_part1 rec_8_1_2368_1_part2 rfl rfl rfl
private theorem rec_8_1_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2368 1 1 0 41 1) 0 278 = 6583611279516011574597 :=
  phaseBlock_append rec_8_1_2368_1_part0 rec_8_1_2368_1_join0 rfl rfl rfl

private theorem rec_8_1_2368_1 : fastPhase (bank 8 1).shape 179798 2368 1 1 0 41 1 = 6583611279516011574597 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_1_2368_1_join1

private theorem rec_8_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2369 1 1 0 41 0) 0 128 = 6797195899441377265854 := by decide +kernel
private theorem rec_8_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2369 1 1 0 41 0) 128 128 = 0 := by decide +kernel
private theorem rec_8_1_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2369 1 1 0 41 0) 256 22 = 0 := by decide +kernel
private theorem rec_8_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2369 1 1 0 41 0) 128 150 = 0 :=
  phaseBlock_append rec_8_1_2369_0_part1 rec_8_1_2369_0_part2 rfl rfl rfl
private theorem rec_8_1_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2369 1 1 0 41 0) 0 278 = 6797195899441377265854 :=
  phaseBlock_append rec_8_1_2369_0_part0 rec_8_1_2369_0_join0 rfl rfl rfl

private theorem rec_8_1_2369_0 : fastPhase (bank 8 1).shape 179798 2369 1 1 0 41 0 = 6797195899441377265854 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_1_2369_0_join1

private theorem rec_8_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2369 1 1 0 41 1) 0 128 = 6583670742012010339653 := by decide +kernel
private theorem rec_8_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2369 1 1 0 41 1) 128 128 = 0 := by decide +kernel
private theorem rec_8_1_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2369 1 1 0 41 1) 256 22 = 0 := by decide +kernel
private theorem rec_8_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2369 1 1 0 41 1) 128 150 = 0 :=
  phaseBlock_append rec_8_1_2369_1_part1 rec_8_1_2369_1_part2 rfl rfl rfl
private theorem rec_8_1_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 1).shape 179798 2369 1 1 0 41 1) 0 278 = 6583670742012010339653 :=
  phaseBlock_append rec_8_1_2369_1_part0 rec_8_1_2369_1_join0 rfl rfl rfl

private theorem rec_8_1_2369_1 : fastPhase (bank 8 1).shape 179798 2369 1 1 0 41 1 = 6583670742012010339653 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_1_2369_1_join1

theorem receipt_8_1 : Checked (bank 8 1) 1 0 41 := by
  refine checked_from_values (bank 8 1) 1 0 41
    (P3_7_1.checked (bank 8 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_1_2368_0 rec_8_1_2368_1 rec_8_1_2369_0 rec_8_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2368 2 1 0 41 0) 0 128 = 7067414095411636956258 := by decide +kernel
private theorem rec_8_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2368 2 1 0 41 0) 128 128 = 0 := by decide +kernel
private theorem rec_8_2_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2368 2 1 0 41 0) 256 22 = 0 := by decide +kernel
private theorem rec_8_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2368 2 1 0 41 0) 128 150 = 0 :=
  phaseBlock_append rec_8_2_2368_0_part1 rec_8_2_2368_0_part2 rfl rfl rfl
private theorem rec_8_2_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2368 2 1 0 41 0) 0 278 = 7067414095411636956258 :=
  phaseBlock_append rec_8_2_2368_0_part0 rec_8_2_2368_0_join0 rfl rfl rfl

private theorem rec_8_2_2368_0 : fastPhase (bank 8 2).shape 179798 2368 2 1 0 41 0 = 7067414095411636956258 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_2_2368_0_join1

private theorem rec_8_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2368 2 1 0 41 1) 0 128 = 6847991326021211427123 := by decide +kernel
private theorem rec_8_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2368 2 1 0 41 1) 128 128 = 0 := by decide +kernel
private theorem rec_8_2_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2368 2 1 0 41 1) 256 22 = 0 := by decide +kernel
private theorem rec_8_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2368 2 1 0 41 1) 128 150 = 0 :=
  phaseBlock_append rec_8_2_2368_1_part1 rec_8_2_2368_1_part2 rfl rfl rfl
private theorem rec_8_2_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2368 2 1 0 41 1) 0 278 = 6847991326021211427123 :=
  phaseBlock_append rec_8_2_2368_1_part0 rec_8_2_2368_1_join0 rfl rfl rfl

private theorem rec_8_2_2368_1 : fastPhase (bank 8 2).shape 179798 2368 2 1 0 41 1 = 6847991326021211427123 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_2_2368_1_join1

private theorem rec_8_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2369 2 1 0 41 0) 0 128 = 7067477605619310608358 := by decide +kernel
private theorem rec_8_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2369 2 1 0 41 0) 128 128 = 0 := by decide +kernel
private theorem rec_8_2_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2369 2 1 0 41 0) 256 22 = 0 := by decide +kernel
private theorem rec_8_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2369 2 1 0 41 0) 128 150 = 0 :=
  phaseBlock_append rec_8_2_2369_0_part1 rec_8_2_2369_0_part2 rfl rfl rfl
private theorem rec_8_2_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2369 2 1 0 41 0) 0 278 = 7067477605619310608358 :=
  phaseBlock_append rec_8_2_2369_0_part0 rec_8_2_2369_0_join0 rfl rfl rfl

private theorem rec_8_2_2369_0 : fastPhase (bank 8 2).shape 179798 2369 2 1 0 41 0 = 7067477605619310608358 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_2_2369_0_join1

private theorem rec_8_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2369 2 1 0 41 1) 0 128 = 6848052948539890543701 := by decide +kernel
private theorem rec_8_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2369 2 1 0 41 1) 128 128 = 0 := by decide +kernel
private theorem rec_8_2_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2369 2 1 0 41 1) 256 22 = 0 := by decide +kernel
private theorem rec_8_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2369 2 1 0 41 1) 128 150 = 0 :=
  phaseBlock_append rec_8_2_2369_1_part1 rec_8_2_2369_1_part2 rfl rfl rfl
private theorem rec_8_2_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 2).shape 179798 2369 2 1 0 41 1) 0 278 = 6848052948539890543701 :=
  phaseBlock_append rec_8_2_2369_1_part0 rec_8_2_2369_1_join0 rfl rfl rfl

private theorem rec_8_2_2369_1 : fastPhase (bank 8 2).shape 179798 2369 2 1 0 41 1 = 6848052948539890543701 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_2_2369_1_join1

theorem receipt_8_2 : Checked (bank 8 2) 2 0 41 := by
  refine checked_from_values (bank 8 2) 2 0 41
    (P3_7_1.checked (bank 8 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_2_2368_0 rec_8_2_2368_1 rec_8_2_2369_0 rec_8_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2368 3 1 0 41 0) 0 128 = 7353768638868894839135 := by decide +kernel
private theorem rec_8_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2368 3 1 0 41 0) 128 128 = 0 := by decide +kernel
private theorem rec_8_3_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2368 3 1 0 41 0) 256 22 = 0 := by decide +kernel
private theorem rec_8_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2368 3 1 0 41 0) 128 150 = 0 :=
  phaseBlock_append rec_8_3_2368_0_part1 rec_8_3_2368_0_part2 rfl rfl rfl
private theorem rec_8_3_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2368 3 1 0 41 0) 0 278 = 7353768638868894839135 :=
  phaseBlock_append rec_8_3_2368_0_part0 rec_8_3_2368_0_join0 rfl rfl rfl

private theorem rec_8_3_2368_0 : fastPhase (bank 8 3).shape 179798 2368 3 1 0 41 0 = 7353768638868894839135 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_3_2368_0_join1

private theorem rec_8_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2368 3 1 0 41 1) 0 128 = 7128165370848195990687 := by decide +kernel
private theorem rec_8_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2368 3 1 0 41 1) 128 128 = 0 := by decide +kernel
private theorem rec_8_3_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2368 3 1 0 41 1) 256 22 = 0 := by decide +kernel
private theorem rec_8_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2368 3 1 0 41 1) 128 150 = 0 :=
  phaseBlock_append rec_8_3_2368_1_part1 rec_8_3_2368_1_part2 rfl rfl rfl
private theorem rec_8_3_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2368 3 1 0 41 1) 0 278 = 7128165370848195990687 :=
  phaseBlock_append rec_8_3_2368_1_part0 rec_8_3_2368_1_join0 rfl rfl rfl

private theorem rec_8_3_2368_1 : fastPhase (bank 8 3).shape 179798 2368 3 1 0 41 1 = 7128165370848195990687 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_3_2368_1_join1

private theorem rec_8_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2369 3 1 0 41 0) 0 128 = 7353834476356420928106 := by decide +kernel
private theorem rec_8_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2369 3 1 0 41 0) 128 128 = 0 := by decide +kernel
private theorem rec_8_3_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2369 3 1 0 41 0) 256 22 = 0 := by decide +kernel
private theorem rec_8_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2369 3 1 0 41 0) 128 150 = 0 :=
  phaseBlock_append rec_8_3_2369_0_part1 rec_8_3_2369_0_part2 rfl rfl rfl
private theorem rec_8_3_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2369 3 1 0 41 0) 0 278 = 7353834476356420928106 :=
  phaseBlock_append rec_8_3_2369_0_part0 rec_8_3_2369_0_join0 rfl rfl rfl

private theorem rec_8_3_2369_0 : fastPhase (bank 8 3).shape 179798 2369 3 1 0 41 0 = 7353834476356420928106 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_3_2369_0_join1

private theorem rec_8_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2369 3 1 0 41 1) 0 128 = 7128229275975912213942 := by decide +kernel
private theorem rec_8_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2369 3 1 0 41 1) 128 128 = 0 := by decide +kernel
private theorem rec_8_3_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2369 3 1 0 41 1) 256 22 = 0 := by decide +kernel
private theorem rec_8_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2369 3 1 0 41 1) 128 150 = 0 :=
  phaseBlock_append rec_8_3_2369_1_part1 rec_8_3_2369_1_part2 rfl rfl rfl
private theorem rec_8_3_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 3).shape 179798 2369 3 1 0 41 1) 0 278 = 7128229275975912213942 :=
  phaseBlock_append rec_8_3_2369_1_part0 rec_8_3_2369_1_join0 rfl rfl rfl

private theorem rec_8_3_2369_1 : fastPhase (bank 8 3).shape 179798 2369 3 1 0 41 1 = 7128229275975912213942 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_3_2369_1_join1

theorem receipt_8_3 : Checked (bank 8 3) 3 0 41 := by
  refine checked_from_values (bank 8 3) 3 0 41
    (P3_7_1.checked (bank 8 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_3_2368_0 rec_8_3_2368_1 rec_8_3_2369_0 rec_8_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2368 4 1 0 41 0) 0 128 = 7661775353842788861893 := by decide +kernel
private theorem rec_8_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2368 4 1 0 41 0) 128 128 = 0 := by decide +kernel
private theorem rec_8_4_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2368 4 1 0 41 0) 256 22 = 0 := by decide +kernel
private theorem rec_8_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2368 4 1 0 41 0) 128 150 = 0 :=
  phaseBlock_append rec_8_4_2368_0_part1 rec_8_4_2368_0_part2 rfl rfl rfl
private theorem rec_8_4_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2368 4 1 0 41 0) 0 278 = 7661775353842788861893 :=
  phaseBlock_append rec_8_4_2368_0_part0 rec_8_4_2368_0_join0 rfl rfl rfl

private theorem rec_8_4_2368_0 : fastPhase (bank 8 4).shape 179798 2368 4 1 0 41 0 = 7661775353842788861893 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_4_2368_0_join1

private theorem rec_8_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2368 4 1 0 41 1) 0 128 = 7429600225377195414560 := by decide +kernel
private theorem rec_8_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2368 4 1 0 41 1) 128 128 = 0 := by decide +kernel
private theorem rec_8_4_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2368 4 1 0 41 1) 256 22 = 0 := by decide +kernel
private theorem rec_8_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2368 4 1 0 41 1) 128 150 = 0 :=
  phaseBlock_append rec_8_4_2368_1_part1 rec_8_4_2368_1_part2 rfl rfl rfl
private theorem rec_8_4_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2368 4 1 0 41 1) 0 278 = 7429600225377195414560 :=
  phaseBlock_append rec_8_4_2368_1_part0 rec_8_4_2368_1_join0 rfl rfl rfl

private theorem rec_8_4_2368_1 : fastPhase (bank 8 4).shape 179798 2368 4 1 0 41 1 = 7429600225377195414560 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_4_2368_1_join1

private theorem rec_8_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2369 4 1 0 41 0) 0 128 = 7661843690295001285770 := by decide +kernel
private theorem rec_8_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2369 4 1 0 41 0) 128 128 = 0 := by decide +kernel
private theorem rec_8_4_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2369 4 1 0 41 0) 256 22 = 0 := by decide +kernel
private theorem rec_8_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2369 4 1 0 41 0) 128 150 = 0 :=
  phaseBlock_append rec_8_4_2369_0_part1 rec_8_4_2369_0_part2 rfl rfl rfl
private theorem rec_8_4_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2369 4 1 0 41 0) 0 278 = 7661843690295001285770 :=
  phaseBlock_append rec_8_4_2369_0_part0 rec_8_4_2369_0_join0 rfl rfl rfl

private theorem rec_8_4_2369_0 : fastPhase (bank 8 4).shape 179798 2369 4 1 0 41 0 = 7661843690295001285770 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_4_2369_0_join1

private theorem rec_8_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2369 4 1 0 41 1) 0 128 = 7429666582039047890511 := by decide +kernel
private theorem rec_8_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2369 4 1 0 41 1) 128 128 = 0 := by decide +kernel
private theorem rec_8_4_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2369 4 1 0 41 1) 256 22 = 0 := by decide +kernel
private theorem rec_8_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2369 4 1 0 41 1) 128 150 = 0 :=
  phaseBlock_append rec_8_4_2369_1_part1 rec_8_4_2369_1_part2 rfl rfl rfl
private theorem rec_8_4_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 4).shape 179798 2369 4 1 0 41 1) 0 278 = 7429666582039047890511 :=
  phaseBlock_append rec_8_4_2369_1_part0 rec_8_4_2369_1_join0 rfl rfl rfl

private theorem rec_8_4_2369_1 : fastPhase (bank 8 4).shape 179798 2369 4 1 0 41 1 = 7429666582039047890511 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_8_4_2369_1_join1

theorem receipt_8_4 : Checked (bank 8 4) 4 0 41 := by
  refine checked_from_values (bank 8 4) 4 0 41
    (P3_7_1.checked (bank 8 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_4_2368_0 rec_8_4_2368_1 rec_8_4_2369_0 rec_8_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2368 5 1 0 41 0) 0 128 = 38456328475524188209792 := by decide +kernel
private theorem rec_8_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2368 5 1 0 41 0) 128 128 = 28975290362971872680 := by decide +kernel
private theorem rec_8_5_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2368 5 1 0 41 0) 256 114 = 0 := by decide +kernel
private theorem rec_8_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2368 5 1 0 41 0) 128 242 = 28975290362971872680 :=
  phaseBlock_append rec_8_5_2368_0_part1 rec_8_5_2368_0_part2 rfl rfl rfl
private theorem rec_8_5_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2368 5 1 0 41 0) 0 370 = 38485303765887160082472 :=
  phaseBlock_append rec_8_5_2368_0_part0 rec_8_5_2368_0_join0 rfl rfl rfl

private theorem rec_8_5_2368_0 : fastPhase (bank 8 5).shape 179798 2368 5 1 0 41 0 = 38485303765887160082472 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_5_2368_0_join1

private theorem rec_8_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2368 5 1 0 41 1) 0 128 = 37555156703413921909056 := by decide +kernel
private theorem rec_8_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2368 5 1 0 41 1) 128 128 = 23442791819303430112 := by decide +kernel
private theorem rec_8_5_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2368 5 1 0 41 1) 256 114 = 0 := by decide +kernel
private theorem rec_8_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2368 5 1 0 41 1) 128 242 = 23442791819303430112 :=
  phaseBlock_append rec_8_5_2368_1_part1 rec_8_5_2368_1_part2 rfl rfl rfl
private theorem rec_8_5_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2368 5 1 0 41 1) 0 370 = 37578599495233225339168 :=
  phaseBlock_append rec_8_5_2368_1_part0 rec_8_5_2368_1_join0 rfl rfl rfl

private theorem rec_8_5_2368_1 : fastPhase (bank 8 5).shape 179798 2368 5 1 0 41 1 = 37578599495233225339168 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_5_2368_1_join1

private theorem rec_8_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2369 5 1 0 41 0) 0 128 = 38456672718716985227040 := by decide +kernel
private theorem rec_8_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2369 5 1 0 41 0) 128 128 = 28975506646690102668 := by decide +kernel
private theorem rec_8_5_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2369 5 1 0 41 0) 256 114 = 0 := by decide +kernel
private theorem rec_8_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2369 5 1 0 41 0) 128 242 = 28975506646690102668 :=
  phaseBlock_append rec_8_5_2369_0_part1 rec_8_5_2369_0_part2 rfl rfl rfl
private theorem rec_8_5_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2369 5 1 0 41 0) 0 370 = 38485648225363675329708 :=
  phaseBlock_append rec_8_5_2369_0_part0 rec_8_5_2369_0_join0 rfl rfl rfl

private theorem rec_8_5_2369_0 : fastPhase (bank 8 5).shape 179798 2369 5 1 0 41 0 = 38485648225363675329708 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_5_2369_0_join1

private theorem rec_8_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2369 5 1 0 41 1) 0 128 = 37555493218419252385824 := by decide +kernel
private theorem rec_8_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2369 5 1 0 41 1) 128 128 = 23442967028361160252 := by decide +kernel
private theorem rec_8_5_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2369 5 1 0 41 1) 256 114 = 0 := by decide +kernel
private theorem rec_8_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2369 5 1 0 41 1) 128 242 = 23442967028361160252 :=
  phaseBlock_append rec_8_5_2369_1_part1 rec_8_5_2369_1_part2 rfl rfl rfl
private theorem rec_8_5_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 5).shape 179798 2369 5 1 0 41 1) 0 370 = 37578936185447613546076 :=
  phaseBlock_append rec_8_5_2369_1_part0 rec_8_5_2369_1_join0 rfl rfl rfl

private theorem rec_8_5_2369_1 : fastPhase (bank 8 5).shape 179798 2369 5 1 0 41 1 = 37578936185447613546076 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_5_2369_1_join1

theorem receipt_8_5 : Checked (bank 8 5) 5 0 41 := by
  refine checked_from_values (bank 8 5) 5 0 41
    (P3_7_1.checked (bank 8 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_5_2368_0 rec_8_5_2368_1 rec_8_5_2369_0 rec_8_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2368 7 1 0 41 0) 0 128 = 40775083618260955423200 := by decide +kernel
private theorem rec_8_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2368 7 1 0 41 0) 128 128 = 49816291989939588555 := by decide +kernel
private theorem rec_8_6_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2368 7 1 0 41 0) 256 114 = 0 := by decide +kernel
private theorem rec_8_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2368 7 1 0 41 0) 128 242 = 49816291989939588555 :=
  phaseBlock_append rec_8_6_2368_0_part1 rec_8_6_2368_0_part2 rfl rfl rfl
private theorem rec_8_6_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2368 7 1 0 41 0) 0 370 = 40824899910250895011755 :=
  phaseBlock_append rec_8_6_2368_0_part0 rec_8_6_2368_0_join0 rfl rfl rfl

private theorem rec_8_6_2368_0 : fastPhase (bank 8 6).shape 179798 2368 7 1 0 41 0 = 40824899910250895011755 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_6_2368_0_join1

private theorem rec_8_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2368 7 1 0 41 1) 0 128 = 39838274956605414516960 := by decide +kernel
private theorem rec_8_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2368 7 1 0 41 1) 128 128 = 41767443454790981724 := by decide +kernel
private theorem rec_8_6_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2368 7 1 0 41 1) 256 114 = 0 := by decide +kernel
private theorem rec_8_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2368 7 1 0 41 1) 128 242 = 41767443454790981724 :=
  phaseBlock_append rec_8_6_2368_1_part1 rec_8_6_2368_1_part2 rfl rfl rfl
private theorem rec_8_6_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2368 7 1 0 41 1) 0 370 = 39880042400060205498684 :=
  phaseBlock_append rec_8_6_2368_1_part0 rec_8_6_2368_1_join0 rfl rfl rfl

private theorem rec_8_6_2368_1 : fastPhase (bank 8 6).shape 179798 2368 7 1 0 41 1 = 39880042400060205498684 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_6_2368_1_join1

private theorem rec_8_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2369 7 1 0 41 0) 0 128 = 40775446604087809825440 := by decide +kernel
private theorem rec_8_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2369 7 1 0 41 0) 128 128 = 49816661137272422703 := by decide +kernel
private theorem rec_8_6_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2369 7 1 0 41 0) 256 114 = 0 := by decide +kernel
private theorem rec_8_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2369 7 1 0 41 0) 128 242 = 49816661137272422703 :=
  phaseBlock_append rec_8_6_2369_0_part1 rec_8_6_2369_0_part2 rfl rfl rfl
private theorem rec_8_6_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2369 7 1 0 41 0) 0 370 = 40825263265225082248143 :=
  phaseBlock_append rec_8_6_2369_0_part0 rec_8_6_2369_0_join0 rfl rfl rfl

private theorem rec_8_6_2369_0 : fastPhase (bank 8 6).shape 179798 2369 7 1 0 41 0 = 40825263265225082248143 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_6_2369_0_join1

private theorem rec_8_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2369 7 1 0 41 1) 0 128 = 39838629958707558775392 := by decide +kernel
private theorem rec_8_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2369 7 1 0 41 1) 128 128 = 41767753353781150548 := by decide +kernel
private theorem rec_8_6_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2369 7 1 0 41 1) 256 114 = 0 := by decide +kernel
private theorem rec_8_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2369 7 1 0 41 1) 128 242 = 41767753353781150548 :=
  phaseBlock_append rec_8_6_2369_1_part1 rec_8_6_2369_1_part2 rfl rfl rfl
private theorem rec_8_6_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 6).shape 179798 2369 7 1 0 41 1) 0 370 = 39880397712061339925940 :=
  phaseBlock_append rec_8_6_2369_1_part0 rec_8_6_2369_1_join0 rfl rfl rfl

private theorem rec_8_6_2369_1 : fastPhase (bank 8 6).shape 179798 2369 7 1 0 41 1 = 39880397712061339925940 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_6_2369_1_join1

theorem receipt_8_6 : Checked (bank 8 6) 7 0 41 := by
  refine checked_from_values (bank 8 6) 7 0 41
    (P3_7_1.checked (bank 8 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_6_2368_0 rec_8_6_2368_1 rec_8_6_2369_0 rec_8_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2368 10 1 0 41 0) 0 128 = 44709116732026132186752 := by decide +kernel
private theorem rec_8_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2368 10 1 0 41 0) 128 128 = 101389887098581230248 := by decide +kernel
private theorem rec_8_7_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2368 10 1 0 41 0) 256 114 = 0 := by decide +kernel
private theorem rec_8_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2368 10 1 0 41 0) 128 242 = 101389887098581230248 :=
  phaseBlock_append rec_8_7_2368_0_part1 rec_8_7_2368_0_part2 rfl rfl rfl
private theorem rec_8_7_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2368 10 1 0 41 0) 0 370 = 44810506619124713417000 :=
  phaseBlock_append rec_8_7_2368_0_part0 rec_8_7_2368_0_join0 rfl rfl rfl

private theorem rec_8_7_2368_0 : fastPhase (bank 8 7).shape 179798 2368 10 1 0 41 0 = 44810506619124713417000 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_7_2368_0_join1

private theorem rec_8_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2368 10 1 0 41 1) 0 128 = 43713796667201801921856 := by decide +kernel
private theorem rec_8_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2368 10 1 0 41 1) 128 128 = 88257075633241913024 := by decide +kernel
private theorem rec_8_7_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2368 10 1 0 41 1) 256 114 = 0 := by decide +kernel
private theorem rec_8_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2368 10 1 0 41 1) 128 242 = 88257075633241913024 :=
  phaseBlock_append rec_8_7_2368_1_part1 rec_8_7_2368_1_part2 rfl rfl rfl
private theorem rec_8_7_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2368 10 1 0 41 1) 0 370 = 43802053742835043834880 :=
  phaseBlock_append rec_8_7_2368_1_part0 rec_8_7_2368_1_join0 rfl rfl rfl

private theorem rec_8_7_2368_1 : fastPhase (bank 8 7).shape 179798 2368 10 1 0 41 1 = 43802053742835043834880 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_7_2368_1_join1

private theorem rec_8_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2369 10 1 0 41 0) 0 128 = 44709511400463600455520 := by decide +kernel
private theorem rec_8_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2369 10 1 0 41 0) 128 128 = 101390630022098438010 := by decide +kernel
private theorem rec_8_7_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2369 10 1 0 41 0) 256 114 = 0 := by decide +kernel
private theorem rec_8_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2369 10 1 0 41 0) 128 242 = 101390630022098438010 :=
  phaseBlock_append rec_8_7_2369_0_part1 rec_8_7_2369_0_part2 rfl rfl rfl
private theorem rec_8_7_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2369 10 1 0 41 0) 0 370 = 44810902030485698893530 :=
  phaseBlock_append rec_8_7_2369_0_part0 rec_8_7_2369_0_join0 rfl rfl rfl

private theorem rec_8_7_2369_0 : fastPhase (bank 8 7).shape 179798 2369 10 1 0 41 0 = 44810902030485698893530 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_7_2369_0_join1

private theorem rec_8_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2369 10 1 0 41 1) 0 128 = 43714182933713008783584 := by decide +kernel
private theorem rec_8_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2369 10 1 0 41 1) 128 128 = 88257723158830181286 := by decide +kernel
private theorem rec_8_7_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2369 10 1 0 41 1) 256 114 = 0 := by decide +kernel
private theorem rec_8_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2369 10 1 0 41 1) 128 242 = 88257723158830181286 :=
  phaseBlock_append rec_8_7_2369_1_part1 rec_8_7_2369_1_part2 rfl rfl rfl
private theorem rec_8_7_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 7).shape 179798 2369 10 1 0 41 1) 0 370 = 43802440656871838964870 :=
  phaseBlock_append rec_8_7_2369_1_part0 rec_8_7_2369_1_join0 rfl rfl rfl

private theorem rec_8_7_2369_1 : fastPhase (bank 8 7).shape 179798 2369 10 1 0 41 1 = 43802440656871838964870 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_7_2369_1_join1

theorem receipt_8_7 : Checked (bank 8 7) 10 0 41 := by
  refine checked_from_values (bank 8 7) 10 0 41
    (P3_7_1.checked (bank 8 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_7_2368_0 rec_8_7_2368_1 rec_8_7_2369_0 rec_8_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 0) 0 128 = 237720306647446467187424 := by decide +kernel
private theorem rec_8_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 0) 128 128 = 8387976234705576192486 := by decide +kernel
private theorem rec_8_8_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 0) 256 128 = 0 := by decide +kernel
private theorem rec_8_8_2368_0_part3 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 0) 384 109 = 0 := by decide +kernel
private theorem rec_8_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 0) 0 256 = 246108282882152043379910 :=
  phaseBlock_append rec_8_8_2368_0_part0 rec_8_8_2368_0_part1 rfl rfl rfl
private theorem rec_8_8_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 0) 256 237 = 0 :=
  phaseBlock_append rec_8_8_2368_0_part2 rec_8_8_2368_0_part3 rfl rfl rfl
private theorem rec_8_8_2368_0_join2 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 0) 0 493 = 246108282882152043379910 :=
  phaseBlock_append rec_8_8_2368_0_join0 rec_8_8_2368_0_join1 rfl rfl rfl

private theorem rec_8_8_2368_0 : fastPhase (bank 8 8).shape 179798 2368 16 1 0 41 0 = 246108282882152043379910 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_8_8_2368_0_join2

private theorem rec_8_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 1) 0 128 = 233898207289276861070304 := by decide +kernel
private theorem rec_8_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 1) 128 128 = 8020286604486931612845 := by decide +kernel
private theorem rec_8_8_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 1) 256 128 = 0 := by decide +kernel
private theorem rec_8_8_2368_1_part3 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 1) 384 109 = 0 := by decide +kernel
private theorem rec_8_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 1) 0 256 = 241918493893763792683149 :=
  phaseBlock_append rec_8_8_2368_1_part0 rec_8_8_2368_1_part1 rfl rfl rfl
private theorem rec_8_8_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 1) 256 237 = 0 :=
  phaseBlock_append rec_8_8_2368_1_part2 rec_8_8_2368_1_part3 rfl rfl rfl
private theorem rec_8_8_2368_1_join2 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2368 16 1 0 41 1) 0 493 = 241918493893763792683149 :=
  phaseBlock_append rec_8_8_2368_1_join0 rec_8_8_2368_1_join1 rfl rfl rfl

private theorem rec_8_8_2368_1 : fastPhase (bank 8 8).shape 179798 2368 16 1 0 41 1 = 241918493893763792683149 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_8_8_2368_1_join2

private theorem rec_8_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 0) 0 128 = 237722403675585671249472 := by decide +kernel
private theorem rec_8_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 0) 128 128 = 8388040542360023341908 := by decide +kernel
private theorem rec_8_8_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 0) 256 128 = 0 := by decide +kernel
private theorem rec_8_8_2369_0_part3 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 0) 384 109 = 0 := by decide +kernel
private theorem rec_8_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 0) 0 256 = 246110444217945694591380 :=
  phaseBlock_append rec_8_8_2369_0_part0 rec_8_8_2369_0_part1 rfl rfl rfl
private theorem rec_8_8_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 0) 256 237 = 0 :=
  phaseBlock_append rec_8_8_2369_0_part2 rec_8_8_2369_0_part3 rfl rfl rfl
private theorem rec_8_8_2369_0_join2 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 0) 0 493 = 246110444217945694591380 :=
  phaseBlock_append rec_8_8_2369_0_join0 rec_8_8_2369_0_join1 rfl rfl rfl

private theorem rec_8_8_2369_0 : fastPhase (bank 8 8).shape 179798 2369 16 1 0 41 0 = 246110444217945694591380 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_8_8_2369_0_join2

private theorem rec_8_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 1) 0 128 = 233900271945945399822720 := by decide +kernel
private theorem rec_8_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 1) 128 128 = 8020348149205944177780 := by decide +kernel
private theorem rec_8_8_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 1) 256 128 = 0 := by decide +kernel
private theorem rec_8_8_2369_1_part3 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 1) 384 109 = 0 := by decide +kernel
private theorem rec_8_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 1) 0 256 = 241920620095151344000500 :=
  phaseBlock_append rec_8_8_2369_1_part0 rec_8_8_2369_1_part1 rfl rfl rfl
private theorem rec_8_8_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 1) 256 237 = 0 :=
  phaseBlock_append rec_8_8_2369_1_part2 rec_8_8_2369_1_part3 rfl rfl rfl
private theorem rec_8_8_2369_1_join2 :
    phaseBlock (fastLayerG (bank 8 8).shape 179798 2369 16 1 0 41 1) 0 493 = 241920620095151344000500 :=
  phaseBlock_append rec_8_8_2369_1_join0 rec_8_8_2369_1_join1 rfl rfl rfl

private theorem rec_8_8_2369_1 : fastPhase (bank 8 8).shape 179798 2369 16 1 0 41 1 = 241920620095151344000500 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_8_8_2369_1_join2

theorem receipt_8_8 : Checked (bank 8 8) 16 0 41 := by
  refine checked_from_values (bank 8 8) 16 0 41
    (P3_7_1.checked (bank 8 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_8_2368_0 rec_8_8_2368_1 rec_8_8_2369_0 rec_8_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2368 10 1 0 41 0) 0 128 = 44709116732026132186752 := by decide +kernel
private theorem rec_8_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2368 10 1 0 41 0) 128 128 = 101389887098581230248 := by decide +kernel
private theorem rec_8_9_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2368 10 1 0 41 0) 256 114 = 0 := by decide +kernel
private theorem rec_8_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2368 10 1 0 41 0) 128 242 = 101389887098581230248 :=
  phaseBlock_append rec_8_9_2368_0_part1 rec_8_9_2368_0_part2 rfl rfl rfl
private theorem rec_8_9_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2368 10 1 0 41 0) 0 370 = 44810506619124713417000 :=
  phaseBlock_append rec_8_9_2368_0_part0 rec_8_9_2368_0_join0 rfl rfl rfl

private theorem rec_8_9_2368_0 : fastPhase (bank 8 9).shape 179798 2368 10 1 0 41 0 = 44810506619124713417000 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_9_2368_0_join1

private theorem rec_8_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2368 10 1 0 41 1) 0 128 = 43713796667201801921856 := by decide +kernel
private theorem rec_8_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2368 10 1 0 41 1) 128 128 = 88257075633241913024 := by decide +kernel
private theorem rec_8_9_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2368 10 1 0 41 1) 256 114 = 0 := by decide +kernel
private theorem rec_8_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2368 10 1 0 41 1) 128 242 = 88257075633241913024 :=
  phaseBlock_append rec_8_9_2368_1_part1 rec_8_9_2368_1_part2 rfl rfl rfl
private theorem rec_8_9_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2368 10 1 0 41 1) 0 370 = 43802053742835043834880 :=
  phaseBlock_append rec_8_9_2368_1_part0 rec_8_9_2368_1_join0 rfl rfl rfl

private theorem rec_8_9_2368_1 : fastPhase (bank 8 9).shape 179798 2368 10 1 0 41 1 = 43802053742835043834880 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_9_2368_1_join1

private theorem rec_8_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2369 10 1 0 41 0) 0 128 = 44709511400463600455520 := by decide +kernel
private theorem rec_8_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2369 10 1 0 41 0) 128 128 = 101390630022098438010 := by decide +kernel
private theorem rec_8_9_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2369 10 1 0 41 0) 256 114 = 0 := by decide +kernel
private theorem rec_8_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2369 10 1 0 41 0) 128 242 = 101390630022098438010 :=
  phaseBlock_append rec_8_9_2369_0_part1 rec_8_9_2369_0_part2 rfl rfl rfl
private theorem rec_8_9_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2369 10 1 0 41 0) 0 370 = 44810902030485698893530 :=
  phaseBlock_append rec_8_9_2369_0_part0 rec_8_9_2369_0_join0 rfl rfl rfl

private theorem rec_8_9_2369_0 : fastPhase (bank 8 9).shape 179798 2369 10 1 0 41 0 = 44810902030485698893530 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_9_2369_0_join1

private theorem rec_8_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2369 10 1 0 41 1) 0 128 = 43714182933713008783584 := by decide +kernel
private theorem rec_8_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2369 10 1 0 41 1) 128 128 = 88257723158830181286 := by decide +kernel
private theorem rec_8_9_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2369 10 1 0 41 1) 256 114 = 0 := by decide +kernel
private theorem rec_8_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2369 10 1 0 41 1) 128 242 = 88257723158830181286 :=
  phaseBlock_append rec_8_9_2369_1_part1 rec_8_9_2369_1_part2 rfl rfl rfl
private theorem rec_8_9_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 9).shape 179798 2369 10 1 0 41 1) 0 370 = 43802440656871838964870 :=
  phaseBlock_append rec_8_9_2369_1_part0 rec_8_9_2369_1_join0 rfl rfl rfl

private theorem rec_8_9_2369_1 : fastPhase (bank 8 9).shape 179798 2369 10 1 0 41 1 = 43802440656871838964870 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_8_9_2369_1_join1

theorem receipt_8_9 : Checked (bank 8 9) 10 0 41 := by
  refine checked_from_values (bank 8 9) 10 0 41
    (P3_7_1.checked (bank 8 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_9_2368_0 rec_8_9_2368_1 rec_8_9_2369_0 rec_8_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 0 128 = 1336680762959132214082656 := by decide +kernel
private theorem rec_8_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 128 128 = 168125782879270490647648 := by decide +kernel
private theorem rec_8_10_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 256 128 = 36295542919050449010 := by decide +kernel
private theorem rec_8_10_2368_0_part3 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 384 128 = 0 := by decide +kernel
private theorem rec_8_10_2368_0_part4 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 512 128 = 0 := by decide +kernel
private theorem rec_8_10_2368_0_part5 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 640 38 = 0 := by decide +kernel
private theorem rec_8_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 128 256 = 168162078422189541096658 :=
  phaseBlock_append rec_8_10_2368_0_part1 rec_8_10_2368_0_part2 rfl rfl rfl
private theorem rec_8_10_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 0 384 = 1504842841381321755179314 :=
  phaseBlock_append rec_8_10_2368_0_part0 rec_8_10_2368_0_join0 rfl rfl rfl
private theorem rec_8_10_2368_0_join2 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 512 166 = 0 :=
  phaseBlock_append rec_8_10_2368_0_part4 rec_8_10_2368_0_part5 rfl rfl rfl
private theorem rec_8_10_2368_0_join3 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 384 294 = 0 :=
  phaseBlock_append rec_8_10_2368_0_part3 rec_8_10_2368_0_join2 rfl rfl rfl
private theorem rec_8_10_2368_0_join4 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 0) 0 678 = 1504842841381321755179314 :=
  phaseBlock_append rec_8_10_2368_0_join1 rec_8_10_2368_0_join3 rfl rfl rfl

private theorem rec_8_10_2368_0 : fastPhase (bank 8 10).shape 179798 2368 20 1 0 41 0 = 1504842841381321755179314 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_8_10_2368_0_join4

private theorem rec_8_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 0 128 = 1321392191370049125955040 := by decide +kernel
private theorem rec_8_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 128 128 = 164192173381033871975904 := by decide +kernel
private theorem rec_8_10_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 256 128 = 25338636641293607382 := by decide +kernel
private theorem rec_8_10_2368_1_part3 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 384 128 = 0 := by decide +kernel
private theorem rec_8_10_2368_1_part4 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 512 128 = 0 := by decide +kernel
private theorem rec_8_10_2368_1_part5 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 640 38 = 0 := by decide +kernel
private theorem rec_8_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 128 256 = 164217512017675165583286 :=
  phaseBlock_append rec_8_10_2368_1_part1 rec_8_10_2368_1_part2 rfl rfl rfl
private theorem rec_8_10_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 0 384 = 1485609703387724291538326 :=
  phaseBlock_append rec_8_10_2368_1_part0 rec_8_10_2368_1_join0 rfl rfl rfl
private theorem rec_8_10_2368_1_join2 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 512 166 = 0 :=
  phaseBlock_append rec_8_10_2368_1_part4 rec_8_10_2368_1_part5 rfl rfl rfl
private theorem rec_8_10_2368_1_join3 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 384 294 = 0 :=
  phaseBlock_append rec_8_10_2368_1_part3 rec_8_10_2368_1_join2 rfl rfl rfl
private theorem rec_8_10_2368_1_join4 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2368 20 1 0 41 1) 0 678 = 1485609703387724291538326 :=
  phaseBlock_append rec_8_10_2368_1_join1 rec_8_10_2368_1_join3 rfl rfl rfl

private theorem rec_8_10_2368_1 : fastPhase (bank 8 10).shape 179798 2368 20 1 0 41 1 = 1485609703387724291538326 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_8_10_2368_1_join4

private theorem rec_8_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 0 128 = 1336692692936013345981120 := by decide +kernel
private theorem rec_8_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 128 128 = 168127131292692997300928 := by decide +kernel
private theorem rec_8_10_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 256 128 = 36295803930179752296 := by decide +kernel
private theorem rec_8_10_2369_0_part3 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 384 128 = 0 := by decide +kernel
private theorem rec_8_10_2369_0_part4 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 512 128 = 0 := by decide +kernel
private theorem rec_8_10_2369_0_part5 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 640 38 = 0 := by decide +kernel
private theorem rec_8_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 128 256 = 168163427096623177053224 :=
  phaseBlock_append rec_8_10_2369_0_part1 rec_8_10_2369_0_part2 rfl rfl rfl
private theorem rec_8_10_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 0 384 = 1504856120032636523034344 :=
  phaseBlock_append rec_8_10_2369_0_part0 rec_8_10_2369_0_join0 rfl rfl rfl
private theorem rec_8_10_2369_0_join2 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 512 166 = 0 :=
  phaseBlock_append rec_8_10_2369_0_part4 rec_8_10_2369_0_part5 rfl rfl rfl
private theorem rec_8_10_2369_0_join3 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 384 294 = 0 :=
  phaseBlock_append rec_8_10_2369_0_part3 rec_8_10_2369_0_join2 rfl rfl rfl
private theorem rec_8_10_2369_0_join4 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 0) 0 678 = 1504856120032636523034344 :=
  phaseBlock_append rec_8_10_2369_0_join1 rec_8_10_2369_0_join3 rfl rfl rfl

private theorem rec_8_10_2369_0 : fastPhase (bank 8 10).shape 179798 2369 20 1 0 41 0 = 1504856120032636523034344 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_8_10_2369_0_join4

private theorem rec_8_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 0 128 = 1321403989874927605783360 := by decide +kernel
private theorem rec_8_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 128 128 = 164193491068622154021696 := by decide +kernel
private theorem rec_8_10_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 256 128 = 25338818989115877252 := by decide +kernel
private theorem rec_8_10_2369_1_part3 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 384 128 = 0 := by decide +kernel
private theorem rec_8_10_2369_1_part4 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 512 128 = 0 := by decide +kernel
private theorem rec_8_10_2369_1_part5 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 640 38 = 0 := by decide +kernel
private theorem rec_8_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 128 256 = 164218829887611269898948 :=
  phaseBlock_append rec_8_10_2369_1_part1 rec_8_10_2369_1_part2 rfl rfl rfl
private theorem rec_8_10_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 0 384 = 1485622819762538875682308 :=
  phaseBlock_append rec_8_10_2369_1_part0 rec_8_10_2369_1_join0 rfl rfl rfl
private theorem rec_8_10_2369_1_join2 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 512 166 = 0 :=
  phaseBlock_append rec_8_10_2369_1_part4 rec_8_10_2369_1_part5 rfl rfl rfl
private theorem rec_8_10_2369_1_join3 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 384 294 = 0 :=
  phaseBlock_append rec_8_10_2369_1_part3 rec_8_10_2369_1_join2 rfl rfl rfl
private theorem rec_8_10_2369_1_join4 :
    phaseBlock (fastLayerG (bank 8 10).shape 179798 2369 20 1 0 41 1) 0 678 = 1485622819762538875682308 :=
  phaseBlock_append rec_8_10_2369_1_join1 rec_8_10_2369_1_join3 rfl rfl rfl

private theorem rec_8_10_2369_1 : fastPhase (bank 8 10).shape 179798 2369 20 1 0 41 1 = 1485622819762538875682308 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_8_10_2369_1_join4

theorem receipt_8_10 : Checked (bank 8 10) 20 0 41 := by
  refine checked_from_values (bank 8 10) 20 0 41
    (P3_7_1.checked (bank 8 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_10_2368_0 rec_8_10_2368_1 rec_8_10_2369_0 rec_8_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 0 128 = 7495267173334746215525248 := by decide +kernel
private theorem rec_8_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 128 128 = 2090342587707593969257344 := by decide +kernel
private theorem rec_8_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 256 128 = 179338842646818275342592 := by decide +kernel
private theorem rec_8_11_2368_0_part3 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 384 128 = 0 := by decide +kernel
private theorem rec_8_11_2368_0_part4 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 512 128 = 0 := by decide +kernel
private theorem rec_8_11_2368_0_part5 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 640 128 = 0 := by decide +kernel
private theorem rec_8_11_2368_0_part6 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 768 128 = 0 := by decide +kernel
private theorem rec_8_11_2368_0_part7 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 896 29 = 0 := by decide +kernel
private theorem rec_8_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 0 256 = 9585609761042340184782592 :=
  phaseBlock_append rec_8_11_2368_0_part0 rec_8_11_2368_0_part1 rfl rfl rfl
private theorem rec_8_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 256 256 = 179338842646818275342592 :=
  phaseBlock_append rec_8_11_2368_0_part2 rec_8_11_2368_0_part3 rfl rfl rfl
private theorem rec_8_11_2368_0_join2 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 0 512 = 9764948603689158460125184 :=
  phaseBlock_append rec_8_11_2368_0_join0 rec_8_11_2368_0_join1 rfl rfl rfl
private theorem rec_8_11_2368_0_join3 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 512 256 = 0 :=
  phaseBlock_append rec_8_11_2368_0_part4 rec_8_11_2368_0_part5 rfl rfl rfl
private theorem rec_8_11_2368_0_join4 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 768 157 = 0 :=
  phaseBlock_append rec_8_11_2368_0_part6 rec_8_11_2368_0_part7 rfl rfl rfl
private theorem rec_8_11_2368_0_join5 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 512 413 = 0 :=
  phaseBlock_append rec_8_11_2368_0_join3 rec_8_11_2368_0_join4 rfl rfl rfl
private theorem rec_8_11_2368_0_join6 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 0) 0 925 = 9764948603689158460125184 :=
  phaseBlock_append rec_8_11_2368_0_join2 rec_8_11_2368_0_join5 rfl rfl rfl

private theorem rec_8_11_2368_0 : fastPhase (bank 8 11).shape 179798 2368 32 1 0 41 0 = 9764948603689158460125184 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_8_11_2368_0_join6

private theorem rec_8_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 0 128 = 7435564992683614455006528 := by decide +kernel
private theorem rec_8_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 128 128 = 2063915304556229489427776 := by decide +kernel
private theorem rec_8_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 256 128 = 174090769307618562587188 := by decide +kernel
private theorem rec_8_11_2368_1_part3 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 384 128 = 0 := by decide +kernel
private theorem rec_8_11_2368_1_part4 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 512 128 = 0 := by decide +kernel
private theorem rec_8_11_2368_1_part5 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 640 128 = 0 := by decide +kernel
private theorem rec_8_11_2368_1_part6 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 768 128 = 0 := by decide +kernel
private theorem rec_8_11_2368_1_part7 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 896 29 = 0 := by decide +kernel
private theorem rec_8_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 0 256 = 9499480297239843944434304 :=
  phaseBlock_append rec_8_11_2368_1_part0 rec_8_11_2368_1_part1 rfl rfl rfl
private theorem rec_8_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 256 256 = 174090769307618562587188 :=
  phaseBlock_append rec_8_11_2368_1_part2 rec_8_11_2368_1_part3 rfl rfl rfl
private theorem rec_8_11_2368_1_join2 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 0 512 = 9673571066547462507021492 :=
  phaseBlock_append rec_8_11_2368_1_join0 rec_8_11_2368_1_join1 rfl rfl rfl
private theorem rec_8_11_2368_1_join3 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 512 256 = 0 :=
  phaseBlock_append rec_8_11_2368_1_part4 rec_8_11_2368_1_part5 rfl rfl rfl
private theorem rec_8_11_2368_1_join4 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 768 157 = 0 :=
  phaseBlock_append rec_8_11_2368_1_part6 rec_8_11_2368_1_part7 rfl rfl rfl
private theorem rec_8_11_2368_1_join5 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 512 413 = 0 :=
  phaseBlock_append rec_8_11_2368_1_join3 rec_8_11_2368_1_join4 rfl rfl rfl
private theorem rec_8_11_2368_1_join6 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2368 32 1 0 41 1) 0 925 = 9673571066547462507021492 :=
  phaseBlock_append rec_8_11_2368_1_join2 rec_8_11_2368_1_join5 rfl rfl rfl

private theorem rec_8_11_2368_1 : fastPhase (bank 8 11).shape 179798 2368 32 1 0 41 1 = 9673571066547462507021492 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_8_11_2368_1_join6

private theorem rec_8_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 0 128 = 7495334357991138721336288 := by decide +kernel
private theorem rec_8_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 128 128 = 2090359832235231768566752 := by decide +kernel
private theorem rec_8_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 256 128 = 179340204871269868718948 := by decide +kernel
private theorem rec_8_11_2369_0_part3 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 384 128 = 0 := by decide +kernel
private theorem rec_8_11_2369_0_part4 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 512 128 = 0 := by decide +kernel
private theorem rec_8_11_2369_0_part5 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 640 128 = 0 := by decide +kernel
private theorem rec_8_11_2369_0_part6 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 768 128 = 0 := by decide +kernel
private theorem rec_8_11_2369_0_part7 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 896 29 = 0 := by decide +kernel
private theorem rec_8_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 0 256 = 9585694190226370489903040 :=
  phaseBlock_append rec_8_11_2369_0_part0 rec_8_11_2369_0_part1 rfl rfl rfl
private theorem rec_8_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 256 256 = 179340204871269868718948 :=
  phaseBlock_append rec_8_11_2369_0_part2 rec_8_11_2369_0_part3 rfl rfl rfl
private theorem rec_8_11_2369_0_join2 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 0 512 = 9765034395097640358621988 :=
  phaseBlock_append rec_8_11_2369_0_join0 rec_8_11_2369_0_join1 rfl rfl rfl
private theorem rec_8_11_2369_0_join3 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 512 256 = 0 :=
  phaseBlock_append rec_8_11_2369_0_part4 rec_8_11_2369_0_part5 rfl rfl rfl
private theorem rec_8_11_2369_0_join4 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 768 157 = 0 :=
  phaseBlock_append rec_8_11_2369_0_part6 rec_8_11_2369_0_part7 rfl rfl rfl
private theorem rec_8_11_2369_0_join5 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 512 413 = 0 :=
  phaseBlock_append rec_8_11_2369_0_join3 rec_8_11_2369_0_join4 rfl rfl rfl
private theorem rec_8_11_2369_0_join6 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 0) 0 925 = 9765034395097640358621988 :=
  phaseBlock_append rec_8_11_2369_0_join2 rec_8_11_2369_0_join5 rfl rfl rfl

private theorem rec_8_11_2369_0 : fastPhase (bank 8 11).shape 179798 2369 32 1 0 41 0 = 9765034395097640358621988 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_8_11_2369_0_join6

private theorem rec_8_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 0 128 = 7435631661406997975984928 := by decide +kernel
private theorem rec_8_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 128 128 = 2063932336890196805647136 := by decide +kernel
private theorem rec_8_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 256 128 = 174092092320009951821188 := by decide +kernel
private theorem rec_8_11_2369_1_part3 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 384 128 = 0 := by decide +kernel
private theorem rec_8_11_2369_1_part4 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 512 128 = 0 := by decide +kernel
private theorem rec_8_11_2369_1_part5 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 640 128 = 0 := by decide +kernel
private theorem rec_8_11_2369_1_part6 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 768 128 = 0 := by decide +kernel
private theorem rec_8_11_2369_1_part7 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 896 29 = 0 := by decide +kernel
private theorem rec_8_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 0 256 = 9499563998297194781632064 :=
  phaseBlock_append rec_8_11_2369_1_part0 rec_8_11_2369_1_part1 rfl rfl rfl
private theorem rec_8_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 256 256 = 174092092320009951821188 :=
  phaseBlock_append rec_8_11_2369_1_part2 rec_8_11_2369_1_part3 rfl rfl rfl
private theorem rec_8_11_2369_1_join2 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 0 512 = 9673656090617204733453252 :=
  phaseBlock_append rec_8_11_2369_1_join0 rec_8_11_2369_1_join1 rfl rfl rfl
private theorem rec_8_11_2369_1_join3 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 512 256 = 0 :=
  phaseBlock_append rec_8_11_2369_1_part4 rec_8_11_2369_1_part5 rfl rfl rfl
private theorem rec_8_11_2369_1_join4 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 768 157 = 0 :=
  phaseBlock_append rec_8_11_2369_1_part6 rec_8_11_2369_1_part7 rfl rfl rfl
private theorem rec_8_11_2369_1_join5 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 512 413 = 0 :=
  phaseBlock_append rec_8_11_2369_1_join3 rec_8_11_2369_1_join4 rfl rfl rfl
private theorem rec_8_11_2369_1_join6 :
    phaseBlock (fastLayerG (bank 8 11).shape 179798 2369 32 1 0 41 1) 0 925 = 9673656090617204733453252 :=
  phaseBlock_append rec_8_11_2369_1_join2 rec_8_11_2369_1_join5 rfl rfl rfl

private theorem rec_8_11_2369_1 : fastPhase (bank 8 11).shape 179798 2369 32 1 0 41 1 = 9673656090617204733453252 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_8_11_2369_1_join6

theorem receipt_8_11 : Checked (bank 8 11) 32 0 41 := by
  refine checked_from_values (bank 8 11) 32 0 41
    (P3_7_1.checked (bank 8 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_11_2368_0 rec_8_11_2368_1 rec_8_11_2369_0 rec_8_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 0 128 = 7421268741153336562229856 := by decide +kernel
private theorem rec_8_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 128 128 = 2055530248071619264623200 := by decide +kernel
private theorem rec_8_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 256 128 = 171926598334026630393901 := by decide +kernel
private theorem rec_8_12_2368_0_part3 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 384 128 = 0 := by decide +kernel
private theorem rec_8_12_2368_0_part4 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 512 128 = 0 := by decide +kernel
private theorem rec_8_12_2368_0_part5 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 640 128 = 0 := by decide +kernel
private theorem rec_8_12_2368_0_part6 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 768 128 = 0 := by decide +kernel
private theorem rec_8_12_2368_0_part7 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 896 29 = 0 := by decide +kernel
private theorem rec_8_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 0 256 = 9476798989224955826853056 :=
  phaseBlock_append rec_8_12_2368_0_part0 rec_8_12_2368_0_part1 rfl rfl rfl
private theorem rec_8_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 256 256 = 171926598334026630393901 :=
  phaseBlock_append rec_8_12_2368_0_part2 rec_8_12_2368_0_part3 rfl rfl rfl
private theorem rec_8_12_2368_0_join2 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 0 512 = 9648725587558982457246957 :=
  phaseBlock_append rec_8_12_2368_0_join0 rec_8_12_2368_0_join1 rfl rfl rfl
private theorem rec_8_12_2368_0_join3 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 512 256 = 0 :=
  phaseBlock_append rec_8_12_2368_0_part4 rec_8_12_2368_0_part5 rfl rfl rfl
private theorem rec_8_12_2368_0_join4 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 768 157 = 0 :=
  phaseBlock_append rec_8_12_2368_0_part6 rec_8_12_2368_0_part7 rfl rfl rfl
private theorem rec_8_12_2368_0_join5 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 512 413 = 0 :=
  phaseBlock_append rec_8_12_2368_0_join3 rec_8_12_2368_0_join4 rfl rfl rfl
private theorem rec_8_12_2368_0_join6 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 0) 0 925 = 9648725587558982457246957 :=
  phaseBlock_append rec_8_12_2368_0_join2 rec_8_12_2368_0_join5 rfl rfl rfl

private theorem rec_8_12_2368_0 : fastPhase (bank 8 12).shape 179798 2368 31 1 0 41 0 = 9648725587558982457246957 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_8_12_2368_0_join6

private theorem rec_8_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 0 128 = 7361918755025399138475872 := by decide +kernel
private theorem rec_8_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 128 128 = 2029361651130282367700832 := by decide +kernel
private theorem rec_8_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 256 128 = 166827127745310770124790 := by decide +kernel
private theorem rec_8_12_2368_1_part3 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 384 128 = 0 := by decide +kernel
private theorem rec_8_12_2368_1_part4 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 512 128 = 0 := by decide +kernel
private theorem rec_8_12_2368_1_part5 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 640 128 = 0 := by decide +kernel
private theorem rec_8_12_2368_1_part6 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 768 128 = 0 := by decide +kernel
private theorem rec_8_12_2368_1_part7 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 896 29 = 0 := by decide +kernel
private theorem rec_8_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 0 256 = 9391280406155681506176704 :=
  phaseBlock_append rec_8_12_2368_1_part0 rec_8_12_2368_1_part1 rfl rfl rfl
private theorem rec_8_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 256 256 = 166827127745310770124790 :=
  phaseBlock_append rec_8_12_2368_1_part2 rec_8_12_2368_1_part3 rfl rfl rfl
private theorem rec_8_12_2368_1_join2 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 0 512 = 9558107533900992276301494 :=
  phaseBlock_append rec_8_12_2368_1_join0 rec_8_12_2368_1_join1 rfl rfl rfl
private theorem rec_8_12_2368_1_join3 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 512 256 = 0 :=
  phaseBlock_append rec_8_12_2368_1_part4 rec_8_12_2368_1_part5 rfl rfl rfl
private theorem rec_8_12_2368_1_join4 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 768 157 = 0 :=
  phaseBlock_append rec_8_12_2368_1_part6 rec_8_12_2368_1_part7 rfl rfl rfl
private theorem rec_8_12_2368_1_join5 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 512 413 = 0 :=
  phaseBlock_append rec_8_12_2368_1_join3 rec_8_12_2368_1_join4 rfl rfl rfl
private theorem rec_8_12_2368_1_join6 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2368 31 1 0 41 1) 0 925 = 9558107533900992276301494 :=
  phaseBlock_append rec_8_12_2368_1_join2 rec_8_12_2368_1_join5 rfl rfl rfl

private theorem rec_8_12_2368_1 : fastPhase (bank 8 12).shape 179798 2368 31 1 0 41 1 = 9558107533900992276301494 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_8_12_2368_1_join6

private theorem rec_8_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 0 128 = 7421335324871200944122016 := by decide +kernel
private theorem rec_8_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 128 128 = 2055547224013401468016800 := by decide +kernel
private theorem rec_8_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 256 128 = 171927906099936776530986 := by decide +kernel
private theorem rec_8_12_2369_0_part3 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 384 128 = 0 := by decide +kernel
private theorem rec_8_12_2369_0_part4 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 512 128 = 0 := by decide +kernel
private theorem rec_8_12_2369_0_part5 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 640 128 = 0 := by decide +kernel
private theorem rec_8_12_2369_0_part6 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 768 128 = 0 := by decide +kernel
private theorem rec_8_12_2369_0_part7 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 896 29 = 0 := by decide +kernel
private theorem rec_8_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 0 256 = 9476882548884602412138816 :=
  phaseBlock_append rec_8_12_2369_0_part0 rec_8_12_2369_0_part1 rfl rfl rfl
private theorem rec_8_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 256 256 = 171927906099936776530986 :=
  phaseBlock_append rec_8_12_2369_0_part2 rec_8_12_2369_0_part3 rfl rfl rfl
private theorem rec_8_12_2369_0_join2 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 0 512 = 9648810454984539188669802 :=
  phaseBlock_append rec_8_12_2369_0_join0 rec_8_12_2369_0_join1 rfl rfl rfl
private theorem rec_8_12_2369_0_join3 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 512 256 = 0 :=
  phaseBlock_append rec_8_12_2369_0_part4 rec_8_12_2369_0_part5 rfl rfl rfl
private theorem rec_8_12_2369_0_join4 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 768 157 = 0 :=
  phaseBlock_append rec_8_12_2369_0_part6 rec_8_12_2369_0_part7 rfl rfl rfl
private theorem rec_8_12_2369_0_join5 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 512 413 = 0 :=
  phaseBlock_append rec_8_12_2369_0_join3 rec_8_12_2369_0_join4 rfl rfl rfl
private theorem rec_8_12_2369_0_join6 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 0) 0 925 = 9648810454984539188669802 :=
  phaseBlock_append rec_8_12_2369_0_join2 rec_8_12_2369_0_join5 rfl rfl rfl

private theorem rec_8_12_2369_0 : fastPhase (bank 8 12).shape 179798 2369 31 1 0 41 0 = 9648810454984539188669802 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_8_12_2369_0_join6

private theorem rec_8_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 0 128 = 7361984825298065319594144 := by decide +kernel
private theorem rec_8_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 128 128 = 2029378416694962305153184 := by decide +kernel
private theorem rec_8_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 256 128 = 166828397346394993865370 := by decide +kernel
private theorem rec_8_12_2369_1_part3 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 384 128 = 0 := by decide +kernel
private theorem rec_8_12_2369_1_part4 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 512 128 = 0 := by decide +kernel
private theorem rec_8_12_2369_1_part5 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 640 128 = 0 := by decide +kernel
private theorem rec_8_12_2369_1_part6 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 768 128 = 0 := by decide +kernel
private theorem rec_8_12_2369_1_part7 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 896 29 = 0 := by decide +kernel
private theorem rec_8_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 0 256 = 9391363241993027624747328 :=
  phaseBlock_append rec_8_12_2369_1_part0 rec_8_12_2369_1_part1 rfl rfl rfl
private theorem rec_8_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 256 256 = 166828397346394993865370 :=
  phaseBlock_append rec_8_12_2369_1_part2 rec_8_12_2369_1_part3 rfl rfl rfl
private theorem rec_8_12_2369_1_join2 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 0 512 = 9558191639339422618612698 :=
  phaseBlock_append rec_8_12_2369_1_join0 rec_8_12_2369_1_join1 rfl rfl rfl
private theorem rec_8_12_2369_1_join3 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 512 256 = 0 :=
  phaseBlock_append rec_8_12_2369_1_part4 rec_8_12_2369_1_part5 rfl rfl rfl
private theorem rec_8_12_2369_1_join4 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 768 157 = 0 :=
  phaseBlock_append rec_8_12_2369_1_part6 rec_8_12_2369_1_part7 rfl rfl rfl
private theorem rec_8_12_2369_1_join5 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 512 413 = 0 :=
  phaseBlock_append rec_8_12_2369_1_join3 rec_8_12_2369_1_join4 rfl rfl rfl
private theorem rec_8_12_2369_1_join6 :
    phaseBlock (fastLayerG (bank 8 12).shape 179798 2369 31 1 0 41 1) 0 925 = 9558191639339422618612698 :=
  phaseBlock_append rec_8_12_2369_1_join2 rec_8_12_2369_1_join5 rfl rfl rfl

private theorem rec_8_12_2369_1 : fastPhase (bank 8 12).shape 179798 2369 31 1 0 41 1 = 9558191639339422618612698 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_8_12_2369_1_join6

theorem receipt_8_12 : Checked (bank 8 12) 31 0 41 := by
  refine checked_from_values (bank 8 12) 31 0 41
    (P3_7_1.checked (bank 8 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_12_2368_0 rec_8_12_2368_1 rec_8_12_2369_0 rec_8_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 0 128 = 44363997027617189192457600 := by decide +kernel
private theorem rec_8_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 128 128 = 19504143108365391504915840 := by decide +kernel
private theorem rec_8_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 256 128 = 5932546951977294711397760 := by decide +kernel
private theorem rec_8_13_2368_0_part3 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 384 128 = 621824591077146193172800 := by decide +kernel
private theorem rec_8_13_2368_0_part4 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 512 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_0_part5 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 640 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_0_part6 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 768 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_0_part7 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 896 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_0_part8 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 1024 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_0_part9 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 1152 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_0_part10 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 1280 14 = 0 := by decide +kernel
private theorem rec_8_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 0 256 = 63868140135982580697373440 :=
  phaseBlock_append rec_8_13_2368_0_part0 rec_8_13_2368_0_part1 rfl rfl rfl
private theorem rec_8_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 384 256 = 621824591077146193172800 :=
  phaseBlock_append rec_8_13_2368_0_part3 rec_8_13_2368_0_part4 rfl rfl rfl
private theorem rec_8_13_2368_0_join2 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 256 384 = 6554371543054440904570560 :=
  phaseBlock_append rec_8_13_2368_0_part2 rec_8_13_2368_0_join1 rfl rfl rfl
private theorem rec_8_13_2368_0_join3 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 0 640 = 70422511679037021601944000 :=
  phaseBlock_append rec_8_13_2368_0_join0 rec_8_13_2368_0_join2 rfl rfl rfl
private theorem rec_8_13_2368_0_join4 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 768 256 = 0 :=
  phaseBlock_append rec_8_13_2368_0_part6 rec_8_13_2368_0_part7 rfl rfl rfl
private theorem rec_8_13_2368_0_join5 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 640 384 = 0 :=
  phaseBlock_append rec_8_13_2368_0_part5 rec_8_13_2368_0_join4 rfl rfl rfl
private theorem rec_8_13_2368_0_join6 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 1152 142 = 0 :=
  phaseBlock_append rec_8_13_2368_0_part9 rec_8_13_2368_0_part10 rfl rfl rfl
private theorem rec_8_13_2368_0_join7 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 1024 270 = 0 :=
  phaseBlock_append rec_8_13_2368_0_part8 rec_8_13_2368_0_join6 rfl rfl rfl
private theorem rec_8_13_2368_0_join8 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 640 654 = 0 :=
  phaseBlock_append rec_8_13_2368_0_join5 rec_8_13_2368_0_join7 rfl rfl rfl
private theorem rec_8_13_2368_0_join9 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 0) 0 1294 = 70422511679037021601944000 :=
  phaseBlock_append rec_8_13_2368_0_join3 rec_8_13_2368_0_join8 rfl rfl rfl

private theorem rec_8_13_2368_0 : fastPhase (bank 8 13).shape 179798 2368 44 1 0 41 0 = 70422511679037021601944000 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_8_13_2368_0_join9

private theorem rec_8_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 0 128 = 44118321306902087937602176 := by decide +kernel
private theorem rec_8_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 128 128 = 19358761631075310374605440 := by decide +kernel
private theorem rec_8_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 256 128 = 5862888248187878121599616 := by decide +kernel
private theorem rec_8_13_2368_1_part3 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 384 128 = 605276412119840761130688 := by decide +kernel
private theorem rec_8_13_2368_1_part4 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 512 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_1_part5 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 640 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_1_part6 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 768 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_1_part7 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 896 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_1_part8 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 1024 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_1_part9 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 1152 128 = 0 := by decide +kernel
private theorem rec_8_13_2368_1_part10 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 1280 14 = 0 := by decide +kernel
private theorem rec_8_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 0 256 = 63477082937977398312207616 :=
  phaseBlock_append rec_8_13_2368_1_part0 rec_8_13_2368_1_part1 rfl rfl rfl
private theorem rec_8_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 384 256 = 605276412119840761130688 :=
  phaseBlock_append rec_8_13_2368_1_part3 rec_8_13_2368_1_part4 rfl rfl rfl
private theorem rec_8_13_2368_1_join2 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 256 384 = 6468164660307718882730304 :=
  phaseBlock_append rec_8_13_2368_1_part2 rec_8_13_2368_1_join1 rfl rfl rfl
private theorem rec_8_13_2368_1_join3 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 0 640 = 69945247598285117194937920 :=
  phaseBlock_append rec_8_13_2368_1_join0 rec_8_13_2368_1_join2 rfl rfl rfl
private theorem rec_8_13_2368_1_join4 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 768 256 = 0 :=
  phaseBlock_append rec_8_13_2368_1_part6 rec_8_13_2368_1_part7 rfl rfl rfl
private theorem rec_8_13_2368_1_join5 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 640 384 = 0 :=
  phaseBlock_append rec_8_13_2368_1_part5 rec_8_13_2368_1_join4 rfl rfl rfl
private theorem rec_8_13_2368_1_join6 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 1152 142 = 0 :=
  phaseBlock_append rec_8_13_2368_1_part9 rec_8_13_2368_1_part10 rfl rfl rfl
private theorem rec_8_13_2368_1_join7 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 1024 270 = 0 :=
  phaseBlock_append rec_8_13_2368_1_part8 rec_8_13_2368_1_join6 rfl rfl rfl
private theorem rec_8_13_2368_1_join8 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 640 654 = 0 :=
  phaseBlock_append rec_8_13_2368_1_join5 rec_8_13_2368_1_join7 rfl rfl rfl
private theorem rec_8_13_2368_1_join9 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2368 44 1 0 41 1) 0 1294 = 69945247598285117194937920 :=
  phaseBlock_append rec_8_13_2368_1_join3 rec_8_13_2368_1_join8 rfl rfl rfl

private theorem rec_8_13_2368_1 : fastPhase (bank 8 13).shape 179798 2368 44 1 0 41 1 = 69945247598285117194937920 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_8_13_2368_1_join9

private theorem rec_8_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 0 128 = 44364398077533552700033920 := by decide +kernel
private theorem rec_8_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 128 128 = 19504309279245021569747840 := by decide +kernel
private theorem rec_8_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 256 128 = 5932594392800435960286080 := by decide +kernel
private theorem rec_8_13_2369_0_part3 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 384 128 = 621829266708278419645660 := by decide +kernel
private theorem rec_8_13_2369_0_part4 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 512 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_0_part5 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 640 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_0_part6 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 768 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_0_part7 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 896 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_0_part8 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 1024 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_0_part9 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 1152 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_0_part10 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 1280 14 = 0 := by decide +kernel
private theorem rec_8_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 0 256 = 63868707356778574269781760 :=
  phaseBlock_append rec_8_13_2369_0_part0 rec_8_13_2369_0_part1 rfl rfl rfl
private theorem rec_8_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 384 256 = 621829266708278419645660 :=
  phaseBlock_append rec_8_13_2369_0_part3 rec_8_13_2369_0_part4 rfl rfl rfl
private theorem rec_8_13_2369_0_join2 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 256 384 = 6554423659508714379931740 :=
  phaseBlock_append rec_8_13_2369_0_part2 rec_8_13_2369_0_join1 rfl rfl rfl
private theorem rec_8_13_2369_0_join3 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 0 640 = 70423131016287288649713500 :=
  phaseBlock_append rec_8_13_2369_0_join0 rec_8_13_2369_0_join2 rfl rfl rfl
private theorem rec_8_13_2369_0_join4 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 768 256 = 0 :=
  phaseBlock_append rec_8_13_2369_0_part6 rec_8_13_2369_0_part7 rfl rfl rfl
private theorem rec_8_13_2369_0_join5 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 640 384 = 0 :=
  phaseBlock_append rec_8_13_2369_0_part5 rec_8_13_2369_0_join4 rfl rfl rfl
private theorem rec_8_13_2369_0_join6 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 1152 142 = 0 :=
  phaseBlock_append rec_8_13_2369_0_part9 rec_8_13_2369_0_part10 rfl rfl rfl
private theorem rec_8_13_2369_0_join7 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 1024 270 = 0 :=
  phaseBlock_append rec_8_13_2369_0_part8 rec_8_13_2369_0_join6 rfl rfl rfl
private theorem rec_8_13_2369_0_join8 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 640 654 = 0 :=
  phaseBlock_append rec_8_13_2369_0_join5 rec_8_13_2369_0_join7 rfl rfl rfl
private theorem rec_8_13_2369_0_join9 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 0) 0 1294 = 70423131016287288649713500 :=
  phaseBlock_append rec_8_13_2369_0_join3 rec_8_13_2369_0_join8 rfl rfl rfl

private theorem rec_8_13_2369_0 : fastPhase (bank 8 13).shape 179798 2369 44 1 0 41 0 = 70423131016287288649713500 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_8_13_2369_0_join9

private theorem rec_8_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 0 128 = 44118720214730877383042368 := by decide +kernel
private theorem rec_8_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 128 128 = 19358926598310353418880320 := by decide +kernel
private theorem rec_8_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 256 128 = 5862935143511558505080128 := by decide +kernel
private theorem rec_8_13_2369_1_part3 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 384 128 = 605280964944839657811974 := by decide +kernel
private theorem rec_8_13_2369_1_part4 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 512 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_1_part5 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 640 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_1_part6 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 768 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_1_part7 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 896 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_1_part8 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 1024 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_1_part9 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 1152 128 = 0 := by decide +kernel
private theorem rec_8_13_2369_1_part10 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 1280 14 = 0 := by decide +kernel
private theorem rec_8_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 0 256 = 63477646813041230801922688 :=
  phaseBlock_append rec_8_13_2369_1_part0 rec_8_13_2369_1_part1 rfl rfl rfl
private theorem rec_8_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 384 256 = 605280964944839657811974 :=
  phaseBlock_append rec_8_13_2369_1_part3 rec_8_13_2369_1_part4 rfl rfl rfl
private theorem rec_8_13_2369_1_join2 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 256 384 = 6468216108456398162892102 :=
  phaseBlock_append rec_8_13_2369_1_part2 rec_8_13_2369_1_join1 rfl rfl rfl
private theorem rec_8_13_2369_1_join3 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 0 640 = 69945862921497628964814790 :=
  phaseBlock_append rec_8_13_2369_1_join0 rec_8_13_2369_1_join2 rfl rfl rfl
private theorem rec_8_13_2369_1_join4 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 768 256 = 0 :=
  phaseBlock_append rec_8_13_2369_1_part6 rec_8_13_2369_1_part7 rfl rfl rfl
private theorem rec_8_13_2369_1_join5 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 640 384 = 0 :=
  phaseBlock_append rec_8_13_2369_1_part5 rec_8_13_2369_1_join4 rfl rfl rfl
private theorem rec_8_13_2369_1_join6 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 1152 142 = 0 :=
  phaseBlock_append rec_8_13_2369_1_part9 rec_8_13_2369_1_part10 rfl rfl rfl
private theorem rec_8_13_2369_1_join7 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 1024 270 = 0 :=
  phaseBlock_append rec_8_13_2369_1_part8 rec_8_13_2369_1_join6 rfl rfl rfl
private theorem rec_8_13_2369_1_join8 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 640 654 = 0 :=
  phaseBlock_append rec_8_13_2369_1_join5 rec_8_13_2369_1_join7 rfl rfl rfl
private theorem rec_8_13_2369_1_join9 :
    phaseBlock (fastLayerG (bank 8 13).shape 179798 2369 44 1 0 41 1) 0 1294 = 69945862921497628964814790 :=
  phaseBlock_append rec_8_13_2369_1_join3 rec_8_13_2369_1_join8 rfl rfl rfl

private theorem rec_8_13_2369_1 : fastPhase (bank 8 13).shape 179798 2369 44 1 0 41 1 = 69945862921497628964814790 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_8_13_2369_1_join9

theorem receipt_8_13 : Checked (bank 8 13) 44 0 41 := by
  refine checked_from_values (bank 8 13) 44 0 41
    (P3_7_1.checked (bank 8 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_13_2368_0 rec_8_13_2368_1 rec_8_13_2369_0 rec_8_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 0 128 = 256927058023700462049335904 := by decide +kernel
private theorem rec_8_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 128 128 = 150034440462426360017341024 := by decide +kernel
private theorem rec_8_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 256 128 = 76840335299339500452444768 := by decide +kernel
private theorem rec_8_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 384 128 = 31257103317756683585825376 := by decide +kernel
private theorem rec_8_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 512 128 = 7581864413878015570041440 := by decide +kernel
private theorem rec_8_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 640 128 = 291918017693268352592161 := by decide +kernel
private theorem rec_8_14_2368_0_part6 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 768 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_0_part7 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 896 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_0_part8 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 1024 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_0_part9 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 1152 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_0_part10 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 1280 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_0_part11 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 1408 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_0_part12 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 1536 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_0_part13 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 1664 123 = 0 := by decide +kernel
private theorem rec_8_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 128 256 = 226874775761765860469785792 :=
  phaseBlock_append rec_8_14_2368_0_part1 rec_8_14_2368_0_part2 rfl rfl rfl
private theorem rec_8_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 0 384 = 483801833785466322519121696 :=
  phaseBlock_append rec_8_14_2368_0_part0 rec_8_14_2368_0_join0 rfl rfl rfl
private theorem rec_8_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 384 256 = 38838967731634699155866816 :=
  phaseBlock_append rec_8_14_2368_0_part3 rec_8_14_2368_0_part4 rfl rfl rfl
private theorem rec_8_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 640 256 = 291918017693268352592161 :=
  phaseBlock_append rec_8_14_2368_0_part5 rec_8_14_2368_0_part6 rfl rfl rfl
private theorem rec_8_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 384 512 = 39130885749327967508458977 :=
  phaseBlock_append rec_8_14_2368_0_join2 rec_8_14_2368_0_join3 rfl rfl rfl
private theorem rec_8_14_2368_0_join5 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 0 896 = 522932719534794290027580673 :=
  phaseBlock_append rec_8_14_2368_0_join1 rec_8_14_2368_0_join4 rfl rfl rfl
private theorem rec_8_14_2368_0_join6 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 1024 256 = 0 :=
  phaseBlock_append rec_8_14_2368_0_part8 rec_8_14_2368_0_part9 rfl rfl rfl
private theorem rec_8_14_2368_0_join7 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 896 384 = 0 :=
  phaseBlock_append rec_8_14_2368_0_part7 rec_8_14_2368_0_join6 rfl rfl rfl
private theorem rec_8_14_2368_0_join8 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 1280 256 = 0 :=
  phaseBlock_append rec_8_14_2368_0_part10 rec_8_14_2368_0_part11 rfl rfl rfl
private theorem rec_8_14_2368_0_join9 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 1536 251 = 0 :=
  phaseBlock_append rec_8_14_2368_0_part12 rec_8_14_2368_0_part13 rfl rfl rfl
private theorem rec_8_14_2368_0_join10 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 1280 507 = 0 :=
  phaseBlock_append rec_8_14_2368_0_join8 rec_8_14_2368_0_join9 rfl rfl rfl
private theorem rec_8_14_2368_0_join11 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 896 891 = 0 :=
  phaseBlock_append rec_8_14_2368_0_join7 rec_8_14_2368_0_join10 rfl rfl rfl
private theorem rec_8_14_2368_0_join12 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 0) 0 1787 = 522932719534794290027580673 :=
  phaseBlock_append rec_8_14_2368_0_join5 rec_8_14_2368_0_join11 rfl rfl rfl

private theorem rec_8_14_2368_0 : fastPhase (bank 8 14).shape 179798 2368 76 1 0 41 0 = 522932719534794290027580673 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_8_14_2368_0_join12

private theorem rec_8_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 0 128 = 255947529684366727617742432 := by decide +kernel
private theorem rec_8_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 128 128 = 149341719231551614439265888 := by decide +kernel
private theorem rec_8_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 256 128 = 76385669182690745206679136 := by decide +kernel
private theorem rec_8_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 384 128 = 30994734229397409927607904 := by decide +kernel
private theorem rec_8_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 512 128 = 7468947275030551867344480 := by decide +kernel
private theorem rec_8_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 640 128 = 278870846087353256452705 := by decide +kernel
private theorem rec_8_14_2368_1_part6 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 768 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_1_part7 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 896 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_1_part8 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 1024 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_1_part9 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 1152 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_1_part10 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 1280 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_1_part11 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 1408 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_1_part12 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 1536 128 = 0 := by decide +kernel
private theorem rec_8_14_2368_1_part13 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 1664 123 = 0 := by decide +kernel
private theorem rec_8_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 128 256 = 225727388414242359645945024 :=
  phaseBlock_append rec_8_14_2368_1_part1 rec_8_14_2368_1_part2 rfl rfl rfl
private theorem rec_8_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 0 384 = 481674918098609087263687456 :=
  phaseBlock_append rec_8_14_2368_1_part0 rec_8_14_2368_1_join0 rfl rfl rfl
private theorem rec_8_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 384 256 = 38463681504427961794952384 :=
  phaseBlock_append rec_8_14_2368_1_part3 rec_8_14_2368_1_part4 rfl rfl rfl
private theorem rec_8_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 640 256 = 278870846087353256452705 :=
  phaseBlock_append rec_8_14_2368_1_part5 rec_8_14_2368_1_part6 rfl rfl rfl
private theorem rec_8_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 384 512 = 38742552350515315051405089 :=
  phaseBlock_append rec_8_14_2368_1_join2 rec_8_14_2368_1_join3 rfl rfl rfl
private theorem rec_8_14_2368_1_join5 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 0 896 = 520417470449124402315092545 :=
  phaseBlock_append rec_8_14_2368_1_join1 rec_8_14_2368_1_join4 rfl rfl rfl
private theorem rec_8_14_2368_1_join6 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 1024 256 = 0 :=
  phaseBlock_append rec_8_14_2368_1_part8 rec_8_14_2368_1_part9 rfl rfl rfl
private theorem rec_8_14_2368_1_join7 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 896 384 = 0 :=
  phaseBlock_append rec_8_14_2368_1_part7 rec_8_14_2368_1_join6 rfl rfl rfl
private theorem rec_8_14_2368_1_join8 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 1280 256 = 0 :=
  phaseBlock_append rec_8_14_2368_1_part10 rec_8_14_2368_1_part11 rfl rfl rfl
private theorem rec_8_14_2368_1_join9 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 1536 251 = 0 :=
  phaseBlock_append rec_8_14_2368_1_part12 rec_8_14_2368_1_part13 rfl rfl rfl
private theorem rec_8_14_2368_1_join10 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 1280 507 = 0 :=
  phaseBlock_append rec_8_14_2368_1_join8 rec_8_14_2368_1_join9 rfl rfl rfl
private theorem rec_8_14_2368_1_join11 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 896 891 = 0 :=
  phaseBlock_append rec_8_14_2368_1_join7 rec_8_14_2368_1_join10 rfl rfl rfl
private theorem rec_8_14_2368_1_join12 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2368 76 1 0 41 1) 0 1787 = 520417470449124402315092545 :=
  phaseBlock_append rec_8_14_2368_1_join5 rec_8_14_2368_1_join11 rfl rfl rfl

private theorem rec_8_14_2368_1 : fastPhase (bank 8 14).shape 179798 2368 76 1 0 41 1 = 520417470449124402315092545 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_8_14_2368_1_join12

private theorem rec_8_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 0 128 = 256929378457881262121085120 := by decide +kernel
private theorem rec_8_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 128 128 = 150035738626897343779473600 := by decide +kernel
private theorem rec_8_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 256 128 = 76840970502177736369907904 := by decide +kernel
private theorem rec_8_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 384 128 = 31257349516703064369383616 := by decide +kernel
private theorem rec_8_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 512 128 = 7581921241661277879625920 := by decide +kernel
private theorem rec_8_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 640 128 = 291920109468390642374070 := by decide +kernel
private theorem rec_8_14_2369_0_part6 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 768 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_0_part7 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 896 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_0_part8 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 1024 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_0_part9 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 1152 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_0_part10 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 1280 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_0_part11 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 1408 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_0_part12 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 1536 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_0_part13 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 1664 123 = 0 := by decide +kernel
private theorem rec_8_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 128 256 = 226876709129075080149381504 :=
  phaseBlock_append rec_8_14_2369_0_part1 rec_8_14_2369_0_part2 rfl rfl rfl
private theorem rec_8_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 0 384 = 483806087586956342270466624 :=
  phaseBlock_append rec_8_14_2369_0_part0 rec_8_14_2369_0_join0 rfl rfl rfl
private theorem rec_8_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 384 256 = 38839270758364342249009536 :=
  phaseBlock_append rec_8_14_2369_0_part3 rec_8_14_2369_0_part4 rfl rfl rfl
private theorem rec_8_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 640 256 = 291920109468390642374070 :=
  phaseBlock_append rec_8_14_2369_0_part5 rec_8_14_2369_0_part6 rfl rfl rfl
private theorem rec_8_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 384 512 = 39131190867832732891383606 :=
  phaseBlock_append rec_8_14_2369_0_join2 rec_8_14_2369_0_join3 rfl rfl rfl
private theorem rec_8_14_2369_0_join5 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 0 896 = 522937278454789075161850230 :=
  phaseBlock_append rec_8_14_2369_0_join1 rec_8_14_2369_0_join4 rfl rfl rfl
private theorem rec_8_14_2369_0_join6 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 1024 256 = 0 :=
  phaseBlock_append rec_8_14_2369_0_part8 rec_8_14_2369_0_part9 rfl rfl rfl
private theorem rec_8_14_2369_0_join7 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 896 384 = 0 :=
  phaseBlock_append rec_8_14_2369_0_part7 rec_8_14_2369_0_join6 rfl rfl rfl
private theorem rec_8_14_2369_0_join8 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 1280 256 = 0 :=
  phaseBlock_append rec_8_14_2369_0_part10 rec_8_14_2369_0_part11 rfl rfl rfl
private theorem rec_8_14_2369_0_join9 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 1536 251 = 0 :=
  phaseBlock_append rec_8_14_2369_0_part12 rec_8_14_2369_0_part13 rfl rfl rfl
private theorem rec_8_14_2369_0_join10 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 1280 507 = 0 :=
  phaseBlock_append rec_8_14_2369_0_join8 rec_8_14_2369_0_join9 rfl rfl rfl
private theorem rec_8_14_2369_0_join11 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 896 891 = 0 :=
  phaseBlock_append rec_8_14_2369_0_join7 rec_8_14_2369_0_join10 rfl rfl rfl
private theorem rec_8_14_2369_0_join12 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 0) 0 1787 = 522937278454789075161850230 :=
  phaseBlock_append rec_8_14_2369_0_join5 rec_8_14_2369_0_join11 rfl rfl rfl

private theorem rec_8_14_2369_0 : fastPhase (bank 8 14).shape 179798 2369 76 1 0 41 0 = 522937278454789075161850230 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_8_14_2369_0_join12

private theorem rec_8_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 0 128 = 255949841596664172525054336 := by decide +kernel
private theorem rec_8_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 128 128 = 149343011590446288303679872 := by decide +kernel
private theorem rec_8_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 256 128 = 76386300723490056778082688 := by decide +kernel
private theorem rec_8_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 384 128 = 30994978402271093403150720 := by decide +kernel
private theorem rec_8_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 512 128 = 7469003268139855227316608 := by decide +kernel
private theorem rec_8_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 640 128 = 278872844915726387433954 := by decide +kernel
private theorem rec_8_14_2369_1_part6 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 768 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_1_part7 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 896 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_1_part8 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 1024 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_1_part9 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 1152 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_1_part10 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 1280 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_1_part11 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 1408 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_1_part12 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 1536 128 = 0 := by decide +kernel
private theorem rec_8_14_2369_1_part13 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 1664 123 = 0 := by decide +kernel
private theorem rec_8_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 128 256 = 225729312313936345081762560 :=
  phaseBlock_append rec_8_14_2369_1_part1 rec_8_14_2369_1_part2 rfl rfl rfl
private theorem rec_8_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 0 384 = 481679153910600517606816896 :=
  phaseBlock_append rec_8_14_2369_1_part0 rec_8_14_2369_1_join0 rfl rfl rfl
private theorem rec_8_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 384 256 = 38463981670410948630467328 :=
  phaseBlock_append rec_8_14_2369_1_part3 rec_8_14_2369_1_part4 rfl rfl rfl
private theorem rec_8_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 640 256 = 278872844915726387433954 :=
  phaseBlock_append rec_8_14_2369_1_part5 rec_8_14_2369_1_part6 rfl rfl rfl
private theorem rec_8_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 384 512 = 38742854515326675017901282 :=
  phaseBlock_append rec_8_14_2369_1_join2 rec_8_14_2369_1_join3 rfl rfl rfl
private theorem rec_8_14_2369_1_join5 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 0 896 = 520422008425927192624718178 :=
  phaseBlock_append rec_8_14_2369_1_join1 rec_8_14_2369_1_join4 rfl rfl rfl
private theorem rec_8_14_2369_1_join6 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 1024 256 = 0 :=
  phaseBlock_append rec_8_14_2369_1_part8 rec_8_14_2369_1_part9 rfl rfl rfl
private theorem rec_8_14_2369_1_join7 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 896 384 = 0 :=
  phaseBlock_append rec_8_14_2369_1_part7 rec_8_14_2369_1_join6 rfl rfl rfl
private theorem rec_8_14_2369_1_join8 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 1280 256 = 0 :=
  phaseBlock_append rec_8_14_2369_1_part10 rec_8_14_2369_1_part11 rfl rfl rfl
private theorem rec_8_14_2369_1_join9 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 1536 251 = 0 :=
  phaseBlock_append rec_8_14_2369_1_part12 rec_8_14_2369_1_part13 rfl rfl rfl
private theorem rec_8_14_2369_1_join10 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 1280 507 = 0 :=
  phaseBlock_append rec_8_14_2369_1_join8 rec_8_14_2369_1_join9 rfl rfl rfl
private theorem rec_8_14_2369_1_join11 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 896 891 = 0 :=
  phaseBlock_append rec_8_14_2369_1_join7 rec_8_14_2369_1_join10 rfl rfl rfl
private theorem rec_8_14_2369_1_join12 :
    phaseBlock (fastLayerG (bank 8 14).shape 179798 2369 76 1 0 41 1) 0 1787 = 520422008425927192624718178 :=
  phaseBlock_append rec_8_14_2369_1_join5 rec_8_14_2369_1_join11 rfl rfl rfl

private theorem rec_8_14_2369_1 : fastPhase (bank 8 14).shape 179798 2369 76 1 0 41 1 = 520422008425927192624718178 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_8_14_2369_1_join12

theorem receipt_8_14 : Checked (bank 8 14) 76 0 41 := by
  refine checked_from_values (bank 8 14) 76 0 41
    (P3_7_1.checked (bank 8 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_14_2368_0 rec_8_14_2368_1 rec_8_14_2369_0 rec_8_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 0 128 = 1195469733181489011484375840 := by decide +kernel
private theorem rec_8_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 128 128 = 815806139771523095900220192 := by decide +kernel
private theorem rec_8_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 256 128 = 523909183555760356633287456 := by decide +kernel
private theorem rec_8_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 384 128 = 308410046475531821447498528 := by decide +kernel
private theorem rec_8_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 512 128 = 158466381321042567307492128 := by decide +kernel
private theorem rec_8_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 640 128 = 63751746302962661751204640 := by decide +kernel
private theorem rec_8_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 768 128 = 14445039624018104262449952 := by decide +kernel
private theorem rec_8_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 896 128 = 356692408364443145837634 := by decide +kernel
private theorem rec_8_15_2368_0_part8 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1024 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_part9 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1152 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_part10 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1280 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_part11 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1408 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_part12 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1536 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_part13 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1664 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_part14 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1792 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_part15 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1920 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_part16 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 2048 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_part17 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 2176 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_part18 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 2304 99 = 0 := by decide +kernel
private theorem rec_8_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 0 256 = 2011275872953012107384596032 :=
  phaseBlock_append rec_8_15_2368_0_part0 rec_8_15_2368_0_part1 rfl rfl rfl
private theorem rec_8_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 256 256 = 832319230031292178080785984 :=
  phaseBlock_append rec_8_15_2368_0_part2 rec_8_15_2368_0_part3 rfl rfl rfl
private theorem rec_8_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 0 512 = 2843595102984304285465382016 :=
  phaseBlock_append rec_8_15_2368_0_join0 rec_8_15_2368_0_join1 rfl rfl rfl
private theorem rec_8_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 512 256 = 222218127624005229058696768 :=
  phaseBlock_append rec_8_15_2368_0_part4 rec_8_15_2368_0_part5 rfl rfl rfl
private theorem rec_8_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 896 256 = 356692408364443145837634 :=
  phaseBlock_append rec_8_15_2368_0_part7 rec_8_15_2368_0_part8 rfl rfl rfl
private theorem rec_8_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 768 384 = 14801732032382547408287586 :=
  phaseBlock_append rec_8_15_2368_0_part6 rec_8_15_2368_0_join4 rfl rfl rfl
private theorem rec_8_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 512 640 = 237019859656387776466984354 :=
  phaseBlock_append rec_8_15_2368_0_join3 rec_8_15_2368_0_join5 rfl rfl rfl
private theorem rec_8_15_2368_0_join7 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 0 1152 = 3080614962640692061932366370 :=
  phaseBlock_append rec_8_15_2368_0_join2 rec_8_15_2368_0_join6 rfl rfl rfl
private theorem rec_8_15_2368_0_join8 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1152 256 = 0 :=
  phaseBlock_append rec_8_15_2368_0_part9 rec_8_15_2368_0_part10 rfl rfl rfl
private theorem rec_8_15_2368_0_join9 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1536 256 = 0 :=
  phaseBlock_append rec_8_15_2368_0_part12 rec_8_15_2368_0_part13 rfl rfl rfl
private theorem rec_8_15_2368_0_join10 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1408 384 = 0 :=
  phaseBlock_append rec_8_15_2368_0_part11 rec_8_15_2368_0_join9 rfl rfl rfl
private theorem rec_8_15_2368_0_join11 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1152 640 = 0 :=
  phaseBlock_append rec_8_15_2368_0_join8 rec_8_15_2368_0_join10 rfl rfl rfl
private theorem rec_8_15_2368_0_join12 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1792 256 = 0 :=
  phaseBlock_append rec_8_15_2368_0_part14 rec_8_15_2368_0_part15 rfl rfl rfl
private theorem rec_8_15_2368_0_join13 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 2176 227 = 0 :=
  phaseBlock_append rec_8_15_2368_0_part17 rec_8_15_2368_0_part18 rfl rfl rfl
private theorem rec_8_15_2368_0_join14 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 2048 355 = 0 :=
  phaseBlock_append rec_8_15_2368_0_part16 rec_8_15_2368_0_join13 rfl rfl rfl
private theorem rec_8_15_2368_0_join15 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1792 611 = 0 :=
  phaseBlock_append rec_8_15_2368_0_join12 rec_8_15_2368_0_join14 rfl rfl rfl
private theorem rec_8_15_2368_0_join16 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 1152 1251 = 0 :=
  phaseBlock_append rec_8_15_2368_0_join11 rec_8_15_2368_0_join15 rfl rfl rfl
private theorem rec_8_15_2368_0_join17 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 0) 0 2403 = 3080614962640692061932366370 :=
  phaseBlock_append rec_8_15_2368_0_join7 rec_8_15_2368_0_join16 rfl rfl rfl

private theorem rec_8_15_2368_0 : fastPhase (bank 8 15).shape 179798 2368 105 1 0 41 0 = 3080614962640692061932366370 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_8_15_2368_0_join17

private theorem rec_8_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 0 128 = 1192142161525530601240020768 := by decide +kernel
private theorem rec_8_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 128 128 = 813206871395002278703863584 := by decide +kernel
private theorem rec_8_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 256 128 = 521947958805296711902422816 := by decide +kernel
private theorem rec_8_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 384 128 = 307000687337702881920202528 := by decide +kernel
private theorem rec_8_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 512 128 = 157526710521246166378710816 := by decide +kernel
private theorem rec_8_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 640 128 = 63203506404279280809039648 := by decide +kernel
private theorem rec_8_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 768 128 = 14213812126073220024444704 := by decide +kernel
private theorem rec_8_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 896 128 = 336982344277125750698781 := by decide +kernel
private theorem rec_8_15_2368_1_part8 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1024 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_part9 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1152 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_part10 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1280 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_part11 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1408 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_part12 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1536 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_part13 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1664 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_part14 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1792 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_part15 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1920 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_part16 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 2048 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_part17 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 2176 128 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_part18 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 2304 99 = 0 := by decide +kernel
private theorem rec_8_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 0 256 = 2005349032920532879943884352 :=
  phaseBlock_append rec_8_15_2368_1_part0 rec_8_15_2368_1_part1 rfl rfl rfl
private theorem rec_8_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 256 256 = 828948646142999593822625344 :=
  phaseBlock_append rec_8_15_2368_1_part2 rec_8_15_2368_1_part3 rfl rfl rfl
private theorem rec_8_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 0 512 = 2834297679063532473766509696 :=
  phaseBlock_append rec_8_15_2368_1_join0 rec_8_15_2368_1_join1 rfl rfl rfl
private theorem rec_8_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 512 256 = 220730216925525447187750464 :=
  phaseBlock_append rec_8_15_2368_1_part4 rec_8_15_2368_1_part5 rfl rfl rfl
private theorem rec_8_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 896 256 = 336982344277125750698781 :=
  phaseBlock_append rec_8_15_2368_1_part7 rec_8_15_2368_1_part8 rfl rfl rfl
private theorem rec_8_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 768 384 = 14550794470350345775143485 :=
  phaseBlock_append rec_8_15_2368_1_part6 rec_8_15_2368_1_join4 rfl rfl rfl
private theorem rec_8_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 512 640 = 235281011395875792962893949 :=
  phaseBlock_append rec_8_15_2368_1_join3 rec_8_15_2368_1_join5 rfl rfl rfl
private theorem rec_8_15_2368_1_join7 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 0 1152 = 3069578690459408266729403645 :=
  phaseBlock_append rec_8_15_2368_1_join2 rec_8_15_2368_1_join6 rfl rfl rfl
private theorem rec_8_15_2368_1_join8 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1152 256 = 0 :=
  phaseBlock_append rec_8_15_2368_1_part9 rec_8_15_2368_1_part10 rfl rfl rfl
private theorem rec_8_15_2368_1_join9 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1536 256 = 0 :=
  phaseBlock_append rec_8_15_2368_1_part12 rec_8_15_2368_1_part13 rfl rfl rfl
private theorem rec_8_15_2368_1_join10 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1408 384 = 0 :=
  phaseBlock_append rec_8_15_2368_1_part11 rec_8_15_2368_1_join9 rfl rfl rfl
private theorem rec_8_15_2368_1_join11 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1152 640 = 0 :=
  phaseBlock_append rec_8_15_2368_1_join8 rec_8_15_2368_1_join10 rfl rfl rfl
private theorem rec_8_15_2368_1_join12 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1792 256 = 0 :=
  phaseBlock_append rec_8_15_2368_1_part14 rec_8_15_2368_1_part15 rfl rfl rfl
private theorem rec_8_15_2368_1_join13 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 2176 227 = 0 :=
  phaseBlock_append rec_8_15_2368_1_part17 rec_8_15_2368_1_part18 rfl rfl rfl
private theorem rec_8_15_2368_1_join14 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 2048 355 = 0 :=
  phaseBlock_append rec_8_15_2368_1_part16 rec_8_15_2368_1_join13 rfl rfl rfl
private theorem rec_8_15_2368_1_join15 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1792 611 = 0 :=
  phaseBlock_append rec_8_15_2368_1_join12 rec_8_15_2368_1_join14 rfl rfl rfl
private theorem rec_8_15_2368_1_join16 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 1152 1251 = 0 :=
  phaseBlock_append rec_8_15_2368_1_join11 rec_8_15_2368_1_join15 rfl rfl rfl
private theorem rec_8_15_2368_1_join17 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2368 105 1 0 41 1) 0 2403 = 3069578690459408266729403645 :=
  phaseBlock_append rec_8_15_2368_1_join7 rec_8_15_2368_1_join16 rfl rfl rfl

private theorem rec_8_15_2368_1 : fastPhase (bank 8 15).shape 179798 2368 105 1 0 41 1 = 3069578690459408266729403645 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_8_15_2368_1_join17

private theorem rec_8_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 0 128 = 1195480569541026057694980352 := by decide +kernel
private theorem rec_8_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 128 128 = 815813304932934015734393088 := by decide +kernel
private theorem rec_8_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 256 128 = 523913635136808112148490496 := by decide +kernel
private theorem rec_8_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 384 128 = 308412577473906383020566784 := by decide +kernel
private theorem rec_8_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 512 128 = 158467635256247534199351552 := by decide +kernel
private theorem rec_8_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 640 128 = 63752231988546073413298432 := by decide +kernel
private theorem rec_8_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 768 128 = 14445145570147442384873728 := by decide +kernel
private theorem rec_8_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 896 128 = 356694937991489020777128 := by decide +kernel
private theorem rec_8_15_2369_0_part8 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1024 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_part9 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1152 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_part10 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1280 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_part11 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1408 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_part12 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1536 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_part13 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1664 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_part14 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1792 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_part15 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1920 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_part16 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 2048 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_part17 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 2176 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_part18 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 2304 99 = 0 := by decide +kernel
private theorem rec_8_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 0 256 = 2011293874473960073429373440 :=
  phaseBlock_append rec_8_15_2369_0_part0 rec_8_15_2369_0_part1 rfl rfl rfl
private theorem rec_8_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 256 256 = 832326212610714495169057280 :=
  phaseBlock_append rec_8_15_2369_0_part2 rec_8_15_2369_0_part3 rfl rfl rfl
private theorem rec_8_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 0 512 = 2843620087084674568598430720 :=
  phaseBlock_append rec_8_15_2369_0_join0 rec_8_15_2369_0_join1 rfl rfl rfl
private theorem rec_8_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 512 256 = 222219867244793607612649984 :=
  phaseBlock_append rec_8_15_2369_0_part4 rec_8_15_2369_0_part5 rfl rfl rfl
private theorem rec_8_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 896 256 = 356694937991489020777128 :=
  phaseBlock_append rec_8_15_2369_0_part7 rec_8_15_2369_0_part8 rfl rfl rfl
private theorem rec_8_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 768 384 = 14801840508138931405650856 :=
  phaseBlock_append rec_8_15_2369_0_part6 rec_8_15_2369_0_join4 rfl rfl rfl
private theorem rec_8_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 512 640 = 237021707752932539018300840 :=
  phaseBlock_append rec_8_15_2369_0_join3 rec_8_15_2369_0_join5 rfl rfl rfl
private theorem rec_8_15_2369_0_join7 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 0 1152 = 3080641794837607107616731560 :=
  phaseBlock_append rec_8_15_2369_0_join2 rec_8_15_2369_0_join6 rfl rfl rfl
private theorem rec_8_15_2369_0_join8 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1152 256 = 0 :=
  phaseBlock_append rec_8_15_2369_0_part9 rec_8_15_2369_0_part10 rfl rfl rfl
private theorem rec_8_15_2369_0_join9 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1536 256 = 0 :=
  phaseBlock_append rec_8_15_2369_0_part12 rec_8_15_2369_0_part13 rfl rfl rfl
private theorem rec_8_15_2369_0_join10 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1408 384 = 0 :=
  phaseBlock_append rec_8_15_2369_0_part11 rec_8_15_2369_0_join9 rfl rfl rfl
private theorem rec_8_15_2369_0_join11 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1152 640 = 0 :=
  phaseBlock_append rec_8_15_2369_0_join8 rec_8_15_2369_0_join10 rfl rfl rfl
private theorem rec_8_15_2369_0_join12 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1792 256 = 0 :=
  phaseBlock_append rec_8_15_2369_0_part14 rec_8_15_2369_0_part15 rfl rfl rfl
private theorem rec_8_15_2369_0_join13 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 2176 227 = 0 :=
  phaseBlock_append rec_8_15_2369_0_part17 rec_8_15_2369_0_part18 rfl rfl rfl
private theorem rec_8_15_2369_0_join14 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 2048 355 = 0 :=
  phaseBlock_append rec_8_15_2369_0_part16 rec_8_15_2369_0_join13 rfl rfl rfl
private theorem rec_8_15_2369_0_join15 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1792 611 = 0 :=
  phaseBlock_append rec_8_15_2369_0_join12 rec_8_15_2369_0_join14 rfl rfl rfl
private theorem rec_8_15_2369_0_join16 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 1152 1251 = 0 :=
  phaseBlock_append rec_8_15_2369_0_join11 rec_8_15_2369_0_join15 rfl rfl rfl
private theorem rec_8_15_2369_0_join17 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 0) 0 2403 = 3080641794837607107616731560 :=
  phaseBlock_append rec_8_15_2369_0_join7 rec_8_15_2369_0_join16 rfl rfl rfl

private theorem rec_8_15_2369_0 : fastPhase (bank 8 15).shape 179798 2369 105 1 0 41 0 = 3080641794837607107616731560 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_8_15_2369_0_join17

private theorem rec_8_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 0 128 = 1192152968839739804301754112 := by decide +kernel
private theorem rec_8_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 128 128 = 813214014482931648683777792 := by decide +kernel
private theorem rec_8_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 256 128 = 521952394203711711678349056 := by decide +kernel
private theorem rec_8_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 384 128 = 307003207052466245779218176 := by decide +kernel
private theorem rec_8_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 512 128 = 157527957167009689214385920 := by decide +kernel
private theorem rec_8_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 640 128 = 63203987974519798060392192 := by decide +kernel
private theorem rec_8_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 768 128 = 14213916393472778356604672 := by decide +kernel
private theorem rec_8_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 896 128 = 336984734612686926981501 := by decide +kernel
private theorem rec_8_15_2369_1_part8 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1024 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_part9 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1152 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_part10 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1280 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_part11 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1408 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_part12 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1536 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_part13 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1664 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_part14 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1792 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_part15 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1920 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_part16 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 2048 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_part17 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 2176 128 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_part18 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 2304 99 = 0 := by decide +kernel
private theorem rec_8_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 0 256 = 2005366983322671452985531904 :=
  phaseBlock_append rec_8_15_2369_1_part0 rec_8_15_2369_1_part1 rfl rfl rfl
private theorem rec_8_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 256 256 = 828955601256177957457567232 :=
  phaseBlock_append rec_8_15_2369_1_part2 rec_8_15_2369_1_part3 rfl rfl rfl
private theorem rec_8_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 0 512 = 2834322584578849410443099136 :=
  phaseBlock_append rec_8_15_2369_1_join0 rec_8_15_2369_1_join1 rfl rfl rfl
private theorem rec_8_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 512 256 = 220731945141529487274778112 :=
  phaseBlock_append rec_8_15_2369_1_part4 rec_8_15_2369_1_part5 rfl rfl rfl
private theorem rec_8_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 896 256 = 336984734612686926981501 :=
  phaseBlock_append rec_8_15_2369_1_part7 rec_8_15_2369_1_part8 rfl rfl rfl
private theorem rec_8_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 768 384 = 14550901128085465283586173 :=
  phaseBlock_append rec_8_15_2369_1_part6 rec_8_15_2369_1_join4 rfl rfl rfl
private theorem rec_8_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 512 640 = 235282846269614952558364285 :=
  phaseBlock_append rec_8_15_2369_1_join3 rec_8_15_2369_1_join5 rfl rfl rfl
private theorem rec_8_15_2369_1_join7 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 0 1152 = 3069605430848464363001463421 :=
  phaseBlock_append rec_8_15_2369_1_join2 rec_8_15_2369_1_join6 rfl rfl rfl
private theorem rec_8_15_2369_1_join8 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1152 256 = 0 :=
  phaseBlock_append rec_8_15_2369_1_part9 rec_8_15_2369_1_part10 rfl rfl rfl
private theorem rec_8_15_2369_1_join9 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1536 256 = 0 :=
  phaseBlock_append rec_8_15_2369_1_part12 rec_8_15_2369_1_part13 rfl rfl rfl
private theorem rec_8_15_2369_1_join10 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1408 384 = 0 :=
  phaseBlock_append rec_8_15_2369_1_part11 rec_8_15_2369_1_join9 rfl rfl rfl
private theorem rec_8_15_2369_1_join11 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1152 640 = 0 :=
  phaseBlock_append rec_8_15_2369_1_join8 rec_8_15_2369_1_join10 rfl rfl rfl
private theorem rec_8_15_2369_1_join12 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1792 256 = 0 :=
  phaseBlock_append rec_8_15_2369_1_part14 rec_8_15_2369_1_part15 rfl rfl rfl
private theorem rec_8_15_2369_1_join13 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 2176 227 = 0 :=
  phaseBlock_append rec_8_15_2369_1_part17 rec_8_15_2369_1_part18 rfl rfl rfl
private theorem rec_8_15_2369_1_join14 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 2048 355 = 0 :=
  phaseBlock_append rec_8_15_2369_1_part16 rec_8_15_2369_1_join13 rfl rfl rfl
private theorem rec_8_15_2369_1_join15 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1792 611 = 0 :=
  phaseBlock_append rec_8_15_2369_1_join12 rec_8_15_2369_1_join14 rfl rfl rfl
private theorem rec_8_15_2369_1_join16 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 1152 1251 = 0 :=
  phaseBlock_append rec_8_15_2369_1_join11 rec_8_15_2369_1_join15 rfl rfl rfl
private theorem rec_8_15_2369_1_join17 :
    phaseBlock (fastLayerG (bank 8 15).shape 179798 2369 105 1 0 41 1) 0 2403 = 3069605430848464363001463421 :=
  phaseBlock_append rec_8_15_2369_1_join7 rec_8_15_2369_1_join16 rfl rfl rfl

private theorem rec_8_15_2369_1 : fastPhase (bank 8 15).shape 179798 2369 105 1 0 41 1 = 3069605430848464363001463421 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_8_15_2369_1_join17

theorem receipt_8_15 : Checked (bank 8 15) 105 0 41 := by
  refine checked_from_values (bank 8 15) 105 0 41
    (P3_7_1.checked (bank 8 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_10849_2402)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_15_2368_0 rec_8_15_2368_1 rec_8_15_2369_0 rec_8_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 0 128 = 5424805319477168210900031744 := by decide +kernel
private theorem rec_8_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 128 128 = 4114031906102086995925874944 := by decide +kernel
private theorem rec_8_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 256 128 = 3027193285319318807630600448 := by decide +kernel
private theorem rec_8_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 384 128 = 2143221911257717780404205824 := by decide +kernel
private theorem rec_8_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 512 128 = 1441767716672749265428584704 := by decide +kernel
private theorem rec_8_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 640 128 = 903187547518080772050106624 := by decide +kernel
private theorem rec_8_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 768 128 = 508534597517172909152196864 := by decide +kernel
private theorem rec_8_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 896 128 = 239547842734870326527916288 := by decide +kernel
private theorem rec_8_16_2368_0_part8 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1024 128 = 78641476148992656252541184 := by decide +kernel
private theorem rec_8_16_2368_0_part9 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1152 128 = 8884551466697042881452964 := by decide +kernel
private theorem rec_8_16_2368_0_part10 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1280 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part11 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1408 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part12 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1536 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part13 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1664 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part14 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1792 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part15 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1920 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part16 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2048 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part17 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2176 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part18 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2304 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part19 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2432 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part20 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2560 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part21 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2688 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part22 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2816 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part23 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2944 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part24 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 3072 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_part25 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 3200 35 = 0 := by decide +kernel
private theorem rec_8_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 128 256 = 7141225191421405803556475392 :=
  phaseBlock_append rec_8_16_2368_0_part1 rec_8_16_2368_0_part2 rfl rfl rfl
private theorem rec_8_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 0 384 = 12566030510898574014456507136 :=
  phaseBlock_append rec_8_16_2368_0_part0 rec_8_16_2368_0_join0 rfl rfl rfl
private theorem rec_8_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 512 256 = 2344955264190830037478691328 :=
  phaseBlock_append rec_8_16_2368_0_part4 rec_8_16_2368_0_part5 rfl rfl rfl
private theorem rec_8_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 384 384 = 4488177175448547817882897152 :=
  phaseBlock_append rec_8_16_2368_0_part3 rec_8_16_2368_0_join2 rfl rfl rfl
private theorem rec_8_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 0 768 = 17054207686347121832339404288 :=
  phaseBlock_append rec_8_16_2368_0_join1 rec_8_16_2368_0_join3 rfl rfl rfl
private theorem rec_8_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 896 256 = 318189318883862982780457472 :=
  phaseBlock_append rec_8_16_2368_0_part7 rec_8_16_2368_0_part8 rfl rfl rfl
private theorem rec_8_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 768 384 = 826723916401035891932654336 :=
  phaseBlock_append rec_8_16_2368_0_part6 rec_8_16_2368_0_join5 rfl rfl rfl
private theorem rec_8_16_2368_0_join7 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1152 256 = 8884551466697042881452964 :=
  phaseBlock_append rec_8_16_2368_0_part9 rec_8_16_2368_0_part10 rfl rfl rfl
private theorem rec_8_16_2368_0_join8 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1408 256 = 0 :=
  phaseBlock_append rec_8_16_2368_0_part11 rec_8_16_2368_0_part12 rfl rfl rfl
private theorem rec_8_16_2368_0_join9 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1152 512 = 8884551466697042881452964 :=
  phaseBlock_append rec_8_16_2368_0_join7 rec_8_16_2368_0_join8 rfl rfl rfl
private theorem rec_8_16_2368_0_join10 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 768 896 = 835608467867732934814107300 :=
  phaseBlock_append rec_8_16_2368_0_join6 rec_8_16_2368_0_join9 rfl rfl rfl
private theorem rec_8_16_2368_0_join11 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 0 1664 = 17889816154214854767153511588 :=
  phaseBlock_append rec_8_16_2368_0_join4 rec_8_16_2368_0_join10 rfl rfl rfl
private theorem rec_8_16_2368_0_join12 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1792 256 = 0 :=
  phaseBlock_append rec_8_16_2368_0_part14 rec_8_16_2368_0_part15 rfl rfl rfl
private theorem rec_8_16_2368_0_join13 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1664 384 = 0 :=
  phaseBlock_append rec_8_16_2368_0_part13 rec_8_16_2368_0_join12 rfl rfl rfl
private theorem rec_8_16_2368_0_join14 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2176 256 = 0 :=
  phaseBlock_append rec_8_16_2368_0_part17 rec_8_16_2368_0_part18 rfl rfl rfl
private theorem rec_8_16_2368_0_join15 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2048 384 = 0 :=
  phaseBlock_append rec_8_16_2368_0_part16 rec_8_16_2368_0_join14 rfl rfl rfl
private theorem rec_8_16_2368_0_join16 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1664 768 = 0 :=
  phaseBlock_append rec_8_16_2368_0_join13 rec_8_16_2368_0_join15 rfl rfl rfl
private theorem rec_8_16_2368_0_join17 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2560 256 = 0 :=
  phaseBlock_append rec_8_16_2368_0_part20 rec_8_16_2368_0_part21 rfl rfl rfl
private theorem rec_8_16_2368_0_join18 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2432 384 = 0 :=
  phaseBlock_append rec_8_16_2368_0_part19 rec_8_16_2368_0_join17 rfl rfl rfl
private theorem rec_8_16_2368_0_join19 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2816 256 = 0 :=
  phaseBlock_append rec_8_16_2368_0_part22 rec_8_16_2368_0_part23 rfl rfl rfl
private theorem rec_8_16_2368_0_join20 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 3072 163 = 0 :=
  phaseBlock_append rec_8_16_2368_0_part24 rec_8_16_2368_0_part25 rfl rfl rfl
private theorem rec_8_16_2368_0_join21 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2816 419 = 0 :=
  phaseBlock_append rec_8_16_2368_0_join19 rec_8_16_2368_0_join20 rfl rfl rfl
private theorem rec_8_16_2368_0_join22 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 2432 803 = 0 :=
  phaseBlock_append rec_8_16_2368_0_join18 rec_8_16_2368_0_join21 rfl rfl rfl
private theorem rec_8_16_2368_0_join23 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 1664 1571 = 0 :=
  phaseBlock_append rec_8_16_2368_0_join16 rec_8_16_2368_0_join22 rfl rfl rfl
private theorem rec_8_16_2368_0_join24 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 0) 0 3235 = 17889816154214854767153511588 :=
  phaseBlock_append rec_8_16_2368_0_join11 rec_8_16_2368_0_join23 rfl rfl rfl

private theorem rec_8_16_2368_0 : fastPhase (bank 8 16).shape 179798 2368 138 1 0 41 0 = 17889816154214854767153511588 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_8_16_2368_0_join24

private theorem rec_8_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 0 128 = 5413671705772320801867984704 := by decide +kernel
private theorem rec_8_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 128 128 = 4104724105115723348826255168 := by decide +kernel
private theorem rec_8_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 256 128 = 3019545080979215087963434816 := by decide +kernel
private theorem rec_8_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 384 128 = 2137072635260726154792333120 := by decide +kernel
private theorem rec_8_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 512 128 = 1436962167583660248953941824 := by decide +kernel
private theorem rec_8_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 640 128 = 899575909868485575590014784 := by decide +kernel
private theorem rec_8_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 768 128 = 505972360904325786715647808 := by decide +kernel
private theorem rec_8_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 896 128 = 237895720920550922591858496 := by decide +kernel
private theorem rec_8_16_2368_1_part8 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1024 128 = 77765326158368353098166080 := by decide +kernel
private theorem rec_8_16_2368_1_part9 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1152 128 = 8652683783904834217557072 := by decide +kernel
private theorem rec_8_16_2368_1_part10 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1280 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part11 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1408 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part12 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1536 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part13 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1664 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part14 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1792 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part15 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1920 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part16 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2048 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part17 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2176 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part18 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2304 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part19 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2432 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part20 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2560 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part21 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2688 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part22 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2816 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part23 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2944 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part24 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 3072 128 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_part25 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 3200 35 = 0 := by decide +kernel
private theorem rec_8_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 128 256 = 7124269186094938436789689984 :=
  phaseBlock_append rec_8_16_2368_1_part1 rec_8_16_2368_1_part2 rfl rfl rfl
private theorem rec_8_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 0 384 = 12537940891867259238657674688 :=
  phaseBlock_append rec_8_16_2368_1_part0 rec_8_16_2368_1_join0 rfl rfl rfl
private theorem rec_8_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 512 256 = 2336538077452145824543956608 :=
  phaseBlock_append rec_8_16_2368_1_part4 rec_8_16_2368_1_part5 rfl rfl rfl
private theorem rec_8_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 384 384 = 4473610712712871979336289728 :=
  phaseBlock_append rec_8_16_2368_1_part3 rec_8_16_2368_1_join2 rfl rfl rfl
private theorem rec_8_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 0 768 = 17011551604580131217993964416 :=
  phaseBlock_append rec_8_16_2368_1_join1 rec_8_16_2368_1_join3 rfl rfl rfl
private theorem rec_8_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 896 256 = 315661047078919275690024576 :=
  phaseBlock_append rec_8_16_2368_1_part7 rec_8_16_2368_1_part8 rfl rfl rfl
private theorem rec_8_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 768 384 = 821633407983245062405672384 :=
  phaseBlock_append rec_8_16_2368_1_part6 rec_8_16_2368_1_join5 rfl rfl rfl
private theorem rec_8_16_2368_1_join7 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1152 256 = 8652683783904834217557072 :=
  phaseBlock_append rec_8_16_2368_1_part9 rec_8_16_2368_1_part10 rfl rfl rfl
private theorem rec_8_16_2368_1_join8 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1408 256 = 0 :=
  phaseBlock_append rec_8_16_2368_1_part11 rec_8_16_2368_1_part12 rfl rfl rfl
private theorem rec_8_16_2368_1_join9 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1152 512 = 8652683783904834217557072 :=
  phaseBlock_append rec_8_16_2368_1_join7 rec_8_16_2368_1_join8 rfl rfl rfl
private theorem rec_8_16_2368_1_join10 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 768 896 = 830286091767149896623229456 :=
  phaseBlock_append rec_8_16_2368_1_join6 rec_8_16_2368_1_join9 rfl rfl rfl
private theorem rec_8_16_2368_1_join11 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 0 1664 = 17841837696347281114617193872 :=
  phaseBlock_append rec_8_16_2368_1_join4 rec_8_16_2368_1_join10 rfl rfl rfl
private theorem rec_8_16_2368_1_join12 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1792 256 = 0 :=
  phaseBlock_append rec_8_16_2368_1_part14 rec_8_16_2368_1_part15 rfl rfl rfl
private theorem rec_8_16_2368_1_join13 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1664 384 = 0 :=
  phaseBlock_append rec_8_16_2368_1_part13 rec_8_16_2368_1_join12 rfl rfl rfl
private theorem rec_8_16_2368_1_join14 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2176 256 = 0 :=
  phaseBlock_append rec_8_16_2368_1_part17 rec_8_16_2368_1_part18 rfl rfl rfl
private theorem rec_8_16_2368_1_join15 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2048 384 = 0 :=
  phaseBlock_append rec_8_16_2368_1_part16 rec_8_16_2368_1_join14 rfl rfl rfl
private theorem rec_8_16_2368_1_join16 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1664 768 = 0 :=
  phaseBlock_append rec_8_16_2368_1_join13 rec_8_16_2368_1_join15 rfl rfl rfl
private theorem rec_8_16_2368_1_join17 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2560 256 = 0 :=
  phaseBlock_append rec_8_16_2368_1_part20 rec_8_16_2368_1_part21 rfl rfl rfl
private theorem rec_8_16_2368_1_join18 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2432 384 = 0 :=
  phaseBlock_append rec_8_16_2368_1_part19 rec_8_16_2368_1_join17 rfl rfl rfl
private theorem rec_8_16_2368_1_join19 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2816 256 = 0 :=
  phaseBlock_append rec_8_16_2368_1_part22 rec_8_16_2368_1_part23 rfl rfl rfl
private theorem rec_8_16_2368_1_join20 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 3072 163 = 0 :=
  phaseBlock_append rec_8_16_2368_1_part24 rec_8_16_2368_1_part25 rfl rfl rfl
private theorem rec_8_16_2368_1_join21 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2816 419 = 0 :=
  phaseBlock_append rec_8_16_2368_1_join19 rec_8_16_2368_1_join20 rfl rfl rfl
private theorem rec_8_16_2368_1_join22 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 2432 803 = 0 :=
  phaseBlock_append rec_8_16_2368_1_join18 rec_8_16_2368_1_join21 rfl rfl rfl
private theorem rec_8_16_2368_1_join23 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 1664 1571 = 0 :=
  phaseBlock_append rec_8_16_2368_1_join16 rec_8_16_2368_1_join22 rfl rfl rfl
private theorem rec_8_16_2368_1_join24 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2368 138 1 0 41 1) 0 3235 = 17841837696347281114617193872 :=
  phaseBlock_append rec_8_16_2368_1_join11 rec_8_16_2368_1_join23 rfl rfl rfl

private theorem rec_8_16_2368_1 : fastPhase (bank 8 16).shape 179798 2368 138 1 0 41 1 = 17841837696347281114617193872 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_8_16_2368_1_join24

private theorem rec_8_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 0 128 = 5424854714448780552021736032 := by decide +kernel
private theorem rec_8_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 128 128 = 4114068507402696028311120480 := by decide +kernel
private theorem rec_8_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 256 128 = 3027219577735024706423609952 := by decide +kernel
private theorem rec_8_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 384 128 = 2143240067656714708496534112 := by decide +kernel
private theorem rec_8_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 512 128 = 1441779618698258899693976160 := by decide +kernel
private theorem rec_8_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 640 128 = 903194805911630020321061472 := by decide +kernel
private theorem rec_8_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 768 128 = 508538572072215817938246240 := by decide +kernel
private theorem rec_8_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 896 128 = 239549661880754179475606112 := by decide +kernel
private theorem rec_8_16_2369_0_part8 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1024 128 = 78642056165268263347124832 := by decide +kernel
private theorem rec_8_16_2369_0_part9 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1152 128 = 8884615259198334095415141 := by decide +kernel
private theorem rec_8_16_2369_0_part10 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1280 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part11 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1408 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part12 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1536 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part13 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1664 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part14 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1792 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part15 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1920 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part16 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2048 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part17 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2176 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part18 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2304 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part19 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2432 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part20 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2560 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part21 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2688 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part22 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2816 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part23 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2944 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part24 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 3072 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_part25 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 3200 35 = 0 := by decide +kernel
private theorem rec_8_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 128 256 = 7141288085137720734734730432 :=
  phaseBlock_append rec_8_16_2369_0_part1 rec_8_16_2369_0_part2 rfl rfl rfl
private theorem rec_8_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 0 384 = 12566142799586501286756466464 :=
  phaseBlock_append rec_8_16_2369_0_part0 rec_8_16_2369_0_join0 rfl rfl rfl
private theorem rec_8_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 512 256 = 2344974424609888920015037632 :=
  phaseBlock_append rec_8_16_2369_0_part4 rec_8_16_2369_0_part5 rfl rfl rfl
private theorem rec_8_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 384 384 = 4488214492266603628511571744 :=
  phaseBlock_append rec_8_16_2369_0_part3 rec_8_16_2369_0_join2 rfl rfl rfl
private theorem rec_8_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 0 768 = 17054357291853104915268038208 :=
  phaseBlock_append rec_8_16_2369_0_join1 rec_8_16_2369_0_join3 rfl rfl rfl
private theorem rec_8_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 896 256 = 318191718046022442822730944 :=
  phaseBlock_append rec_8_16_2369_0_part7 rec_8_16_2369_0_part8 rfl rfl rfl
private theorem rec_8_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 768 384 = 826730290118238260760977184 :=
  phaseBlock_append rec_8_16_2369_0_part6 rec_8_16_2369_0_join5 rfl rfl rfl
private theorem rec_8_16_2369_0_join7 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1152 256 = 8884615259198334095415141 :=
  phaseBlock_append rec_8_16_2369_0_part9 rec_8_16_2369_0_part10 rfl rfl rfl
private theorem rec_8_16_2369_0_join8 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1408 256 = 0 :=
  phaseBlock_append rec_8_16_2369_0_part11 rec_8_16_2369_0_part12 rfl rfl rfl
private theorem rec_8_16_2369_0_join9 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1152 512 = 8884615259198334095415141 :=
  phaseBlock_append rec_8_16_2369_0_join7 rec_8_16_2369_0_join8 rfl rfl rfl
private theorem rec_8_16_2369_0_join10 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 768 896 = 835614905377436594856392325 :=
  phaseBlock_append rec_8_16_2369_0_join6 rec_8_16_2369_0_join9 rfl rfl rfl
private theorem rec_8_16_2369_0_join11 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 0 1664 = 17889972197230541510124430533 :=
  phaseBlock_append rec_8_16_2369_0_join4 rec_8_16_2369_0_join10 rfl rfl rfl
private theorem rec_8_16_2369_0_join12 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1792 256 = 0 :=
  phaseBlock_append rec_8_16_2369_0_part14 rec_8_16_2369_0_part15 rfl rfl rfl
private theorem rec_8_16_2369_0_join13 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1664 384 = 0 :=
  phaseBlock_append rec_8_16_2369_0_part13 rec_8_16_2369_0_join12 rfl rfl rfl
private theorem rec_8_16_2369_0_join14 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2176 256 = 0 :=
  phaseBlock_append rec_8_16_2369_0_part17 rec_8_16_2369_0_part18 rfl rfl rfl
private theorem rec_8_16_2369_0_join15 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2048 384 = 0 :=
  phaseBlock_append rec_8_16_2369_0_part16 rec_8_16_2369_0_join14 rfl rfl rfl
private theorem rec_8_16_2369_0_join16 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1664 768 = 0 :=
  phaseBlock_append rec_8_16_2369_0_join13 rec_8_16_2369_0_join15 rfl rfl rfl
private theorem rec_8_16_2369_0_join17 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2560 256 = 0 :=
  phaseBlock_append rec_8_16_2369_0_part20 rec_8_16_2369_0_part21 rfl rfl rfl
private theorem rec_8_16_2369_0_join18 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2432 384 = 0 :=
  phaseBlock_append rec_8_16_2369_0_part19 rec_8_16_2369_0_join17 rfl rfl rfl
private theorem rec_8_16_2369_0_join19 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2816 256 = 0 :=
  phaseBlock_append rec_8_16_2369_0_part22 rec_8_16_2369_0_part23 rfl rfl rfl
private theorem rec_8_16_2369_0_join20 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 3072 163 = 0 :=
  phaseBlock_append rec_8_16_2369_0_part24 rec_8_16_2369_0_part25 rfl rfl rfl
private theorem rec_8_16_2369_0_join21 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2816 419 = 0 :=
  phaseBlock_append rec_8_16_2369_0_join19 rec_8_16_2369_0_join20 rfl rfl rfl
private theorem rec_8_16_2369_0_join22 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 2432 803 = 0 :=
  phaseBlock_append rec_8_16_2369_0_join18 rec_8_16_2369_0_join21 rfl rfl rfl
private theorem rec_8_16_2369_0_join23 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 1664 1571 = 0 :=
  phaseBlock_append rec_8_16_2369_0_join16 rec_8_16_2369_0_join22 rfl rfl rfl
private theorem rec_8_16_2369_0_join24 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 0) 0 3235 = 17889972197230541510124430533 :=
  phaseBlock_append rec_8_16_2369_0_join11 rec_8_16_2369_0_join23 rfl rfl rfl

private theorem rec_8_16_2369_0 : fastPhase (bank 8 16).shape 179798 2369 138 1 0 41 0 = 17889972197230541510124430533 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_8_16_2369_0_join24

private theorem rec_8_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 0 128 = 5413721003130052827373937120 := by decide +kernel
private theorem rec_8_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 128 128 = 4104760626438468530465378784 := by decide +kernel
private theorem rec_8_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 256 128 = 3019571309034251474877710816 := by decide +kernel
private theorem rec_8_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 384 128 = 2137090741018933556349071840 := by decide +kernel
private theorem rec_8_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 512 128 = 1436974030910258929613169120 := by decide +kernel
private theorem rec_8_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 640 128 = 899583139844119140513567200 := by decide +kernel
private theorem rec_8_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 768 128 = 505976315776488258117976544 := by decide +kernel
private theorem rec_8_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 896 128 = 237897527685358006832542176 := by decide +kernel
private theorem rec_8_16_2369_1_part8 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1024 128 = 77765899772672898516132320 := by decide +kernel
private theorem rec_8_16_2369_1_part9 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1152 128 = 8652745920895270022085235 := by decide +kernel
private theorem rec_8_16_2369_1_part10 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1280 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part11 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1408 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part12 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1536 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part13 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1664 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part14 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1792 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part15 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1920 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part16 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2048 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part17 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2176 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part18 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2304 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part19 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2432 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part20 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2560 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part21 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2688 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part22 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2816 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part23 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2944 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part24 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 3072 128 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_part25 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 3200 35 = 0 := by decide +kernel
private theorem rec_8_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 128 256 = 7124331935472720005343089600 :=
  phaseBlock_append rec_8_16_2369_1_part1 rec_8_16_2369_1_part2 rfl rfl rfl
private theorem rec_8_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 0 384 = 12538052938602772832717026720 :=
  phaseBlock_append rec_8_16_2369_1_part0 rec_8_16_2369_1_join0 rfl rfl rfl
private theorem rec_8_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 512 256 = 2336557170754378070126736320 :=
  phaseBlock_append rec_8_16_2369_1_part4 rec_8_16_2369_1_part5 rfl rfl rfl
private theorem rec_8_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 384 384 = 4473647911773311626475808160 :=
  phaseBlock_append rec_8_16_2369_1_part3 rec_8_16_2369_1_join2 rfl rfl rfl
private theorem rec_8_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 0 768 = 17011700850376084459192834880 :=
  phaseBlock_append rec_8_16_2369_1_join1 rec_8_16_2369_1_join3 rfl rfl rfl
private theorem rec_8_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 896 256 = 315663427458030905348674496 :=
  phaseBlock_append rec_8_16_2369_1_part7 rec_8_16_2369_1_part8 rfl rfl rfl
private theorem rec_8_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 768 384 = 821639743234519163466651040 :=
  phaseBlock_append rec_8_16_2369_1_part6 rec_8_16_2369_1_join5 rfl rfl rfl
private theorem rec_8_16_2369_1_join7 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1152 256 = 8652745920895270022085235 :=
  phaseBlock_append rec_8_16_2369_1_part9 rec_8_16_2369_1_part10 rfl rfl rfl
private theorem rec_8_16_2369_1_join8 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1408 256 = 0 :=
  phaseBlock_append rec_8_16_2369_1_part11 rec_8_16_2369_1_part12 rfl rfl rfl
private theorem rec_8_16_2369_1_join9 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1152 512 = 8652745920895270022085235 :=
  phaseBlock_append rec_8_16_2369_1_join7 rec_8_16_2369_1_join8 rfl rfl rfl
private theorem rec_8_16_2369_1_join10 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 768 896 = 830292489155414433488736275 :=
  phaseBlock_append rec_8_16_2369_1_join6 rec_8_16_2369_1_join9 rfl rfl rfl
private theorem rec_8_16_2369_1_join11 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 0 1664 = 17841993339531498892681571155 :=
  phaseBlock_append rec_8_16_2369_1_join4 rec_8_16_2369_1_join10 rfl rfl rfl
private theorem rec_8_16_2369_1_join12 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1792 256 = 0 :=
  phaseBlock_append rec_8_16_2369_1_part14 rec_8_16_2369_1_part15 rfl rfl rfl
private theorem rec_8_16_2369_1_join13 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1664 384 = 0 :=
  phaseBlock_append rec_8_16_2369_1_part13 rec_8_16_2369_1_join12 rfl rfl rfl
private theorem rec_8_16_2369_1_join14 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2176 256 = 0 :=
  phaseBlock_append rec_8_16_2369_1_part17 rec_8_16_2369_1_part18 rfl rfl rfl
private theorem rec_8_16_2369_1_join15 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2048 384 = 0 :=
  phaseBlock_append rec_8_16_2369_1_part16 rec_8_16_2369_1_join14 rfl rfl rfl
private theorem rec_8_16_2369_1_join16 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1664 768 = 0 :=
  phaseBlock_append rec_8_16_2369_1_join13 rec_8_16_2369_1_join15 rfl rfl rfl
private theorem rec_8_16_2369_1_join17 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2560 256 = 0 :=
  phaseBlock_append rec_8_16_2369_1_part20 rec_8_16_2369_1_part21 rfl rfl rfl
private theorem rec_8_16_2369_1_join18 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2432 384 = 0 :=
  phaseBlock_append rec_8_16_2369_1_part19 rec_8_16_2369_1_join17 rfl rfl rfl
private theorem rec_8_16_2369_1_join19 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2816 256 = 0 :=
  phaseBlock_append rec_8_16_2369_1_part22 rec_8_16_2369_1_part23 rfl rfl rfl
private theorem rec_8_16_2369_1_join20 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 3072 163 = 0 :=
  phaseBlock_append rec_8_16_2369_1_part24 rec_8_16_2369_1_part25 rfl rfl rfl
private theorem rec_8_16_2369_1_join21 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2816 419 = 0 :=
  phaseBlock_append rec_8_16_2369_1_join19 rec_8_16_2369_1_join20 rfl rfl rfl
private theorem rec_8_16_2369_1_join22 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 2432 803 = 0 :=
  phaseBlock_append rec_8_16_2369_1_join18 rec_8_16_2369_1_join21 rfl rfl rfl
private theorem rec_8_16_2369_1_join23 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 1664 1571 = 0 :=
  phaseBlock_append rec_8_16_2369_1_join16 rec_8_16_2369_1_join22 rfl rfl rfl
private theorem rec_8_16_2369_1_join24 :
    phaseBlock (fastLayerG (bank 8 16).shape 179798 2369 138 1 0 41 1) 0 3235 = 17841993339531498892681571155 :=
  phaseBlock_append rec_8_16_2369_1_join11 rec_8_16_2369_1_join23 rfl rfl rfl

private theorem rec_8_16_2369_1 : fastPhase (bank 8 16).shape 179798 2369 138 1 0 41 1 = 17841993339531498892681571155 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_8_16_2369_1_join24

theorem receipt_8_16 : Checked (bank 8 16) 138 0 41 := by
  refine checked_from_values (bank 8 16) 138 0 41
    (P3_7_1.checked (bank 8 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_14605_3234)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_16_2368_0 rec_8_16_2368_1 rec_8_16_2369_0 rec_8_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect8_checked (i : Fin 17) :
    Checked (bank 8 i) (reserve i) (excess 8) (seed 8) := by
  fin_cases i
  · exact receipt_8_0
  · exact receipt_8_1
  · exact receipt_8_2
  · exact receipt_8_3
  · exact receipt_8_4
  · exact receipt_8_5
  · exact receipt_8_6
  · exact receipt_8_7
  · exact receipt_8_8
  · exact receipt_8_9
  · exact receipt_8_10
  · exact receipt_8_11
  · exact receipt_8_12
  · exact receipt_8_13
  · exact receipt_8_14
  · exact receipt_8_15
  · exact receipt_8_16

end Lower6961.Lo.RescueSource
