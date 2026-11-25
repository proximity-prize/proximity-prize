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


private theorem rec_5_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2368 1 1 4 1 0) 0 128 = 2009718664017245895891 := by decide +kernel
private theorem rec_5_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2368 1 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2368 1 1 4 1 0) 0 130 = 2009718664017245895891 :=
  phaseBlock_append rec_5_1_2368_0_part0 rec_5_1_2368_0_part1 rfl rfl rfl

private theorem rec_5_1_2368_0 : fastPhase (bank 5 1).shape 179798 2368 1 1 4 1 0 = 2009718664017245895891 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_1_2368_0_join0

private theorem rec_5_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2368 1 1 4 1 1) 0 128 = 1968629038697128055643 := by decide +kernel
private theorem rec_5_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2368 1 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2368 1 1 4 1 1) 0 130 = 1968629038697128055643 :=
  phaseBlock_append rec_5_1_2368_1_part0 rec_5_1_2368_1_part1 rfl rfl rfl

private theorem rec_5_1_2368_1 : fastPhase (bank 5 1).shape 179798 2368 1 1 4 1 1 = 1968629038697128055643 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_1_2368_1_join0

private theorem rec_5_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2369 1 1 4 1 0) 0 128 = 2009729041645650386508 := by decide +kernel
private theorem rec_5_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2369 1 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2369 1 1 4 1 0) 0 130 = 2009729041645650386508 :=
  phaseBlock_append rec_5_1_2369_0_part0 rec_5_1_2369_0_part1 rfl rfl rfl

private theorem rec_5_1_2369_0 : fastPhase (bank 5 1).shape 179798 2369 1 1 4 1 0 = 2009729041645650386508 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_1_2369_0_join0

private theorem rec_5_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2369 1 1 4 1 1) 0 128 = 1968639122608787048154 := by decide +kernel
private theorem rec_5_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2369 1 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 1).shape 179798 2369 1 1 4 1 1) 0 130 = 1968639122608787048154 :=
  phaseBlock_append rec_5_1_2369_1_part0 rec_5_1_2369_1_part1 rfl rfl rfl

private theorem rec_5_1_2369_1 : fastPhase (bank 5 1).shape 179798 2369 1 1 4 1 1 = 1968639122608787048154 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_1_2369_1_join0

theorem receipt_5_1 : Checked (bank 5 1) 1 4 1 := by
  refine checked_from_values (bank 5 1) 1 4 1
    (P3_7_1.checked (bank 5 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_1_2368_0 rec_5_1_2368_1 rec_5_1_2369_0 rec_5_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2368 2 1 4 1 0) 0 128 = 2292361698642722669778 := by decide +kernel
private theorem rec_5_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2368 2 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2368 2 1 4 1 0) 0 130 = 2292361698642722669778 :=
  phaseBlock_append rec_5_2_2368_0_part0 rec_5_2_2368_0_part1 rfl rfl rfl

private theorem rec_5_2_2368_0 : fastPhase (bank 5 2).shape 179798 2368 2 1 4 1 0 = 2292361698642722669778 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_2_2368_0_join0

private theorem rec_5_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2368 2 1 4 1 1) 0 128 = 2245527403042692901730 := by decide +kernel
private theorem rec_5_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2368 2 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2368 2 1 4 1 1) 0 130 = 2245527403042692901730 :=
  phaseBlock_append rec_5_2_2368_1_part0 rec_5_2_2368_1_part1 rfl rfl rfl

private theorem rec_5_2_2368_1 : fastPhase (bank 5 2).shape 179798 2368 2 1 4 1 1 = 2245527403042692901730 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_2_2368_1_join0

private theorem rec_5_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2369 2 1 4 1 0) 0 128 = 2292373420681892212968 := by decide +kernel
private theorem rec_5_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2369 2 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2369 2 1 4 1 0) 0 130 = 2292373420681892212968 :=
  phaseBlock_append rec_5_2_2369_0_part0 rec_5_2_2369_0_part1 rfl rfl rfl

private theorem rec_5_2_2369_0 : fastPhase (bank 5 2).shape 179798 2369 2 1 4 1 0 = 2292373420681892212968 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_2_2369_0_join0

private theorem rec_5_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2369 2 1 4 1 1) 0 128 = 2245538793099529953144 := by decide +kernel
private theorem rec_5_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2369 2 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 2).shape 179798 2369 2 1 4 1 1) 0 130 = 2245538793099529953144 :=
  phaseBlock_append rec_5_2_2369_1_part0 rec_5_2_2369_1_part1 rfl rfl rfl

private theorem rec_5_2_2369_1 : fastPhase (bank 5 2).shape 179798 2369 2 1 4 1 1 = 2245538793099529953144 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_2_2369_1_join0

theorem receipt_5_2 : Checked (bank 5 2) 2 4 1 := by
  refine checked_from_values (bank 5 2) 2 4 1
    (P3_7_1.checked (bank 5 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_2_2368_0 rec_5_2_2368_1 rec_5_2_2369_0 rec_5_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2368 3 1 4 1 0) 0 128 = 2638916588578958066601 := by decide +kernel
private theorem rec_5_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2368 3 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2368 3 1 4 1 0) 0 130 = 2638916588578958066601 :=
  phaseBlock_append rec_5_3_2368_0_part0 rec_5_3_2368_0_part1 rfl rfl rfl

private theorem rec_5_3_2368_0 : fastPhase (bank 5 3).shape 179798 2368 3 1 4 1 0 = 2638916588578958066601 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_3_2368_0_join0

private theorem rec_5_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2368 3 1 4 1 1) 0 128 = 2585041194815408843993 := by decide +kernel
private theorem rec_5_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2368 3 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2368 3 1 4 1 1) 0 130 = 2585041194815408843993 :=
  phaseBlock_append rec_5_3_2368_1_part0 rec_5_3_2368_1_part1 rfl rfl rfl

private theorem rec_5_3_2368_1 : fastPhase (bank 5 3).shape 179798 2368 3 1 4 1 1 = 2585041194815408843993 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_3_2368_1_join0

private theorem rec_5_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2369 3 1 4 1 0) 0 128 = 2638929950244285348912 := by decide +kernel
private theorem rec_5_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2369 3 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2369 3 1 4 1 0) 0 130 = 2638929950244285348912 :=
  phaseBlock_append rec_5_3_2369_0_part0 rec_5_3_2369_0_part1 rfl rfl rfl

private theorem rec_5_3_2369_0 : fastPhase (bank 5 3).shape 179798 2369 3 1 4 1 0 = 2638929950244285348912 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_3_2369_0_join0

private theorem rec_5_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2369 3 1 4 1 1) 0 128 = 2585054177808111342258 := by decide +kernel
private theorem rec_5_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2369 3 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 3).shape 179798 2369 3 1 4 1 1) 0 130 = 2585054177808111342258 :=
  phaseBlock_append rec_5_3_2369_1_part0 rec_5_3_2369_1_part1 rfl rfl rfl

private theorem rec_5_3_2369_1 : fastPhase (bank 5 3).shape 179798 2369 3 1 4 1 1 = 2585054177808111342258 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_3_2369_1_join0

theorem receipt_5_3 : Checked (bank 5 3) 3 4 1 := by
  refine checked_from_values (bank 5 3) 3 4 1
    (P3_7_1.checked (bank 5 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_3_2368_0 rec_5_3_2368_1 rec_5_3_2369_0 rec_5_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2368 4 1 4 1 0) 0 128 = 3069472139400212137107 := by decide +kernel
private theorem rec_5_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2368 4 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2368 4 1 4 1 0) 0 130 = 3069472139400212137107 :=
  phaseBlock_append rec_5_4_2368_0_part0 rec_5_4_2368_0_part1 rfl rfl rfl

private theorem rec_5_4_2368_0 : fastPhase (bank 5 4).shape 179798 2368 4 1 4 1 0 = 3069472139400212137107 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_4_2368_0_join0

private theorem rec_5_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2368 4 1 4 1 1) 0 128 = 3006852162321459973019 := by decide +kernel
private theorem rec_5_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2368 4 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2368 4 1 4 1 1) 0 130 = 3006852162321459973019 :=
  phaseBlock_append rec_5_4_2368_1_part0 rec_5_4_2368_1_part1 rfl rfl rfl

private theorem rec_5_4_2368_1 : fastPhase (bank 5 4).shape 179798 2368 4 1 4 1 1 = 3006852162321459973019 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_4_2368_1_join0

private theorem rec_5_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2369 4 1 4 1 0) 0 128 = 3069487526989559542578 := by decide +kernel
private theorem rec_5_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2369 4 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2369 4 1 4 1 0) 0 130 = 3069487526989559542578 :=
  phaseBlock_append rec_5_4_2369_0_part0 rec_5_4_2369_0_part1 rfl rfl rfl

private theorem rec_5_4_2369_0 : fastPhase (bank 5 4).shape 179798 2369 4 1 4 1 0 = 3069487526989559542578 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_4_2369_0_join0

private theorem rec_5_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2369 4 1 4 1 1) 0 128 = 3006867113519153445474 := by decide +kernel
private theorem rec_5_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2369 4 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 4).shape 179798 2369 4 1 4 1 1) 0 130 = 3006867113519153445474 :=
  phaseBlock_append rec_5_4_2369_1_part0 rec_5_4_2369_1_part1 rfl rfl rfl

private theorem rec_5_4_2369_1 : fastPhase (bank 5 4).shape 179798 2369 4 1 4 1 1 = 3006867113519153445474 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_4_2369_1_join0

theorem receipt_5_4 : Checked (bank 5 4) 4 4 1 := by
  refine checked_from_values (bank 5 4) 4 4 1
    (P3_7_1.checked (bank 5 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_4_2368_0 rec_5_4_2368_1 rec_5_4_2369_0 rec_5_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2368 5 1 4 1 0) 0 128 = 3615147807100925070426 := by decide +kernel
private theorem rec_5_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2368 5 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2368 5 1 4 1 0) 0 130 = 3615147807100925070426 :=
  phaseBlock_append rec_5_5_2368_0_part0 rec_5_5_2368_0_part1 rfl rfl rfl

private theorem rec_5_5_2368_0 : fastPhase (bank 5 5).shape 179798 2368 5 1 4 1 0 = 3615147807100925070426 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_5_2368_0_join0

private theorem rec_5_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2368 5 1 4 1 1) 0 128 = 3541449194948105556258 := by decide +kernel
private theorem rec_5_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2368 5 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2368 5 1 4 1 1) 0 130 = 3541449194948105556258 :=
  phaseBlock_append rec_5_5_2368_1_part0 rec_5_5_2368_1_part1 rfl rfl rfl

private theorem rec_5_5_2368_1 : fastPhase (bank 5 5).shape 179798 2368 5 1 4 1 1 = 3541449194948105556258 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_5_2368_1_join0

private theorem rec_5_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2369 5 1 4 1 0) 0 128 = 3615165748684449225396 := by decide +kernel
private theorem rec_5_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2369 5 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2369 5 1 4 1 0) 0 130 = 3615165748684449225396 :=
  phaseBlock_append rec_5_5_2369_0_part0 rec_5_5_2369_0_part1 rfl rfl rfl

private theorem rec_5_5_2369_0 : fastPhase (bank 5 5).shape 179798 2369 5 1 4 1 0 = 3615165748684449225396 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_5_2369_0_join0

private theorem rec_5_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2369 5 1 4 1 1) 0 128 = 3541466627341827779952 := by decide +kernel
private theorem rec_5_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2369 5 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 5).shape 179798 2369 5 1 4 1 1) 0 130 = 3541466627341827779952 :=
  phaseBlock_append rec_5_5_2369_1_part0 rec_5_5_2369_1_part1 rfl rfl rfl

private theorem rec_5_5_2369_1 : fastPhase (bank 5 5).shape 179798 2369 5 1 4 1 1 = 3541466627341827779952 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_5_2369_1_join0

theorem receipt_5_5 : Checked (bank 5 5) 5 4 1 := by
  refine checked_from_values (bank 5 5) 5 4 1
    (P3_7_1.checked (bank 5 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_5_2368_0 rec_5_5_2368_1 rec_5_5_2369_0 rec_5_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2368 7 1 4 1 0) 0 128 = 5253166544206329328692 := by decide +kernel
private theorem rec_5_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2368 7 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2368 7 1 4 1 0) 0 130 = 5253166544206329328692 :=
  phaseBlock_append rec_5_6_2368_0_part0 rec_5_6_2368_0_part1 rfl rfl rfl

private theorem rec_5_6_2368_0 : fastPhase (bank 5 6).shape 179798 2368 7 1 4 1 0 = 5253166544206329328692 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_6_2368_0_join0

private theorem rec_5_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2368 7 1 4 1 1) 0 128 = 5146230933982532548724 := by decide +kernel
private theorem rec_5_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2368 7 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2368 7 1 4 1 1) 0 130 = 5146230933982532548724 :=
  phaseBlock_append rec_5_6_2368_1_part0 rec_5_6_2368_1_part1 rfl rfl rfl

private theorem rec_5_6_2368_1 : fastPhase (bank 5 6).shape 179798 2368 7 1 4 1 1 = 5146230933982532548724 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_6_2368_1_join0

private theorem rec_5_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2369 7 1 4 1 0) 0 128 = 5253192087438198241404 := by decide +kernel
private theorem rec_5_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2369 7 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2369 7 1 4 1 0) 0 130 = 5253192087438198241404 :=
  phaseBlock_append rec_5_6_2369_0_part0 rec_5_6_2369_0_part1 rfl rfl rfl

private theorem rec_5_6_2369_0 : fastPhase (bank 5 6).shape 179798 2369 7 1 4 1 0 = 5253192087438198241404 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_6_2369_0_join0

private theorem rec_5_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2369 7 1 4 1 1) 0 128 = 5146255751184157265460 := by decide +kernel
private theorem rec_5_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2369 7 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 6).shape 179798 2369 7 1 4 1 1) 0 130 = 5146255751184157265460 :=
  phaseBlock_append rec_5_6_2369_1_part0 rec_5_6_2369_1_part1 rfl rfl rfl

private theorem rec_5_6_2369_1 : fastPhase (bank 5 6).shape 179798 2369 7 1 4 1 1 = 5146255751184157265460 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_6_2369_1_join0

theorem receipt_5_6 : Checked (bank 5 6) 7 4 1 := by
  refine checked_from_values (bank 5 6) 7 4 1
    (P3_7_1.checked (bank 5 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_6_2368_0 rec_5_6_2368_1 rec_5_6_2369_0 rec_5_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2368 10 1 4 1 0) 0 128 = 10955951927274183723864 := by decide +kernel
private theorem rec_5_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2368 10 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2368 10 1 4 1 0) 0 130 = 10955951927274183723864 :=
  phaseBlock_append rec_5_7_2368_0_part0 rec_5_7_2368_0_part1 rfl rfl rfl

private theorem rec_5_7_2368_0 : fastPhase (bank 5 7).shape 179798 2368 10 1 4 1 0 = 10955951927274183723864 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_7_2368_0_join0

private theorem rec_5_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2368 10 1 4 1 1) 0 128 = 10733414040178024435376 := by decide +kernel
private theorem rec_5_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2368 10 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2368 10 1 4 1 1) 0 130 = 10733414040178024435376 :=
  phaseBlock_append rec_5_7_2368_1_part0 rec_5_7_2368_1_part1 rfl rfl rfl

private theorem rec_5_7_2368_1 : fastPhase (bank 5 7).shape 179798 2368 10 1 4 1 1 = 10733414040178024435376 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_7_2368_1_join0

private theorem rec_5_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2369 10 1 4 1 0) 0 128 = 10956003548898090562308 := by decide +kernel
private theorem rec_5_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2369 10 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2369 10 1 4 1 0) 0 130 = 10956003548898090562308 :=
  phaseBlock_append rec_5_7_2369_0_part0 rec_5_7_2369_0_part1 rfl rfl rfl

private theorem rec_5_7_2369_0 : fastPhase (bank 5 7).shape 179798 2369 10 1 4 1 0 = 10956003548898090562308 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_7_2369_0_join0

private theorem rec_5_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2369 10 1 4 1 1) 0 128 = 10733464190875245013014 := by decide +kernel
private theorem rec_5_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2369 10 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 7).shape 179798 2369 10 1 4 1 1) 0 130 = 10733464190875245013014 :=
  phaseBlock_append rec_5_7_2369_1_part0 rec_5_7_2369_1_part1 rfl rfl rfl

private theorem rec_5_7_2369_1 : fastPhase (bank 5 7).shape 179798 2369 10 1 4 1 1 = 10733464190875245013014 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_7_2369_1_join0

theorem receipt_5_7 : Checked (bank 5 7) 10 4 1 := by
  refine checked_from_values (bank 5 7) 10 4 1
    (P3_7_1.checked (bank 5 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_7_2368_0 rec_5_7_2368_1 rec_5_7_2369_0 rec_5_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2368 16 1 4 1 0) 0 128 = 58697046426101755991808 := by decide +kernel
private theorem rec_5_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2368 16 1 4 1 0) 128 63 = 1877230536165375961026 := by decide +kernel
private theorem rec_5_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2368 16 1 4 1 0) 0 191 = 60574276962267131952834 :=
  phaseBlock_append rec_5_8_2368_0_part0 rec_5_8_2368_0_part1 rfl rfl rfl

private theorem rec_5_8_2368_0 : fastPhase (bank 5 8).shape 179798 2368 16 1 4 1 0 = 60574276962267131952834 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_5_8_2368_0_join0

private theorem rec_5_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2368 16 1 4 1 1) 0 128 = 57963939804644435452032 := by decide +kernel
private theorem rec_5_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2368 16 1 4 1 1) 128 63 = 1770456830299968141650 := by decide +kernel
private theorem rec_5_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2368 16 1 4 1 1) 0 191 = 59734396634944403593682 :=
  phaseBlock_append rec_5_8_2368_1_part0 rec_5_8_2368_1_part1 rfl rfl rfl

private theorem rec_5_8_2368_1 : fastPhase (bank 5 8).shape 179798 2368 16 1 4 1 1 = 59734396634944403593682 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_5_8_2368_1_join0

private theorem rec_5_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2369 16 1 4 1 0) 0 128 = 58697330758939602951552 := by decide +kernel
private theorem rec_5_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2369 16 1 4 1 0) 128 63 = 1877228710899108648728 := by decide +kernel
private theorem rec_5_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2369 16 1 4 1 0) 0 191 = 60574559469838711600280 :=
  phaseBlock_append rec_5_8_2369_0_part0 rec_5_8_2369_0_part1 rfl rfl rfl

private theorem rec_5_8_2369_0 : fastPhase (bank 5 8).shape 179798 2369 16 1 4 1 0 = 60574559469838711600280 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_5_8_2369_0_join0

private theorem rec_5_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2369 16 1 4 1 1) 0 128 = 57964218540984969723648 := by decide +kernel
private theorem rec_5_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2369 16 1 4 1 1) 128 63 = 1770455095791132143196 := by decide +kernel
private theorem rec_5_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 8).shape 179798 2369 16 1 4 1 1) 0 191 = 59734673636776101866844 :=
  phaseBlock_append rec_5_8_2369_1_part0 rec_5_8_2369_1_part1 rfl rfl rfl

private theorem rec_5_8_2369_1 : fastPhase (bank 5 8).shape 179798 2369 16 1 4 1 1 = 59734673636776101866844 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_5_8_2369_1_join0

theorem receipt_5_8 : Checked (bank 5 8) 16 4 1 := by
  refine checked_from_values (bank 5 8) 16 4 1
    (P3_7_1.checked (bank 5 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_8_2368_0 rec_5_8_2368_1 rec_5_8_2369_0 rec_5_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2368 10 1 4 1 0) 0 128 = 10955951927274183723864 := by decide +kernel
private theorem rec_5_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2368 10 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2368 10 1 4 1 0) 0 130 = 10955951927274183723864 :=
  phaseBlock_append rec_5_9_2368_0_part0 rec_5_9_2368_0_part1 rfl rfl rfl

private theorem rec_5_9_2368_0 : fastPhase (bank 5 9).shape 179798 2368 10 1 4 1 0 = 10955951927274183723864 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_9_2368_0_join0

private theorem rec_5_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2368 10 1 4 1 1) 0 128 = 10733414040178024435376 := by decide +kernel
private theorem rec_5_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2368 10 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2368 10 1 4 1 1) 0 130 = 10733414040178024435376 :=
  phaseBlock_append rec_5_9_2368_1_part0 rec_5_9_2368_1_part1 rfl rfl rfl

private theorem rec_5_9_2368_1 : fastPhase (bank 5 9).shape 179798 2368 10 1 4 1 1 = 10733414040178024435376 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_9_2368_1_join0

private theorem rec_5_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2369 10 1 4 1 0) 0 128 = 10956003548898090562308 := by decide +kernel
private theorem rec_5_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2369 10 1 4 1 0) 128 2 = 0 := by decide +kernel
private theorem rec_5_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2369 10 1 4 1 0) 0 130 = 10956003548898090562308 :=
  phaseBlock_append rec_5_9_2369_0_part0 rec_5_9_2369_0_part1 rfl rfl rfl

private theorem rec_5_9_2369_0 : fastPhase (bank 5 9).shape 179798 2369 10 1 4 1 0 = 10956003548898090562308 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_9_2369_0_join0

private theorem rec_5_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2369 10 1 4 1 1) 0 128 = 10733464190875245013014 := by decide +kernel
private theorem rec_5_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2369 10 1 4 1 1) 128 2 = 0 := by decide +kernel
private theorem rec_5_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 9).shape 179798 2369 10 1 4 1 1) 0 130 = 10733464190875245013014 :=
  phaseBlock_append rec_5_9_2369_1_part0 rec_5_9_2369_1_part1 rfl rfl rfl

private theorem rec_5_9_2369_1 : fastPhase (bank 5 9).shape 179798 2369 10 1 4 1 1 = 10733464190875245013014 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_5_9_2369_1_join0

theorem receipt_5_9 : Checked (bank 5 9) 10 4 1 := by
  refine checked_from_values (bank 5 9) 10 4 1
    (P3_7_1.checked (bank 5 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_9_2368_0 rec_5_9_2368_1 rec_5_9_2369_0 rec_5_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2368 20 1 4 1 0) 0 128 = 118172917662528032305888 := by decide +kernel
private theorem rec_5_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2368 20 1 4 1 0) 128 63 = 3793695727842697678241 := by decide +kernel
private theorem rec_5_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2368 20 1 4 1 0) 0 191 = 121966613390370729984129 :=
  phaseBlock_append rec_5_10_2368_0_part0 rec_5_10_2368_0_part1 rfl rfl rfl

private theorem rec_5_10_2368_0 : fastPhase (bank 5 10).shape 179798 2368 20 1 4 1 0 = 121966613390370729984129 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_5_10_2368_0_join0

private theorem rec_5_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2368 20 1 4 1 1) 0 128 = 116700826237212146498400 := by decide +kernel
private theorem rec_5_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2368 20 1 4 1 1) 128 63 = 3578020947626921430353 := by decide +kernel
private theorem rec_5_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2368 20 1 4 1 1) 0 191 = 120278847184839067928753 :=
  phaseBlock_append rec_5_10_2368_1_part0 rec_5_10_2368_1_part1 rfl rfl rfl

private theorem rec_5_10_2368_1 : fastPhase (bank 5 10).shape 179798 2368 20 1 4 1 1 = 120278847184839067928753 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_5_10_2368_1_join0

private theorem rec_5_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2369 20 1 4 1 0) 0 128 = 118173473959351832990592 := by decide +kernel
private theorem rec_5_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2369 20 1 4 1 0) 128 63 = 3793691661752087178936 := by decide +kernel
private theorem rec_5_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2369 20 1 4 1 0) 0 191 = 121967165621103920169528 :=
  phaseBlock_append rec_5_10_2369_0_part0 rec_5_10_2369_0_part1 rfl rfl rfl

private theorem rec_5_10_2369_0 : fastPhase (bank 5 10).shape 179798 2369 20 1 4 1 0 = 121967165621103920169528 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_5_10_2369_0_join0

private theorem rec_5_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2369 20 1 4 1 1) 0 128 = 116701371538579453366080 := by decide +kernel
private theorem rec_5_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2369 20 1 4 1 1) 128 63 = 3578017087052896927782 := by decide +kernel
private theorem rec_5_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 10).shape 179798 2369 20 1 4 1 1) 0 191 = 120279388625632350293862 :=
  phaseBlock_append rec_5_10_2369_1_part0 rec_5_10_2369_1_part1 rfl rfl rfl

private theorem rec_5_10_2369_1 : fastPhase (bank 5 10).shape 179798 2369 20 1 4 1 1 = 120279388625632350293862 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_5_10_2369_1_join0

theorem receipt_5_10 : Checked (bank 5 10) 20 4 1 := by
  refine checked_from_values (bank 5 10) 20 4 1
    (P3_7_1.checked (bank 5 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_10_2368_0 rec_5_10_2368_1 rec_5_10_2369_0 rec_5_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2368 32 1 4 1 0) 0 128 = 755908147055098965047104 := by decide +kernel
private theorem rec_5_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2368 32 1 4 1 0) 128 128 = 147079202995791116670160 := by decide +kernel
private theorem rec_5_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2368 32 1 4 1 0) 256 22 = 0 := by decide +kernel
private theorem rec_5_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2368 32 1 4 1 0) 128 150 = 147079202995791116670160 :=
  phaseBlock_append rec_5_11_2368_0_part1 rec_5_11_2368_0_part2 rfl rfl rfl
private theorem rec_5_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2368 32 1 4 1 0) 0 278 = 902987350050890081717264 :=
  phaseBlock_append rec_5_11_2368_0_part0 rec_5_11_2368_0_join0 rfl rfl rfl

private theorem rec_5_11_2368_0 : fastPhase (bank 5 11).shape 179798 2368 32 1 4 1 0 = 902987350050890081717264 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_5_11_2368_0_join1

private theorem rec_5_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2368 32 1 4 1 1) 0 128 = 750379460786311186939200 := by decide +kernel
private theorem rec_5_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2368 32 1 4 1 1) 128 128 = 143981235909447232244549 := by decide +kernel
private theorem rec_5_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2368 32 1 4 1 1) 256 22 = 0 := by decide +kernel
private theorem rec_5_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2368 32 1 4 1 1) 128 150 = 143981235909447232244549 :=
  phaseBlock_append rec_5_11_2368_1_part1 rec_5_11_2368_1_part2 rfl rfl rfl
private theorem rec_5_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2368 32 1 4 1 1) 0 278 = 894360696695758419183749 :=
  phaseBlock_append rec_5_11_2368_1_part0 rec_5_11_2368_1_join0 rfl rfl rfl

private theorem rec_5_11_2368_1 : fastPhase (bank 5 11).shape 179798 2368 32 1 4 1 1 = 894360696695758419183749 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_5_11_2368_1_join1

private theorem rec_5_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2369 32 1 4 1 0) 0 128 = 755912129564337038351584 := by decide +kernel
private theorem rec_5_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2369 32 1 4 1 0) 128 128 = 147079241843684912580440 := by decide +kernel
private theorem rec_5_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2369 32 1 4 1 0) 256 22 = 0 := by decide +kernel
private theorem rec_5_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2369 32 1 4 1 0) 128 150 = 147079241843684912580440 :=
  phaseBlock_append rec_5_11_2369_0_part1 rec_5_11_2369_0_part2 rfl rfl rfl
private theorem rec_5_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2369 32 1 4 1 0) 0 278 = 902991371408021950932024 :=
  phaseBlock_append rec_5_11_2369_0_part0 rec_5_11_2369_0_join0 rfl rfl rfl

private theorem rec_5_11_2369_0 : fastPhase (bank 5 11).shape 179798 2369 32 1 4 1 0 = 902991371408021950932024 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_5_11_2369_0_join1

private theorem rec_5_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2369 32 1 4 1 1) 0 128 = 750383390791124705191200 := by decide +kernel
private theorem rec_5_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2369 32 1 4 1 1) 128 128 = 143981272831737910444027 := by decide +kernel
private theorem rec_5_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2369 32 1 4 1 1) 256 22 = 0 := by decide +kernel
private theorem rec_5_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2369 32 1 4 1 1) 128 150 = 143981272831737910444027 :=
  phaseBlock_append rec_5_11_2369_1_part1 rec_5_11_2369_1_part2 rfl rfl rfl
private theorem rec_5_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 5 11).shape 179798 2369 32 1 4 1 1) 0 278 = 894364663622862615635227 :=
  phaseBlock_append rec_5_11_2369_1_part0 rec_5_11_2369_1_join0 rfl rfl rfl

private theorem rec_5_11_2369_1 : fastPhase (bank 5 11).shape 179798 2369 32 1 4 1 1 = 894364663622862615635227 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_5_11_2369_1_join1

theorem receipt_5_11 : Checked (bank 5 11) 32 4 1 := by
  refine checked_from_values (bank 5 11) 32 4 1
    (P3_7_1.checked (bank 5 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_11_2368_0 rec_5_11_2368_1 rec_5_11_2369_0 rec_5_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2368 31 1 4 1 0) 0 128 = 667327467903351226704128 := by decide +kernel
private theorem rec_5_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2368 31 1 4 1 0) 128 128 = 129776732272110631470826 := by decide +kernel
private theorem rec_5_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2368 31 1 4 1 0) 256 22 = 0 := by decide +kernel
private theorem rec_5_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2368 31 1 4 1 0) 128 150 = 129776732272110631470826 :=
  phaseBlock_append rec_5_12_2368_0_part1 rec_5_12_2368_0_part2 rfl rfl rfl
private theorem rec_5_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2368 31 1 4 1 0) 0 278 = 797104200175461858174954 :=
  phaseBlock_append rec_5_12_2368_0_part0 rec_5_12_2368_0_join0 rfl rfl rfl

private theorem rec_5_12_2368_0 : fastPhase (bank 5 12).shape 179798 2368 31 1 4 1 0 = 797104200175461858174954 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_5_12_2368_0_join1

private theorem rec_5_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2368 31 1 4 1 1) 0 128 = 662443720041991207900800 := by decide +kernel
private theorem rec_5_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2368 31 1 4 1 1) 128 128 = 127042773902323047365121 := by decide +kernel
private theorem rec_5_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2368 31 1 4 1 1) 256 22 = 0 := by decide +kernel
private theorem rec_5_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2368 31 1 4 1 1) 128 150 = 127042773902323047365121 :=
  phaseBlock_append rec_5_12_2368_1_part1 rec_5_12_2368_1_part2 rfl rfl rfl
private theorem rec_5_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2368 31 1 4 1 1) 0 278 = 789486493944314255265921 :=
  phaseBlock_append rec_5_12_2368_1_part0 rec_5_12_2368_1_join0 rfl rfl rfl

private theorem rec_5_12_2368_1 : fastPhase (bank 5 12).shape 179798 2368 31 1 4 1 1 = 789486493944314255265921 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_5_12_2368_1_join1

private theorem rec_5_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2369 31 1 4 1 0) 0 128 = 667330999709711540779936 := by decide +kernel
private theorem rec_5_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2369 31 1 4 1 0) 128 128 = 129776768970280035331238 := by decide +kernel
private theorem rec_5_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2369 31 1 4 1 0) 256 22 = 0 := by decide +kernel
private theorem rec_5_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2369 31 1 4 1 0) 128 150 = 129776768970280035331238 :=
  phaseBlock_append rec_5_12_2369_0_part1 rec_5_12_2369_0_part2 rfl rfl rfl
private theorem rec_5_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2369 31 1 4 1 0) 0 278 = 797107768679991576111174 :=
  phaseBlock_append rec_5_12_2369_0_part0 rec_5_12_2369_0_join0 rfl rfl rfl

private theorem rec_5_12_2369_0 : fastPhase (bank 5 12).shape 179798 2369 31 1 4 1 0 = 797107768679991576111174 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_5_12_2369_0_join1

private theorem rec_5_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2369 31 1 4 1 1) 0 128 = 662447205325104842881632 := by decide +kernel
private theorem rec_5_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2369 31 1 4 1 1) 128 128 = 127042808846455907303073 := by decide +kernel
private theorem rec_5_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2369 31 1 4 1 1) 256 22 = 0 := by decide +kernel
private theorem rec_5_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2369 31 1 4 1 1) 128 150 = 127042808846455907303073 :=
  phaseBlock_append rec_5_12_2369_1_part1 rec_5_12_2369_1_part2 rfl rfl rfl
private theorem rec_5_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 5 12).shape 179798 2369 31 1 4 1 1) 0 278 = 789490014171560750184705 :=
  phaseBlock_append rec_5_12_2369_1_part0 rec_5_12_2369_1_join0 rfl rfl rfl

private theorem rec_5_12_2369_1 : fastPhase (bank 5 12).shape 179798 2369 31 1 4 1 1 = 789490014171560750184705 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_5_12_2369_1_join1

theorem receipt_5_12 : Checked (bank 5 12) 31 4 1 := by
  refine checked_from_values (bank 5 12) 31 4 1
    (P3_7_1.checked (bank 5 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_12_2368_0 rec_5_12_2368_1 rec_5_12_2369_0 rec_5_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2368 44 1 4 1 0) 0 128 = 2959960678350501295482400 := by decide +kernel
private theorem rec_5_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2368 44 1 4 1 0) 128 128 = 1148859698937135876249120 := by decide +kernel
private theorem rec_5_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2368 44 1 4 1 0) 256 114 = 99441020463412944961260 := by decide +kernel
private theorem rec_5_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2368 44 1 4 1 0) 128 242 = 1248300719400548821210380 :=
  phaseBlock_append rec_5_13_2368_0_part1 rec_5_13_2368_0_part2 rfl rfl rfl
private theorem rec_5_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2368 44 1 4 1 0) 0 370 = 4208261397751050116692780 :=
  phaseBlock_append rec_5_13_2368_0_part0 rec_5_13_2368_0_join0 rfl rfl rfl

private theorem rec_5_13_2368_0 : fastPhase (bank 5 13).shape 179798 2368 44 1 4 1 0 = 4208261397751050116692780 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_5_13_2368_0_join1

private theorem rec_5_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2368 44 1 4 1 1) 0 128 = 2945282281286044432033824 := by decide +kernel
private theorem rec_5_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2368 44 1 4 1 1) 128 128 = 1136591570295150209349664 := by decide +kernel
private theorem rec_5_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2368 44 1 4 1 1) 256 114 = 96172337145305099113967 := by decide +kernel
private theorem rec_5_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2368 44 1 4 1 1) 128 242 = 1232763907440455308463631 :=
  phaseBlock_append rec_5_13_2368_1_part1 rec_5_13_2368_1_part2 rfl rfl rfl
private theorem rec_5_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2368 44 1 4 1 1) 0 370 = 4178046188726499740497455 :=
  phaseBlock_append rec_5_13_2368_1_part0 rec_5_13_2368_1_join0 rfl rfl rfl

private theorem rec_5_13_2368_1 : fastPhase (bank 5 13).shape 179798 2368 44 1 4 1 1 = 4178046188726499740497455 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_5_13_2368_1_join1

private theorem rec_5_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2369 44 1 4 1 0) 0 128 = 2959977925826186416014720 := by decide +kernel
private theorem rec_5_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2369 44 1 4 1 0) 128 128 = 1148861236103523456746880 := by decide +kernel
private theorem rec_5_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2369 44 1 4 1 0) 256 114 = 99440893384916044537140 := by decide +kernel
private theorem rec_5_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2369 44 1 4 1 0) 128 242 = 1248302129488439501284020 :=
  phaseBlock_append rec_5_13_2369_0_part1 rec_5_13_2369_0_part2 rfl rfl rfl
private theorem rec_5_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2369 44 1 4 1 0) 0 370 = 4208280055314625917298740 :=
  phaseBlock_append rec_5_13_2369_0_part0 rec_5_13_2369_0_join0 rfl rfl rfl

private theorem rec_5_13_2369_0 : fastPhase (bank 5 13).shape 179798 2369 44 1 4 1 0 = 4208280055314625917298740 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_5_13_2369_0_join1

private theorem rec_5_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2369 44 1 4 1 1) 0 128 = 2945299365153497521026432 := by decide +kernel
private theorem rec_5_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2369 44 1 4 1 1) 128 128 = 1136593077196452562900352 := by decide +kernel
private theorem rec_5_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2369 44 1 4 1 1) 256 114 = 96172213915052225673451 := by decide +kernel
private theorem rec_5_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2369 44 1 4 1 1) 128 242 = 1232765291111504788573803 :=
  phaseBlock_append rec_5_13_2369_1_part1 rec_5_13_2369_1_part2 rfl rfl rfl
private theorem rec_5_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 5 13).shape 179798 2369 44 1 4 1 1) 0 370 = 4178064656265002309600235 :=
  phaseBlock_append rec_5_13_2369_1_part0 rec_5_13_2369_1_join0 rfl rfl rfl

private theorem rec_5_13_2369_1 : fastPhase (bank 5 13).shape 179798 2369 44 1 4 1 1 = 4178064656265002309600235 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_5_13_2369_1_join1

theorem receipt_5_13 : Checked (bank 5 13) 44 4 1 := by
  refine checked_from_values (bank 5 13) 44 4 1
    (P3_7_1.checked (bank 5 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_13_2368_0 rec_5_13_2368_1 rec_5_13_2369_0 rec_5_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 0 128 = 40496165778974368847189824 := by decide +kernel
private theorem rec_5_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 128 128 = 27980207201326097502689088 := by decide +kernel
private theorem rec_5_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 256 128 = 16052561790952717901518656 := by decide +kernel
private theorem rec_5_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 384 128 = 6433998035697365600884544 := by decide +kernel
private theorem rec_5_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 512 128 = 854079840489544571119298 := by decide +kernel
private theorem rec_5_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 640 38 = 0 := by decide +kernel
private theorem rec_5_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 128 256 = 44032768992278815404207744 :=
  phaseBlock_append rec_5_14_2368_0_part1 rec_5_14_2368_0_part2 rfl rfl rfl
private theorem rec_5_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 0 384 = 84528934771253184251397568 :=
  phaseBlock_append rec_5_14_2368_0_part0 rec_5_14_2368_0_join0 rfl rfl rfl
private theorem rec_5_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 512 166 = 854079840489544571119298 :=
  phaseBlock_append rec_5_14_2368_0_part4 rec_5_14_2368_0_part5 rfl rfl rfl
private theorem rec_5_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 384 294 = 7288077876186910172003842 :=
  phaseBlock_append rec_5_14_2368_0_part3 rec_5_14_2368_0_join2 rfl rfl rfl
private theorem rec_5_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 0) 0 678 = 91817012647440094423401410 :=
  phaseBlock_append rec_5_14_2368_0_join1 rec_5_14_2368_0_join3 rfl rfl rfl

private theorem rec_5_14_2368_0 : fastPhase (bank 5 14).shape 179798 2368 76 1 4 1 0 = 91817012647440094423401410 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_5_14_2368_0_join4

private theorem rec_5_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 0 128 = 40401611196606633779025472 := by decide +kernel
private theorem rec_5_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 128 128 = 27883082196516022857373248 := by decide +kernel
private theorem rec_5_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 256 128 = 15966559347549538778207808 := by decide +kernel
private theorem rec_5_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 384 128 = 6372512704764682375108160 := by decide +kernel
private theorem rec_5_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 512 128 = 832260694442099579874146 := by decide +kernel
private theorem rec_5_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 640 38 = 0 := by decide +kernel
private theorem rec_5_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 128 256 = 43849641544065561635581056 :=
  phaseBlock_append rec_5_14_2368_1_part1 rec_5_14_2368_1_part2 rfl rfl rfl
private theorem rec_5_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 0 384 = 84251252740672195414606528 :=
  phaseBlock_append rec_5_14_2368_1_part0 rec_5_14_2368_1_join0 rfl rfl rfl
private theorem rec_5_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 512 166 = 832260694442099579874146 :=
  phaseBlock_append rec_5_14_2368_1_part4 rec_5_14_2368_1_part5 rfl rfl rfl
private theorem rec_5_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 384 294 = 7204773399206781954982306 :=
  phaseBlock_append rec_5_14_2368_1_part3 rec_5_14_2368_1_join2 rfl rfl rfl
private theorem rec_5_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2368 76 1 4 1 1) 0 678 = 91456026139878977369588834 :=
  phaseBlock_append rec_5_14_2368_1_join1 rec_5_14_2368_1_join3 rfl rfl rfl

private theorem rec_5_14_2368_1 : fastPhase (bank 5 14).shape 179798 2368 76 1 4 1 1 = 91456026139878977369588834 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_5_14_2368_1_join4

private theorem rec_5_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 0 128 = 40496446822381983251635968 := by decide +kernel
private theorem rec_5_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 128 128 = 27980315848679411506929408 := by decide +kernel
private theorem rec_5_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 256 128 = 16052586422949913953869568 := by decide +kernel
private theorem rec_5_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 384 128 = 6433996118547513569861376 := by decide +kernel
private theorem rec_5_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 512 128 = 854078461675822138033992 := by decide +kernel
private theorem rec_5_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 640 38 = 0 := by decide +kernel
private theorem rec_5_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 128 256 = 44032902271629325460798976 :=
  phaseBlock_append rec_5_14_2369_0_part1 rec_5_14_2369_0_part2 rfl rfl rfl
private theorem rec_5_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 0 384 = 84529349094011308712434944 :=
  phaseBlock_append rec_5_14_2369_0_part0 rec_5_14_2369_0_join0 rfl rfl rfl
private theorem rec_5_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 512 166 = 854078461675822138033992 :=
  phaseBlock_append rec_5_14_2369_0_part4 rec_5_14_2369_0_part5 rfl rfl rfl
private theorem rec_5_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 384 294 = 7288074580223335707895368 :=
  phaseBlock_append rec_5_14_2369_0_part3 rec_5_14_2369_0_join2 rfl rfl rfl
private theorem rec_5_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 0) 0 678 = 91817423674234644420330312 :=
  phaseBlock_append rec_5_14_2369_0_join1 rec_5_14_2369_0_join3 rfl rfl rfl

private theorem rec_5_14_2369_0 : fastPhase (bank 5 14).shape 179798 2369 76 1 4 1 0 = 91817423674234644420330312 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_5_14_2369_0_join4

private theorem rec_5_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 0 128 = 40401890893953949492521216 := by decide +kernel
private theorem rec_5_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 128 128 = 27883190141113466226993408 := by decide +kernel
private theorem rec_5_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 256 128 = 15966583719129778327955712 := by decide +kernel
private theorem rec_5_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 384 128 = 6372510773015885521971456 := by decide +kernel
private theorem rec_5_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 512 128 = 832259349547159792398576 := by decide +kernel
private theorem rec_5_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 640 38 = 0 := by decide +kernel
private theorem rec_5_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 128 256 = 43849773860243244554949120 :=
  phaseBlock_append rec_5_14_2369_1_part1 rec_5_14_2369_1_part2 rfl rfl rfl
private theorem rec_5_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 0 384 = 84251664754197194047470336 :=
  phaseBlock_append rec_5_14_2369_1_part0 rec_5_14_2369_1_join0 rfl rfl rfl
private theorem rec_5_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 512 166 = 832259349547159792398576 :=
  phaseBlock_append rec_5_14_2369_1_part4 rec_5_14_2369_1_part5 rfl rfl rfl
private theorem rec_5_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 384 294 = 7204770122563045314370032 :=
  phaseBlock_append rec_5_14_2369_1_part3 rec_5_14_2369_1_join2 rfl rfl rfl
private theorem rec_5_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 5 14).shape 179798 2369 76 1 4 1 1) 0 678 = 91456434876760239361840368 :=
  phaseBlock_append rec_5_14_2369_1_join1 rec_5_14_2369_1_join3 rfl rfl rfl

private theorem rec_5_14_2369_1 : fastPhase (bank 5 14).shape 179798 2369 76 1 4 1 1 = 91456434876760239361840368 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_5_14_2369_1_join4

theorem receipt_5_14 : Checked (bank 5 14) 76 4 1 := by
  refine checked_from_values (bank 5 14) 76 4 1
    (P3_7_1.checked (bank 5 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_14_2368_0 rec_5_14_2368_1 rec_5_14_2369_0 rec_5_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 0 128 = 186616628903881925462808320 := by decide +kernel
private theorem rec_5_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 128 128 = 146180153464333430276011776 := by decide +kernel
private theorem rec_5_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 256 128 = 105495482979416041796802304 := by decide +kernel
private theorem rec_5_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 384 128 = 67602431212145643056232192 := by decide +kernel
private theorem rec_5_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 512 128 = 35490554583319076568880896 := by decide +kernel
private theorem rec_5_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 640 128 = 12099412587896491916015360 := by decide +kernel
private theorem rec_5_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 768 128 = 809720065846254596750384 := by decide +kernel
private theorem rec_5_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 896 29 = 0 := by decide +kernel
private theorem rec_5_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 0 256 = 332796782368215355738820096 :=
  phaseBlock_append rec_5_15_2368_0_part0 rec_5_15_2368_0_part1 rfl rfl rfl
private theorem rec_5_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 256 256 = 173097914191561684853034496 :=
  phaseBlock_append rec_5_15_2368_0_part2 rec_5_15_2368_0_part3 rfl rfl rfl
private theorem rec_5_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 0 512 = 505894696559777040591854592 :=
  phaseBlock_append rec_5_15_2368_0_join0 rec_5_15_2368_0_join1 rfl rfl rfl
private theorem rec_5_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 512 256 = 47589967171215568484896256 :=
  phaseBlock_append rec_5_15_2368_0_part4 rec_5_15_2368_0_part5 rfl rfl rfl
private theorem rec_5_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 768 157 = 809720065846254596750384 :=
  phaseBlock_append rec_5_15_2368_0_part6 rec_5_15_2368_0_part7 rfl rfl rfl
private theorem rec_5_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 512 413 = 48399687237061823081646640 :=
  phaseBlock_append rec_5_15_2368_0_join3 rec_5_15_2368_0_join4 rfl rfl rfl
private theorem rec_5_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 0) 0 925 = 554294383796838863673501232 :=
  phaseBlock_append rec_5_15_2368_0_join2 rec_5_15_2368_0_join5 rfl rfl rfl

private theorem rec_5_15_2368_0 : fastPhase (bank 5 15).shape 179798 2368 105 1 4 1 0 = 554294383796838863673501232 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_5_15_2368_0_join6

private theorem rec_5_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 0 128 = 186313058403634924809204416 := by decide +kernel
private theorem rec_5_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 128 128 = 145861715144472045062943424 := by decide +kernel
private theorem rec_5_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 256 128 = 105186300452033429845652160 := by decide +kernel
private theorem rec_5_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 384 128 = 67326232296000979394032320 := by decide +kernel
private theorem rec_5_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 512 128 = 35270673347127837447992000 := by decide +kernel
private theorem rec_5_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 640 128 = 11958791393620738833806016 := by decide +kernel
private theorem rec_5_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 768 128 = 778565853740674716996884 := by decide +kernel
private theorem rec_5_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 896 29 = 0 := by decide +kernel
private theorem rec_5_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 0 256 = 332174773548106969872147840 :=
  phaseBlock_append rec_5_15_2368_1_part0 rec_5_15_2368_1_part1 rfl rfl rfl
private theorem rec_5_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 256 256 = 172512532748034409239684480 :=
  phaseBlock_append rec_5_15_2368_1_part2 rec_5_15_2368_1_part3 rfl rfl rfl
private theorem rec_5_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 0 512 = 504687306296141379111832320 :=
  phaseBlock_append rec_5_15_2368_1_join0 rec_5_15_2368_1_join1 rfl rfl rfl
private theorem rec_5_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 512 256 = 47229464740748576281798016 :=
  phaseBlock_append rec_5_15_2368_1_part4 rec_5_15_2368_1_part5 rfl rfl rfl
private theorem rec_5_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 768 157 = 778565853740674716996884 :=
  phaseBlock_append rec_5_15_2368_1_part6 rec_5_15_2368_1_part7 rfl rfl rfl
private theorem rec_5_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 512 413 = 48008030594489250998794900 :=
  phaseBlock_append rec_5_15_2368_1_join3 rec_5_15_2368_1_join4 rfl rfl rfl
private theorem rec_5_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2368 105 1 4 1 1) 0 925 = 552695336890630630110627220 :=
  phaseBlock_append rec_5_15_2368_1_join2 rec_5_15_2368_1_join5 rfl rfl rfl

private theorem rec_5_15_2368_1 : fastPhase (bank 5 15).shape 179798 2368 105 1 4 1 1 = 552695336890630630110627220 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_5_15_2368_1_join6

private theorem rec_5_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 0 128 = 186617999484021826493552160 := by decide +kernel
private theorem rec_5_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 128 128 = 146180874947718382446691872 := by decide +kernel
private theorem rec_5_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 256 128 = 105495795641799119571547680 := by decide +kernel
private theorem rec_5_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 384 128 = 67602520654572662757598752 := by decide +kernel
private theorem rec_5_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 512 128 = 35490552600935231215490592 := by decide +kernel
private theorem rec_5_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 640 128 = 12099398034310959083980320 := by decide +kernel
private theorem rec_5_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 768 128 = 809718417450987190938873 := by decide +kernel
private theorem rec_5_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 896 29 = 0 := by decide +kernel
private theorem rec_5_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 0 256 = 332798874431740208940244032 :=
  phaseBlock_append rec_5_15_2369_0_part0 rec_5_15_2369_0_part1 rfl rfl rfl
private theorem rec_5_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 256 256 = 173098316296371782329146432 :=
  phaseBlock_append rec_5_15_2369_0_part2 rec_5_15_2369_0_part3 rfl rfl rfl
private theorem rec_5_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 0 512 = 505897190728111991269390464 :=
  phaseBlock_append rec_5_15_2369_0_join0 rec_5_15_2369_0_join1 rfl rfl rfl
private theorem rec_5_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 512 256 = 47589950635246190299470912 :=
  phaseBlock_append rec_5_15_2369_0_part4 rec_5_15_2369_0_part5 rfl rfl rfl
private theorem rec_5_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 768 157 = 809718417450987190938873 :=
  phaseBlock_append rec_5_15_2369_0_part6 rec_5_15_2369_0_part7 rfl rfl rfl
private theorem rec_5_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 512 413 = 48399669052697177490409785 :=
  phaseBlock_append rec_5_15_2369_0_join3 rec_5_15_2369_0_join4 rfl rfl rfl
private theorem rec_5_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 0) 0 925 = 554296859780809168759800249 :=
  phaseBlock_append rec_5_15_2369_0_join2 rec_5_15_2369_0_join5 rfl rfl rfl

private theorem rec_5_15_2369_0 : fastPhase (bank 5 15).shape 179798 2369 105 1 4 1 0 = 554296859780809168759800249 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_5_15_2369_0_join6

private theorem rec_5_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 0 128 = 186314424298824576655879776 := by decide +kernel
private theorem rec_5_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 128 128 = 145862433604547671713357408 := by decide +kernel
private theorem rec_5_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 256 128 = 105186611398073268228607584 := by decide +kernel
private theorem rec_5_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 384 128 = 67326320980273452050087520 := by decide +kernel
private theorem rec_5_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 512 128 = 35270671221867194883092064 := by decide +kernel
private theorem rec_5_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 640 128 = 11958776975360674896698976 := by decide +kernel
private theorem rec_5_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 768 128 = 778564268051448038010675 := by decide +kernel
private theorem rec_5_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 896 29 = 0 := by decide +kernel
private theorem rec_5_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 0 256 = 332176857903372248369237184 :=
  phaseBlock_append rec_5_15_2369_1_part0 rec_5_15_2369_1_part1 rfl rfl rfl
private theorem rec_5_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 256 256 = 172512932378346720278695104 :=
  phaseBlock_append rec_5_15_2369_1_part2 rec_5_15_2369_1_part3 rfl rfl rfl
private theorem rec_5_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 0 512 = 504689790281718968647932288 :=
  phaseBlock_append rec_5_15_2369_1_join0 rec_5_15_2369_1_join1 rfl rfl rfl
private theorem rec_5_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 512 256 = 47229448197227869779791040 :=
  phaseBlock_append rec_5_15_2369_1_part4 rec_5_15_2369_1_part5 rfl rfl rfl
private theorem rec_5_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 768 157 = 778564268051448038010675 :=
  phaseBlock_append rec_5_15_2369_1_part6 rec_5_15_2369_1_part7 rfl rfl rfl
private theorem rec_5_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 512 413 = 48008012465279317817801715 :=
  phaseBlock_append rec_5_15_2369_1_join3 rec_5_15_2369_1_join4 rfl rfl rfl
private theorem rec_5_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 5 15).shape 179798 2369 105 1 4 1 1) 0 925 = 552697802746998286465734003 :=
  phaseBlock_append rec_5_15_2369_1_join2 rec_5_15_2369_1_join5 rfl rfl rfl

private theorem rec_5_15_2369_1 : fastPhase (bank 5 15).shape 179798 2369 105 1 4 1 1 = 552697802746998286465734003 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_5_15_2369_1_join6

theorem receipt_5_15 : Checked (bank 5 15) 105 4 1 := by
  refine checked_from_values (bank 5 15) 105 4 1
    (P3_7_1.checked (bank 5 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_15_2368_0 rec_5_15_2368_1 rec_5_15_2369_0 rec_5_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 0 128 = 568502940120807555853730720 := by decide +kernel
private theorem rec_5_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 128 128 = 446126312868980203428836256 := by decide +kernel
private theorem rec_5_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 256 128 = 322542073308034401304683424 := by decide +kernel
private theorem rec_5_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 384 128 = 207058670455830108619035552 := by decide +kernel
private theorem rec_5_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 512 128 = 108896556481418111512937376 := by decide +kernel
private theorem rec_5_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 640 128 = 37188447121422370713875360 := by decide +kernel
private theorem rec_5_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 768 128 = 2492207317717303477294649 := by decide +kernel
private theorem rec_5_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 896 29 = 0 := by decide +kernel
private theorem rec_5_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 0 256 = 1014629252989787759282566976 :=
  phaseBlock_append rec_5_16_2368_0_part0 rec_5_16_2368_0_part1 rfl rfl rfl
private theorem rec_5_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 256 256 = 529600743763864509923718976 :=
  phaseBlock_append rec_5_16_2368_0_part2 rec_5_16_2368_0_part3 rfl rfl rfl
private theorem rec_5_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 0 512 = 1544229996753652269206285952 :=
  phaseBlock_append rec_5_16_2368_0_join0 rec_5_16_2368_0_join1 rfl rfl rfl
private theorem rec_5_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 512 256 = 146085003602840482226812736 :=
  phaseBlock_append rec_5_16_2368_0_part4 rec_5_16_2368_0_part5 rfl rfl rfl
private theorem rec_5_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 768 157 = 2492207317717303477294649 :=
  phaseBlock_append rec_5_16_2368_0_part6 rec_5_16_2368_0_part7 rfl rfl rfl
private theorem rec_5_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 512 413 = 148577210920557785704107385 :=
  phaseBlock_append rec_5_16_2368_0_join3 rec_5_16_2368_0_join4 rfl rfl rfl
private theorem rec_5_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 0) 0 925 = 1692807207674210054910393337 :=
  phaseBlock_append rec_5_16_2368_0_join2 rec_5_16_2368_0_join5 rfl rfl rfl

private theorem rec_5_16_2368_0 : fastPhase (bank 5 16).shape 179798 2368 138 1 4 1 0 = 1692807207674210054910393337 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_5_16_2368_0_join6

private theorem rec_5_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 0 128 = 567586217190237520192088864 := by decide +kernel
private theorem rec_5_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 128 128 = 445160763083568372512701216 := by decide +kernel
private theorem rec_5_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 256 128 = 321601299208477744342190880 := by decide +kernel
private theorem rec_5_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 384 128 = 206215582357791268043414304 := by decide +kernel
private theorem rec_5_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 512 128 = 108223374518815687002188576 := by decide +kernel
private theorem rec_5_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 640 128 = 36756703289721203210451744 := by decide +kernel
private theorem rec_5_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 768 128 = 2396343139019401427135720 := by decide +kernel
private theorem rec_5_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 896 29 = 0 := by decide +kernel
private theorem rec_5_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 0 256 = 1012746980273805892704790080 :=
  phaseBlock_append rec_5_16_2368_1_part0 rec_5_16_2368_1_part1 rfl rfl rfl
private theorem rec_5_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 256 256 = 527816881566269012385605184 :=
  phaseBlock_append rec_5_16_2368_1_part2 rec_5_16_2368_1_part3 rfl rfl rfl
private theorem rec_5_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 0 512 = 1540563861840074905090395264 :=
  phaseBlock_append rec_5_16_2368_1_join0 rec_5_16_2368_1_join1 rfl rfl rfl
private theorem rec_5_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 512 256 = 144980077808536890212640320 :=
  phaseBlock_append rec_5_16_2368_1_part4 rec_5_16_2368_1_part5 rfl rfl rfl
private theorem rec_5_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 768 157 = 2396343139019401427135720 :=
  phaseBlock_append rec_5_16_2368_1_part6 rec_5_16_2368_1_part7 rfl rfl rfl
private theorem rec_5_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 512 413 = 147376420947556291639776040 :=
  phaseBlock_append rec_5_16_2368_1_join3 rec_5_16_2368_1_join4 rfl rfl rfl
private theorem rec_5_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2368 138 1 4 1 1) 0 925 = 1687940282787631196730171304 :=
  phaseBlock_append rec_5_16_2368_1_join2 rec_5_16_2368_1_join5 rfl rfl rfl

private theorem rec_5_16_2368_1 : fastPhase (bank 5 16).shape 179798 2368 138 1 4 1 1 = 1687940282787631196730171304 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_5_16_2368_1_join6

private theorem rec_5_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 0 128 = 568506970544586875398769760 := by decide +kernel
private theorem rec_5_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 128 128 = 446128411726556565861669984 := by decide +kernel
private theorem rec_5_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 256 128 = 322542961122274935827819616 := by decide +kernel
private theorem rec_5_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 384 128 = 207058904110783889721080928 := by decide +kernel
private theorem rec_5_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 512 128 = 108896530734733332558056544 := by decide +kernel
private theorem rec_5_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 640 128 = 37188396112321490555034720 := by decide +kernel
private theorem rec_5_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 768 128 = 2492201845262608507121526 := by decide +kernel
private theorem rec_5_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 896 29 = 0 := by decide +kernel
private theorem rec_5_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 0 256 = 1014635382271143441260439744 :=
  phaseBlock_append rec_5_16_2369_0_part0 rec_5_16_2369_0_part1 rfl rfl rfl
private theorem rec_5_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 256 256 = 529601865233058825548900544 :=
  phaseBlock_append rec_5_16_2369_0_part2 rec_5_16_2369_0_part3 rfl rfl rfl
private theorem rec_5_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 0 512 = 1544237247504202266809340288 :=
  phaseBlock_append rec_5_16_2369_0_join0 rec_5_16_2369_0_join1 rfl rfl rfl
private theorem rec_5_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 512 256 = 146084926847054823113091264 :=
  phaseBlock_append rec_5_16_2369_0_part4 rec_5_16_2369_0_part5 rfl rfl rfl
private theorem rec_5_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 768 157 = 2492201845262608507121526 :=
  phaseBlock_append rec_5_16_2369_0_part6 rec_5_16_2369_0_part7 rfl rfl rfl
private theorem rec_5_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 512 413 = 148577128692317431620212790 :=
  phaseBlock_append rec_5_16_2369_0_join3 rec_5_16_2369_0_join4 rfl rfl rfl
private theorem rec_5_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 0) 0 925 = 1692814376196519698429553078 :=
  phaseBlock_append rec_5_16_2369_0_join2 rec_5_16_2369_0_join5 rfl rfl rfl

private theorem rec_5_16_2369_0 : fastPhase (bank 5 16).shape 179798 2369 138 1 4 1 0 = 1692814376196519698429553078 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_5_16_2369_0_join6

private theorem rec_5_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 0 128 = 567590233756704182089943136 := by decide +kernel
private theorem rec_5_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 128 128 = 445162853046838755572127840 := by decide +kernel
private theorem rec_5_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 256 128 = 321602182034550098745108576 := by decide +kernel
private theorem rec_5_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 384 128 = 206215813884099225349994592 := by decide +kernel
private theorem rec_5_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 512 128 = 108223348466614441256306784 := by decide +kernel
private theorem rec_5_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 640 128 = 36756652772031665068922976 := by decide +kernel
private theorem rec_5_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 768 128 = 2396337875016928506680610 := by decide +kernel
private theorem rec_5_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 896 29 = 0 := by decide +kernel
private theorem rec_5_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 0 256 = 1012753086803542937662070976 :=
  phaseBlock_append rec_5_16_2369_1_part0 rec_5_16_2369_1_part1 rfl rfl rfl
private theorem rec_5_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 256 256 = 527817995918649324095103168 :=
  phaseBlock_append rec_5_16_2369_1_part2 rec_5_16_2369_1_part3 rfl rfl rfl
private theorem rec_5_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 0 512 = 1540571082722192261757174144 :=
  phaseBlock_append rec_5_16_2369_1_join0 rec_5_16_2369_1_join1 rfl rfl rfl
private theorem rec_5_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 512 256 = 144980001238646106325229760 :=
  phaseBlock_append rec_5_16_2369_1_part4 rec_5_16_2369_1_part5 rfl rfl rfl
private theorem rec_5_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 768 157 = 2396337875016928506680610 :=
  phaseBlock_append rec_5_16_2369_1_part6 rec_5_16_2369_1_part7 rfl rfl rfl
private theorem rec_5_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 512 413 = 147376339113663034831910370 :=
  phaseBlock_append rec_5_16_2369_1_join3 rec_5_16_2369_1_join4 rfl rfl rfl
private theorem rec_5_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 5 16).shape 179798 2369 138 1 4 1 1) 0 925 = 1687947421835855296589084514 :=
  phaseBlock_append rec_5_16_2369_1_join2 rec_5_16_2369_1_join5 rfl rfl rfl

private theorem rec_5_16_2369_1 : fastPhase (bank 5 16).shape 179798 2369 138 1 4 1 1 = 1687947421835855296589084514 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_5_16_2369_1_join6

theorem receipt_5_16 : Checked (bank 5 16) 138 4 1 := by
  refine checked_from_values (bank 5 16) 138 4 1
    (P3_7_1.checked (bank 5 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_16_2368_0 rec_5_16_2368_1 rec_5_16_2369_0 rec_5_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect5_checked (i : Fin 17) (hi : i ≠ 0) :
    Checked (bank 5 i) (reserve i) (excess 5) (seed 5) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact receipt_5_1
  · exact receipt_5_2
  · exact receipt_5_3
  · exact receipt_5_4
  · exact receipt_5_5
  · exact receipt_5_6
  · exact receipt_5_7
  · exact receipt_5_8
  · exact receipt_5_9
  · exact receipt_5_10
  · exact receipt_5_11
  · exact receipt_5_12
  · exact receipt_5_13
  · exact receipt_5_14
  · exact receipt_5_15
  · exact receipt_5_16

end Lower6961.Lo.RescueSource
