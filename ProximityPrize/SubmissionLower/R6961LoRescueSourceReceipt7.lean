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


private theorem rec_7_0_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2368 0 1 0 23 0) 0 128 = 15086578158384905595234 := by decide +kernel
private theorem rec_7_0_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2368 0 1 0 23 0) 128 63 = 753463843191544080084 := by decide +kernel
private theorem rec_7_0_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2368 0 1 0 23 0) 0 191 = 15840042001576449675318 :=
  phaseBlock_append rec_7_0_2368_0_part0 rec_7_0_2368_0_part1 rfl rfl rfl

private theorem rec_7_0_2368_0 : fastPhase (bank 7 0).shape 179798 2368 0 1 0 23 0 = 15840042001576449675318 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_7_0_2368_0_join0

private theorem rec_7_0_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2368 0 1 0 23 1) 0 128 = 14862183190683429653787 := by decide +kernel
private theorem rec_7_0_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2368 0 1 0 23 1) 128 63 = 724525301852219012922 := by decide +kernel
private theorem rec_7_0_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2368 0 1 0 23 1) 0 191 = 15586708492535648666709 :=
  phaseBlock_append rec_7_0_2368_1_part0 rec_7_0_2368_1_part1 rfl rfl rfl

private theorem rec_7_0_2368_1 : fastPhase (bank 7 0).shape 179798 2368 0 1 0 23 1 = 15586708492535648666709 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_7_0_2368_1_join0

private theorem rec_7_0_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2369 0 1 0 23 0) 0 128 = 15086702737633111749726 := by decide +kernel
private theorem rec_7_0_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2369 0 1 0 23 0) 128 63 = 753467579235603944079 := by decide +kernel
private theorem rec_7_0_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2369 0 1 0 23 0) 0 191 = 15840170316868715693805 :=
  phaseBlock_append rec_7_0_2369_0_part0 rec_7_0_2369_0_part1 rfl rfl rfl

private theorem rec_7_0_2369_0 : fastPhase (bank 7 0).shape 179798 2369 0 1 0 23 0 = 15840170316868715693805 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_7_0_2369_0_join0

private theorem rec_7_0_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2369 0 1 0 23 1) 0 128 = 14862306125736287015175 := by decide +kernel
private theorem rec_7_0_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2369 0 1 0 23 1) 128 63 = 724528908224462494935 := by decide +kernel
private theorem rec_7_0_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 0).shape 179798 2369 0 1 0 23 1) 0 191 = 15586835033960749510110 :=
  phaseBlock_append rec_7_0_2369_1_part0 rec_7_0_2369_1_part1 rfl rfl rfl

private theorem rec_7_0_2369_1 : fastPhase (bank 7 0).shape 179798 2369 0 1 0 23 1 = 15586835033960749510110 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_7_0_2369_1_join0

theorem receipt_7_0 : Checked (bank 7 0) 0 0 23 := by
  refine checked_from_values (bank 7 0) 0 0 23
    (P3_7_1.checked (bank 7 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_0_2368_0 rec_7_0_2368_1 rec_7_0_2369_0 rec_7_0_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2368 1 1 0 23 0) 0 128 = 43495290233151943879616 := by decide +kernel
private theorem rec_7_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2368 1 1 0 23 0) 128 128 = 5204125854264189927909 := by decide +kernel
private theorem rec_7_1_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2368 1 1 0 23 0) 256 22 = 20407492437846847663 := by decide +kernel
private theorem rec_7_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2368 1 1 0 23 0) 128 150 = 5224533346702036775572 :=
  phaseBlock_append rec_7_1_2368_0_part1 rec_7_1_2368_0_part2 rfl rfl rfl
private theorem rec_7_1_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2368 1 1 0 23 0) 0 278 = 48719823579853980655188 :=
  phaseBlock_append rec_7_1_2368_0_part0 rec_7_1_2368_0_join0 rfl rfl rfl

private theorem rec_7_1_2368_0 : fastPhase (bank 7 1).shape 179798 2368 1 1 0 23 0 = 48719823579853980655188 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_1_2368_0_join1

private theorem rec_7_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2368 1 1 0 23 1) 0 128 = 42955661855188602628160 := by decide +kernel
private theorem rec_7_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2368 1 1 0 23 1) 128 128 = 5087841297148360833297 := by decide +kernel
private theorem rec_7_1_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2368 1 1 0 23 1) 256 22 = 18260013020264061970 := by decide +kernel
private theorem rec_7_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2368 1 1 0 23 1) 128 150 = 5106101310168624895267 :=
  phaseBlock_append rec_7_1_2368_1_part1 rec_7_1_2368_1_part2 rfl rfl rfl
private theorem rec_7_1_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2368 1 1 0 23 1) 0 278 = 48061763165357227523427 :=
  phaseBlock_append rec_7_1_2368_1_part0 rec_7_1_2368_1_join0 rfl rfl rfl

private theorem rec_7_1_2368_1 : fastPhase (bank 7 1).shape 179798 2368 1 1 0 23 1 = 48061763165357227523427 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_1_2368_1_join1

private theorem rec_7_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2369 1 1 0 23 0) 0 128 = 43495663086746339890464 := by decide +kernel
private theorem rec_7_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2369 1 1 0 23 0) 128 128 = 5204157754152070311037 := by decide +kernel
private theorem rec_7_1_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2369 1 1 0 23 0) 256 22 = 20407567573965230120 := by decide +kernel
private theorem rec_7_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2369 1 1 0 23 0) 128 150 = 5224565321726035541157 :=
  phaseBlock_append rec_7_1_2369_0_part1 rec_7_1_2369_0_part2 rfl rfl rfl
private theorem rec_7_1_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2369 1 1 0 23 0) 0 278 = 48720228408472375431621 :=
  phaseBlock_append rec_7_1_2369_0_part0 rec_7_1_2369_0_join0 rfl rfl rfl

private theorem rec_7_1_2369_0 : fastPhase (bank 7 1).shape 179798 2369 1 1 0 23 0 = 48720228408472375431621 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_1_2369_0_join1

private theorem rec_7_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2369 1 1 0 23 1) 0 128 = 42956030471539248634080 := by decide +kernel
private theorem rec_7_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2369 1 1 0 23 1) 128 128 = 5087872539616033225572 := by decide +kernel
private theorem rec_7_1_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2369 1 1 0 23 1) 256 22 = 18260080484509183551 := by decide +kernel
private theorem rec_7_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2369 1 1 0 23 1) 128 150 = 5106132620100542409123 :=
  phaseBlock_append rec_7_1_2369_1_part1 rec_7_1_2369_1_part2 rfl rfl rfl
private theorem rec_7_1_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 1).shape 179798 2369 1 1 0 23 1) 0 278 = 48062163091639791043203 :=
  phaseBlock_append rec_7_1_2369_1_part0 rec_7_1_2369_1_join0 rfl rfl rfl

private theorem rec_7_1_2369_1 : fastPhase (bank 7 1).shape 179798 2369 1 1 0 23 1 = 48062163091639791043203 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_1_2369_1_join1

theorem receipt_7_1 : Checked (bank 7 1) 1 0 23 := by
  refine checked_from_values (bank 7 1) 1 0 23
    (P3_7_1.checked (bank 7 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_1_2368_0 rec_7_1_2368_1 rec_7_1_2369_0 rec_7_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2368 2 1 0 23 0) 0 128 = 51577964303238664296160 := by decide +kernel
private theorem rec_7_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2368 2 1 0 23 0) 128 128 = 6905849360527159175786 := by decide +kernel
private theorem rec_7_2_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2368 2 1 0 23 0) 256 22 = 37504631332440750555 := by decide +kernel
private theorem rec_7_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2368 2 1 0 23 0) 128 150 = 6943353991859599926341 :=
  phaseBlock_append rec_7_2_2368_0_part1 rec_7_2_2368_0_part2 rfl rfl rfl
private theorem rec_7_2_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2368 2 1 0 23 0) 0 278 = 58521318295098264222501 :=
  phaseBlock_append rec_7_2_2368_0_part0 rec_7_2_2368_0_join0 rfl rfl rfl

private theorem rec_7_2_2368_0 : fastPhase (bank 7 2).shape 179798 2368 2 1 0 23 0 = 58521318295098264222501 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_2_2368_0_join1

private theorem rec_7_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2368 2 1 0 23 1) 0 128 = 50966399237090306053536 := by decide +kernel
private theorem rec_7_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2368 2 1 0 23 1) 128 128 = 6760488977315328668354 := by decide +kernel
private theorem rec_7_2_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2368 2 1 0 23 1) 256 22 = 33733949296960185427 := by decide +kernel
private theorem rec_7_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2368 2 1 0 23 1) 128 150 = 6794222926612288853781 :=
  phaseBlock_append rec_7_2_2368_1_part1 rec_7_2_2368_1_part2 rfl rfl rfl
private theorem rec_7_2_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2368 2 1 0 23 1) 0 278 = 57760622163702594907317 :=
  phaseBlock_append rec_7_2_2368_1_part0 rec_7_2_2368_1_join0 rfl rfl rfl

private theorem rec_7_2_2368_1 : fastPhase (bank 7 2).shape 179798 2368 2 1 0 23 1 = 57760622163702594907317 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_2_2368_1_join1

private theorem rec_7_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2369 2 1 0 23 0) 0 128 = 51578404269488403148480 := by decide +kernel
private theorem rec_7_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2369 2 1 0 23 0) 128 128 = 6905891240019637848964 := by decide +kernel
private theorem rec_7_2_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2369 2 1 0 23 0) 256 22 = 37504768044236713990 := by decide +kernel
private theorem rec_7_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2369 2 1 0 23 0) 128 150 = 6943396008063874562954 :=
  phaseBlock_append rec_7_2_2369_0_part1 rec_7_2_2369_0_part2 rfl rfl rfl
private theorem rec_7_2_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2369 2 1 0 23 0) 0 278 = 58521800277552277711434 :=
  phaseBlock_append rec_7_2_2369_0_part0 rec_7_2_2369_0_join0 rfl rfl rfl

private theorem rec_7_2_2369_0 : fastPhase (bank 7 2).shape 179798 2369 2 1 0 23 0 = 58521800277552277711434 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_2_2369_0_join1

private theorem rec_7_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2369 2 1 0 23 1) 0 128 = 50966834442480025868928 := by decide +kernel
private theorem rec_7_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2369 2 1 0 23 1) 128 128 = 6760530048129228361486 := by decide +kernel
private theorem rec_7_2_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2369 2 1 0 23 1) 256 22 = 33734072709128182314 := by decide +kernel
private theorem rec_7_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2369 2 1 0 23 1) 128 150 = 6794264120838356543800 :=
  phaseBlock_append rec_7_2_2369_1_part1 rec_7_2_2369_1_part2 rfl rfl rfl
private theorem rec_7_2_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 2).shape 179798 2369 2 1 0 23 1) 0 278 = 57761098563318382412728 :=
  phaseBlock_append rec_7_2_2369_1_part0 rec_7_2_2369_1_join0 rfl rfl rfl

private theorem rec_7_2_2369_1 : fastPhase (bank 7 2).shape 179798 2369 2 1 0 23 1 = 57761098563318382412728 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_2_2369_1_join1

theorem receipt_7_2 : Checked (bank 7 2) 2 0 23 := by
  refine checked_from_values (bank 7 2) 2 0 23
    (P3_7_1.checked (bank 7 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_2_2368_0 rec_7_2_2368_1 rec_7_2_2369_0 rec_7_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2368 3 1 0 23 0) 0 128 = 64137532587098461337120 := by decide +kernel
private theorem rec_7_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2368 3 1 0 23 0) 128 128 = 9723058161494658338657 := by decide +kernel
private theorem rec_7_3_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2368 3 1 0 23 0) 256 22 = 70344942157530459013 := by decide +kernel
private theorem rec_7_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2368 3 1 0 23 0) 128 150 = 9793403103652188797670 :=
  phaseBlock_append rec_7_3_2368_0_part1 rec_7_3_2368_0_part2 rfl rfl rfl
private theorem rec_7_3_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2368 3 1 0 23 0) 0 278 = 73930935690750650134790 :=
  phaseBlock_append rec_7_3_2368_0_part0 rec_7_3_2368_0_join0 rfl rfl rfl

private theorem rec_7_3_2368_0 : fastPhase (bank 7 3).shape 179798 2368 3 1 0 23 0 = 73930935690750650134790 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_3_2368_0_join1

private theorem rec_7_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2368 3 1 0 23 1) 0 128 = 63418124175807898214240 := by decide +kernel
private theorem rec_7_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2368 3 1 0 23 1) 128 128 = 9531563908254623316338 := by decide +kernel
private theorem rec_7_3_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2368 3 1 0 23 1) 256 22 = 63521222091248425427 := by decide +kernel
private theorem rec_7_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2368 3 1 0 23 1) 128 150 = 9595085130345871741765 :=
  phaseBlock_append rec_7_3_2368_1_part1 rec_7_3_2368_1_part2 rfl rfl rfl
private theorem rec_7_3_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2368 3 1 0 23 1) 0 278 = 73013209306153769956005 :=
  phaseBlock_append rec_7_3_2368_1_part0 rec_7_3_2368_1_join0 rfl rfl rfl

private theorem rec_7_3_2368_1 : fastPhase (bank 7 3).shape 179798 2368 3 1 0 23 1 = 73013209306153769956005 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_3_2368_1_join1

private theorem rec_7_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2369 3 1 0 23 0) 0 128 = 64138076824703332878912 := by decide +kernel
private theorem rec_7_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2369 3 1 0 23 0) 128 128 = 9723116464309321094340 := by decide +kernel
private theorem rec_7_3_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2369 3 1 0 23 0) 256 22 = 70345196085957201486 := by decide +kernel
private theorem rec_7_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2369 3 1 0 23 0) 128 150 = 9793461660395278295826 :=
  phaseBlock_append rec_7_3_2369_0_part1 rec_7_3_2369_0_part2 rfl rfl rfl
private theorem rec_7_3_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2369 3 1 0 23 0) 0 278 = 73931538485098611174738 :=
  phaseBlock_append rec_7_3_2369_0_part0 rec_7_3_2369_0_join0 rfl rfl rfl

private theorem rec_7_3_2369_0 : fastPhase (bank 7 3).shape 179798 2369 3 1 0 23 0 = 73931538485098611174738 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_3_2369_0_join1

private theorem rec_7_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2369 3 1 0 23 1) 0 128 = 63418662869228089148160 := by decide +kernel
private theorem rec_7_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2369 3 1 0 23 1) 128 128 = 9531621164704544195986 := by decide +kernel
private theorem rec_7_3_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2369 3 1 0 23 1) 256 22 = 63521452244863570496 := by decide +kernel
private theorem rec_7_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2369 3 1 0 23 1) 128 150 = 9595142616949407766482 :=
  phaseBlock_append rec_7_3_2369_1_part1 rec_7_3_2369_1_part2 rfl rfl rfl
private theorem rec_7_3_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 3).shape 179798 2369 3 1 0 23 1) 0 278 = 73013805486177496914642 :=
  phaseBlock_append rec_7_3_2369_1_part0 rec_7_3_2369_1_join0 rfl rfl rfl

private theorem rec_7_3_2369_1 : fastPhase (bank 7 3).shape 179798 2369 3 1 0 23 1 = 73013805486177496914642 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_3_2369_1_join1

theorem receipt_7_3 : Checked (bank 7 3) 3 0 23 := by
  refine checked_from_values (bank 7 3) 3 0 23
    (P3_7_1.checked (bank 7 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_3_2368_0 rec_7_3_2368_1 rec_7_3_2369_0 rec_7_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2368 4 1 0 23 0) 0 128 = 88046941237869216281568 := by decide +kernel
private theorem rec_7_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2368 4 1 0 23 0) 128 128 = 15490461366096477844787 := by decide +kernel
private theorem rec_7_4_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2368 4 1 0 23 0) 256 22 = 147528971205925696969 := by decide +kernel
private theorem rec_7_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2368 4 1 0 23 0) 128 150 = 15637990337302403541756 :=
  phaseBlock_append rec_7_4_2368_0_part1 rec_7_4_2368_0_part2 rfl rfl rfl
private theorem rec_7_4_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2368 4 1 0 23 0) 0 278 = 103684931575171619823324 :=
  phaseBlock_append rec_7_4_2368_0_part0 rec_7_4_2368_0_join0 rfl rfl rfl

private theorem rec_7_4_2368_0 : fastPhase (bank 7 4).shape 179798 2368 4 1 0 23 0 = 103684931575171619823324 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_4_2368_0_join1

private theorem rec_7_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2368 4 1 0 23 1) 0 128 = 87131443675503679315104 := by decide +kernel
private theorem rec_7_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2368 4 1 0 23 1) 128 128 = 15208913373889442728529 := by decide +kernel
private theorem rec_7_4_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2368 4 1 0 23 1) 256 22 = 133652331022468207307 := by decide +kernel
private theorem rec_7_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2368 4 1 0 23 1) 128 150 = 15342565704911910935836 :=
  phaseBlock_append rec_7_4_2368_1_part1 rec_7_4_2368_1_part2 rfl rfl rfl
private theorem rec_7_4_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2368 4 1 0 23 1) 0 278 = 102474009380415590250940 :=
  phaseBlock_append rec_7_4_2368_1_part0 rec_7_4_2368_1_join0 rfl rfl rfl

private theorem rec_7_4_2368_1 : fastPhase (bank 7 4).shape 179798 2368 4 1 0 23 1 = 102474009380415590250940 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_4_2368_1_join1

private theorem rec_7_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2369 4 1 0 23 0) 0 128 = 88047684000284068827584 := by decide +kernel
private theorem rec_7_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2369 4 1 0 23 0) 128 128 = 15490553108252764130132 := by decide +kernel
private theorem rec_7_4_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2369 4 1 0 23 0) 256 22 = 147529498604353557960 := by decide +kernel
private theorem rec_7_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2369 4 1 0 23 0) 128 150 = 15638082606857117688092 :=
  phaseBlock_append rec_7_4_2369_0_part1 rec_7_4_2369_0_part2 rfl rfl rfl
private theorem rec_7_4_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2369 4 1 0 23 0) 0 278 = 103685766607141186515676 :=
  phaseBlock_append rec_7_4_2369_0_part0 rec_7_4_2369_0_join0 rfl rfl rfl

private theorem rec_7_4_2369_0 : fastPhase (bank 7 4).shape 179798 2369 4 1 0 23 0 = 103685766607141186515676 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_4_2369_0_join1

private theorem rec_7_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2369 4 1 0 23 1) 0 128 = 87132179474017057567872 := by decide +kernel
private theorem rec_7_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2369 4 1 0 23 1) 128 128 = 15209003610468900240394 := by decide +kernel
private theorem rec_7_4_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2369 4 1 0 23 1) 256 22 = 133652810655675990602 := by decide +kernel
private theorem rec_7_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2369 4 1 0 23 1) 128 150 = 15342656421124576230996 :=
  phaseBlock_append rec_7_4_2369_1_part1 rec_7_4_2369_1_part2 rfl rfl rfl
private theorem rec_7_4_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 4).shape 179798 2369 4 1 0 23 1) 0 278 = 102474835895141633798868 :=
  phaseBlock_append rec_7_4_2369_1_part0 rec_7_4_2369_1_join0 rfl rfl rfl

private theorem rec_7_4_2369_1 : fastPhase (bank 7 4).shape 179798 2369 4 1 0 23 1 = 102474835895141633798868 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_7_4_2369_1_join1

theorem receipt_7_4 : Checked (bank 7 4) 4 0 23 := by
  refine checked_from_values (bank 7 4) 4 0 23
    (P3_7_1.checked (bank 7 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_4_2368_0 rec_7_4_2368_1 rec_7_4_2369_0 rec_7_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2368 5 1 0 23 0) 0 128 = 224158831899510228001440 := by decide +kernel
private theorem rec_7_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2368 5 1 0 23 0) 128 128 = 55890598832176695029211 := by decide +kernel
private theorem rec_7_5_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2368 5 1 0 23 0) 256 114 = 5179133888239875298455 := by decide +kernel
private theorem rec_7_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2368 5 1 0 23 0) 128 242 = 61069732720416570327666 :=
  phaseBlock_append rec_7_5_2368_0_part1 rec_7_5_2368_0_part2 rfl rfl rfl
private theorem rec_7_5_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2368 5 1 0 23 0) 0 370 = 285228564619926798329106 :=
  phaseBlock_append rec_7_5_2368_0_part0 rec_7_5_2368_0_join0 rfl rfl rfl

private theorem rec_7_5_2368_0 : fastPhase (bank 7 5).shape 179798 2368 5 1 0 23 0 = 285228564619926798329106 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_5_2368_0_join1

private theorem rec_7_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2368 5 1 0 23 1) 0 128 = 222166856169582073797408 := by decide +kernel
private theorem rec_7_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2368 5 1 0 23 1) 128 128 = 55151113388879143822535 := by decide +kernel
private theorem rec_7_5_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2368 5 1 0 23 1) 256 114 = 5042175843061145087515 := by decide +kernel
private theorem rec_7_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2368 5 1 0 23 1) 128 242 = 60193289231940288910050 :=
  phaseBlock_append rec_7_5_2368_1_part1 rec_7_5_2368_1_part2 rfl rfl rfl
private theorem rec_7_5_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2368 5 1 0 23 1) 0 370 = 282360145401522362707458 :=
  phaseBlock_append rec_7_5_2368_1_part0 rec_7_5_2368_1_join0 rfl rfl rfl

private theorem rec_7_5_2368_1 : fastPhase (bank 7 5).shape 179798 2368 5 1 0 23 1 = 282360145401522362707458 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_5_2368_1_join1

private theorem rec_7_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2369 5 1 0 23 0) 0 128 = 224160775607333368126080 := by decide +kernel
private theorem rec_7_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2369 5 1 0 23 0) 128 128 = 55890977286343329534009 := by decide +kernel
private theorem rec_7_5_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2369 5 1 0 23 0) 256 114 = 5179158875749706901795 := by decide +kernel
private theorem rec_7_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2369 5 1 0 23 0) 128 242 = 61070136162093036435804 :=
  phaseBlock_append rec_7_5_2369_0_part1 rec_7_5_2369_0_part2 rfl rfl rfl
private theorem rec_7_5_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2369 5 1 0 23 0) 0 370 = 285230911769426404561884 :=
  phaseBlock_append rec_7_5_2369_0_part0 rec_7_5_2369_0_join0 rfl rfl rfl

private theorem rec_7_5_2369_0 : fastPhase (bank 7 5).shape 179798 2369 5 1 0 23 0 = 285230911769426404561884 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_5_2369_0_join1

private theorem rec_7_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2369 5 1 0 23 1) 0 128 = 222168784027046085323520 := by decide +kernel
private theorem rec_7_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2369 5 1 0 23 1) 128 128 = 55151487197879696467434 := by decide +kernel
private theorem rec_7_5_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2369 5 1 0 23 1) 256 114 = 5042200214655424206453 := by decide +kernel
private theorem rec_7_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2369 5 1 0 23 1) 128 242 = 60193687412535120673887 :=
  phaseBlock_append rec_7_5_2369_1_part1 rec_7_5_2369_1_part2 rfl rfl rfl
private theorem rec_7_5_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 5).shape 179798 2369 5 1 0 23 1) 0 370 = 282362471439581205997407 :=
  phaseBlock_append rec_7_5_2369_1_part0 rec_7_5_2369_1_join0 rfl rfl rfl

private theorem rec_7_5_2369_1 : fastPhase (bank 7 5).shape 179798 2369 5 1 0 23 1 = 282362471439581205997407 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_5_2369_1_join1

theorem receipt_7_5 : Checked (bank 7 5) 5 0 23 := by
  refine checked_from_values (bank 7 5) 5 0 23
    (P3_7_1.checked (bank 7 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_5_2368_0 rec_7_5_2368_1 rec_7_5_2369_0 rec_7_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2368 7 1 0 23 0) 0 128 = 295350738907598109524256 := by decide +kernel
private theorem rec_7_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2368 7 1 0 23 0) 128 128 = 82457307120639575223974 := by decide +kernel
private theorem rec_7_6_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2368 7 1 0 23 0) 256 114 = 9585046744925596109825 := by decide +kernel
private theorem rec_7_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2368 7 1 0 23 0) 128 242 = 92042353865565171333799 :=
  phaseBlock_append rec_7_6_2368_0_part1 rec_7_6_2368_0_part2 rfl rfl rfl
private theorem rec_7_6_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2368 7 1 0 23 0) 0 370 = 387393092773163280858055 :=
  phaseBlock_append rec_7_6_2368_0_part0 rec_7_6_2368_0_join0 rfl rfl rfl

private theorem rec_7_6_2368_0 : fastPhase (bank 7 6).shape 179798 2368 7 1 0 23 0 = 387393092773163280858055 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_6_2368_0_join1

private theorem rec_7_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2368 7 1 0 23 1) 0 128 = 292912291018206902288544 := by decide +kernel
private theorem rec_7_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2368 7 1 0 23 1) 128 128 = 81465988955100114335481 := by decide +kernel
private theorem rec_7_6_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2368 7 1 0 23 1) 256 114 = 9353821057521812730930 := by decide +kernel
private theorem rec_7_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2368 7 1 0 23 1) 128 242 = 90819810012621927066411 :=
  phaseBlock_append rec_7_6_2368_1_part1 rec_7_6_2368_1_part2 rfl rfl rfl
private theorem rec_7_6_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2368 7 1 0 23 1) 0 370 = 383732101030828829354955 :=
  phaseBlock_append rec_7_6_2368_1_part0 rec_7_6_2368_1_join0 rfl rfl rfl

private theorem rec_7_6_2368_1 : fastPhase (bank 7 6).shape 179798 2368 7 1 0 23 1 = 383732101030828829354955 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_6_2368_1_join1

private theorem rec_7_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2369 7 1 0 23 0) 0 128 = 295353284024159203304832 := by decide +kernel
private theorem rec_7_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2369 7 1 0 23 0) 128 128 = 82457859639552539004271 := by decide +kernel
private theorem rec_7_6_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2369 7 1 0 23 0) 256 114 = 9585092170203039267664 := by decide +kernel
private theorem rec_7_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2369 7 1 0 23 0) 128 242 = 92042951809755578271935 :=
  phaseBlock_append rec_7_6_2369_0_part1 rec_7_6_2369_0_part2 rfl rfl rfl
private theorem rec_7_6_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2369 7 1 0 23 0) 0 370 = 387396235833914781576767 :=
  phaseBlock_append rec_7_6_2369_0_part0 rec_7_6_2369_0_join0 rfl rfl rfl

private theorem rec_7_6_2369_0 : fastPhase (bank 7 6).shape 179798 2369 7 1 0 23 0 = 387396235833914781576767 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_6_2369_0_join1

private theorem rec_7_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2369 7 1 0 23 1) 0 128 = 292914816976033038748416 := by decide +kernel
private theorem rec_7_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2369 7 1 0 23 1) 128 128 = 81466535352960820808313 := by decide +kernel
private theorem rec_7_6_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2369 7 1 0 23 1) 256 114 = 9353865473323832369238 := by decide +kernel
private theorem rec_7_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2369 7 1 0 23 1) 128 242 = 90820400826284653177551 :=
  phaseBlock_append rec_7_6_2369_1_part1 rec_7_6_2369_1_part2 rfl rfl rfl
private theorem rec_7_6_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 6).shape 179798 2369 7 1 0 23 1) 0 370 = 383735217802317691925967 :=
  phaseBlock_append rec_7_6_2369_1_part0 rec_7_6_2369_1_join0 rfl rfl rfl

private theorem rec_7_6_2369_1 : fastPhase (bank 7 6).shape 179798 2369 7 1 0 23 1 = 383735217802317691925967 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_6_2369_1_join1

theorem receipt_7_6 : Checked (bank 7 6) 7 0 23 := by
  refine checked_from_values (bank 7 6) 7 0 23
    (P3_7_1.checked (bank 7 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_6_2368_0 rec_7_6_2368_1 rec_7_6_2369_0 rec_7_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2368 10 1 0 23 0) 0 128 = 929024282225138488905920 := by decide +kernel
private theorem rec_7_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2368 10 1 0 23 0) 128 128 = 351168155990777966144551 := by decide +kernel
private theorem rec_7_7_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2368 10 1 0 23 0) 256 114 = 64763481323290153444909 := by decide +kernel
private theorem rec_7_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2368 10 1 0 23 0) 128 242 = 415931637314068119589460 :=
  phaseBlock_append rec_7_7_2368_0_part1 rec_7_7_2368_0_part2 rfl rfl rfl
private theorem rec_7_7_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2368 10 1 0 23 0) 0 370 = 1344955919539206608495380 :=
  phaseBlock_append rec_7_7_2368_0_part0 rec_7_7_2368_0_join0 rfl rfl rfl

private theorem rec_7_7_2368_0 : fastPhase (bank 7 7).shape 179798 2368 10 1 0 23 0 = 1344955919539206608495380 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_7_2368_0_join1

private theorem rec_7_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2368 10 1 0 23 1) 0 128 = 923091016576478366547456 := by decide +kernel
private theorem rec_7_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2368 10 1 0 23 1) 128 128 = 347978061712202944728899 := by decide +kernel
private theorem rec_7_7_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2368 10 1 0 23 1) 256 114 = 63453090464014971536992 := by decide +kernel
private theorem rec_7_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2368 10 1 0 23 1) 128 242 = 411431152176217916265891 :=
  phaseBlock_append rec_7_7_2368_1_part1 rec_7_7_2368_1_part2 rfl rfl rfl
private theorem rec_7_7_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2368 10 1 0 23 1) 0 370 = 1334522168752696282813347 :=
  phaseBlock_append rec_7_7_2368_1_part0 rec_7_7_2368_1_join0 rfl rfl rfl

private theorem rec_7_7_2368_1 : fastPhase (bank 7 7).shape 179798 2368 10 1 0 23 1 = 1334522168752696282813347 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_7_2368_1_join1

private theorem rec_7_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2369 10 1 0 23 0) 0 128 = 929032195470444335452160 := by decide +kernel
private theorem rec_7_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2369 10 1 0 23 0) 128 128 = 351170462694061842810422 := by decide +kernel
private theorem rec_7_7_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2369 10 1 0 23 0) 256 114 = 64763779129405375786468 := by decide +kernel
private theorem rec_7_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2369 10 1 0 23 0) 128 242 = 415934241823467218596890 :=
  phaseBlock_append rec_7_7_2369_0_part1 rec_7_7_2369_0_part2 rfl rfl rfl
private theorem rec_7_7_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2369 10 1 0 23 0) 0 370 = 1344966437293911554049050 :=
  phaseBlock_append rec_7_7_2369_0_part0 rec_7_7_2369_0_join0 rfl rfl rfl

private theorem rec_7_7_2369_0 : fastPhase (bank 7 7).shape 179798 2369 10 1 0 23 0 = 1344966437293911554049050 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_7_2369_0_join1

private theorem rec_7_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2369 10 1 0 23 1) 0 128 = 923098884987144167119680 := by decide +kernel
private theorem rec_7_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2369 10 1 0 23 1) 128 128 = 347980349593122695824684 := by decide +kernel
private theorem rec_7_7_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2369 10 1 0 23 1) 256 114 = 63453382885112313470040 := by decide +kernel
private theorem rec_7_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2369 10 1 0 23 1) 128 242 = 411433732478235009294724 :=
  phaseBlock_append rec_7_7_2369_1_part1 rec_7_7_2369_1_part2 rfl rfl rfl
private theorem rec_7_7_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 7).shape 179798 2369 10 1 0 23 1) 0 370 = 1334532617465379176414404 :=
  phaseBlock_append rec_7_7_2369_1_part0 rec_7_7_2369_1_join0 rfl rfl rfl

private theorem rec_7_7_2369_1 : fastPhase (bank 7 7).shape 179798 2369 10 1 0 23 1 = 1334532617465379176414404 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_7_2369_1_join1

theorem receipt_7_7 : Checked (bank 7 7) 10 0 23 := by
  refine checked_from_values (bank 7 7) 10 0 23
    (P3_7_1.checked (bank 7 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_7_2368_0 rec_7_7_2368_1 rec_7_7_2369_0 rec_7_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 0) 0 128 = 2587207651529009983006464 := by decide +kernel
private theorem rec_7_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 0) 128 128 = 1222671554807644872541952 := by decide +kernel
private theorem rec_7_8_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 0) 256 128 = 447580427295845134664023 := by decide +kernel
private theorem rec_7_8_2368_0_part3 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 0) 384 109 = 75554769503328256058640 := by decide +kernel
private theorem rec_7_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 0) 0 256 = 3809879206336654855548416 :=
  phaseBlock_append rec_7_8_2368_0_part0 rec_7_8_2368_0_part1 rfl rfl rfl
private theorem rec_7_8_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 0) 256 237 = 523135196799173390722663 :=
  phaseBlock_append rec_7_8_2368_0_part2 rec_7_8_2368_0_part3 rfl rfl rfl
private theorem rec_7_8_2368_0_join2 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 0) 0 493 = 4333014403135828246271079 :=
  phaseBlock_append rec_7_8_2368_0_join0 rec_7_8_2368_0_join1 rfl rfl rfl

private theorem rec_7_8_2368_0 : fastPhase (bank 7 8).shape 179798 2368 16 1 0 23 0 = 4333014403135828246271079 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_7_8_2368_0_join2

private theorem rec_7_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 1) 0 128 = 2573803316610150447103936 := by decide +kernel
private theorem rec_7_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 1) 128 128 = 1214647066643572772061120 := by decide +kernel
private theorem rec_7_8_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 1) 256 128 = 443345092897060147187948 := by decide +kernel
private theorem rec_7_8_2368_1_part3 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 1) 384 109 = 73945549539290058415280 := by decide +kernel
private theorem rec_7_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 1) 0 256 = 3788450383253723219165056 :=
  phaseBlock_append rec_7_8_2368_1_part0 rec_7_8_2368_1_part1 rfl rfl rfl
private theorem rec_7_8_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 1) 256 237 = 517290642436350205603228 :=
  phaseBlock_append rec_7_8_2368_1_part2 rec_7_8_2368_1_part3 rfl rfl rfl
private theorem rec_7_8_2368_1_join2 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2368 16 1 0 23 1) 0 493 = 4305741025690073424768284 :=
  phaseBlock_append rec_7_8_2368_1_join0 rec_7_8_2368_1_join1 rfl rfl rfl

private theorem rec_7_8_2368_1 : fastPhase (bank 7 8).shape 179798 2368 16 1 0 23 1 = 4305741025690073424768284 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_7_8_2368_1_join2

private theorem rec_7_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 0) 0 128 = 2587230057843155930931648 := by decide +kernel
private theorem rec_7_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 0) 128 128 = 1222680378501075981566400 := by decide +kernel
private theorem rec_7_8_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 0) 256 128 = 447582958256587870769895 := by decide +kernel
private theorem rec_7_8_2369_0_part3 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 0) 384 109 = 75555082257421422548361 := by decide +kernel
private theorem rec_7_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 0) 0 256 = 3809910436344231912498048 :=
  phaseBlock_append rec_7_8_2369_0_part0 rec_7_8_2369_0_part1 rfl rfl rfl
private theorem rec_7_8_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 0) 256 237 = 523138040514009293318256 :=
  phaseBlock_append rec_7_8_2369_0_part2 rec_7_8_2369_0_part3 rfl rfl rfl
private theorem rec_7_8_2369_0_join2 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 0) 0 493 = 4333048476858241205816304 :=
  phaseBlock_append rec_7_8_2369_0_join0 rec_7_8_2369_0_join1 rfl rfl rfl

private theorem rec_7_8_2369_0 : fastPhase (bank 7 8).shape 179798 2369 16 1 0 23 0 = 4333048476858241205816304 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_7_8_2369_0_join2

private theorem rec_7_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 1) 0 128 = 2573825618617107714437824 := by decide +kernel
private theorem rec_7_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 1) 128 128 = 1214655837761302600954560 := by decide +kernel
private theorem rec_7_8_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 1) 256 128 = 443347601884488565988871 := by decide +kernel
private theorem rec_7_8_2369_1_part3 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 1) 384 109 = 73945856186311485394459 := by decide +kernel
private theorem rec_7_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 1) 0 256 = 3788481456378410315392384 :=
  phaseBlock_append rec_7_8_2369_1_part0 rec_7_8_2369_1_part1 rfl rfl rfl
private theorem rec_7_8_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 1) 256 237 = 517293458070800051383330 :=
  phaseBlock_append rec_7_8_2369_1_part2 rec_7_8_2369_1_part3 rfl rfl rfl
private theorem rec_7_8_2369_1_join2 :
    phaseBlock (fastLayerG (bank 7 8).shape 179798 2369 16 1 0 23 1) 0 493 = 4305774914449210366775714 :=
  phaseBlock_append rec_7_8_2369_1_join0 rec_7_8_2369_1_join1 rfl rfl rfl

private theorem rec_7_8_2369_1 : fastPhase (bank 7 8).shape 179798 2369 16 1 0 23 1 = 4305774914449210366775714 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_7_8_2369_1_join2

theorem receipt_7_8 : Checked (bank 7 8) 16 0 23 := by
  refine checked_from_values (bank 7 8) 16 0 23
    (P3_7_1.checked (bank 7 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_8_2368_0 rec_7_8_2368_1 rec_7_8_2369_0 rec_7_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2368 10 1 0 23 0) 0 128 = 929024282225138488905920 := by decide +kernel
private theorem rec_7_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2368 10 1 0 23 0) 128 128 = 351168155990777966144551 := by decide +kernel
private theorem rec_7_9_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2368 10 1 0 23 0) 256 114 = 64763481323290153444909 := by decide +kernel
private theorem rec_7_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2368 10 1 0 23 0) 128 242 = 415931637314068119589460 :=
  phaseBlock_append rec_7_9_2368_0_part1 rec_7_9_2368_0_part2 rfl rfl rfl
private theorem rec_7_9_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2368 10 1 0 23 0) 0 370 = 1344955919539206608495380 :=
  phaseBlock_append rec_7_9_2368_0_part0 rec_7_9_2368_0_join0 rfl rfl rfl

private theorem rec_7_9_2368_0 : fastPhase (bank 7 9).shape 179798 2368 10 1 0 23 0 = 1344955919539206608495380 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_9_2368_0_join1

private theorem rec_7_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2368 10 1 0 23 1) 0 128 = 923091016576478366547456 := by decide +kernel
private theorem rec_7_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2368 10 1 0 23 1) 128 128 = 347978061712202944728899 := by decide +kernel
private theorem rec_7_9_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2368 10 1 0 23 1) 256 114 = 63453090464014971536992 := by decide +kernel
private theorem rec_7_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2368 10 1 0 23 1) 128 242 = 411431152176217916265891 :=
  phaseBlock_append rec_7_9_2368_1_part1 rec_7_9_2368_1_part2 rfl rfl rfl
private theorem rec_7_9_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2368 10 1 0 23 1) 0 370 = 1334522168752696282813347 :=
  phaseBlock_append rec_7_9_2368_1_part0 rec_7_9_2368_1_join0 rfl rfl rfl

private theorem rec_7_9_2368_1 : fastPhase (bank 7 9).shape 179798 2368 10 1 0 23 1 = 1334522168752696282813347 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_9_2368_1_join1

private theorem rec_7_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2369 10 1 0 23 0) 0 128 = 929032195470444335452160 := by decide +kernel
private theorem rec_7_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2369 10 1 0 23 0) 128 128 = 351170462694061842810422 := by decide +kernel
private theorem rec_7_9_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2369 10 1 0 23 0) 256 114 = 64763779129405375786468 := by decide +kernel
private theorem rec_7_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2369 10 1 0 23 0) 128 242 = 415934241823467218596890 :=
  phaseBlock_append rec_7_9_2369_0_part1 rec_7_9_2369_0_part2 rfl rfl rfl
private theorem rec_7_9_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2369 10 1 0 23 0) 0 370 = 1344966437293911554049050 :=
  phaseBlock_append rec_7_9_2369_0_part0 rec_7_9_2369_0_join0 rfl rfl rfl

private theorem rec_7_9_2369_0 : fastPhase (bank 7 9).shape 179798 2369 10 1 0 23 0 = 1344966437293911554049050 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_9_2369_0_join1

private theorem rec_7_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2369 10 1 0 23 1) 0 128 = 923098884987144167119680 := by decide +kernel
private theorem rec_7_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2369 10 1 0 23 1) 128 128 = 347980349593122695824684 := by decide +kernel
private theorem rec_7_9_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2369 10 1 0 23 1) 256 114 = 63453382885112313470040 := by decide +kernel
private theorem rec_7_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2369 10 1 0 23 1) 128 242 = 411433732478235009294724 :=
  phaseBlock_append rec_7_9_2369_1_part1 rec_7_9_2369_1_part2 rfl rfl rfl
private theorem rec_7_9_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 9).shape 179798 2369 10 1 0 23 1) 0 370 = 1334532617465379176414404 :=
  phaseBlock_append rec_7_9_2369_1_part0 rec_7_9_2369_1_join0 rfl rfl rfl

private theorem rec_7_9_2369_1 : fastPhase (bank 7 9).shape 179798 2369 10 1 0 23 1 = 1334532617465379176414404 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_7_9_2369_1_join1

theorem receipt_7_9 : Checked (bank 7 9) 10 0 23 := by
  refine checked_from_values (bank 7 9) 10 0 23
    (P3_7_1.checked (bank 7 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_9_2368_0 rec_7_9_2368_1 rec_7_9_2369_0 rec_7_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 0 128 = 6760402764967482872002176 := by decide +kernel
private theorem rec_7_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 128 128 = 3639565615502793288521344 := by decide +kernel
private theorem rec_7_10_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 256 128 = 1707324090647979641294312 := by decide +kernel
private theorem rec_7_10_2368_0_part3 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 384 128 = 635692761169405815704261 := by decide +kernel
private theorem rec_7_10_2368_0_part4 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 512 128 = 143932064821777705868018 := by decide +kernel
private theorem rec_7_10_2368_0_part5 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 640 38 = 4051261368422673778659 := by decide +kernel
private theorem rec_7_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 128 256 = 5346889706150772929815656 :=
  phaseBlock_append rec_7_10_2368_0_part1 rec_7_10_2368_0_part2 rfl rfl rfl
private theorem rec_7_10_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 0 384 = 12107292471118255801817832 :=
  phaseBlock_append rec_7_10_2368_0_part0 rec_7_10_2368_0_join0 rfl rfl rfl
private theorem rec_7_10_2368_0_join2 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 512 166 = 147983326190200379646677 :=
  phaseBlock_append rec_7_10_2368_0_part4 rec_7_10_2368_0_part5 rfl rfl rfl
private theorem rec_7_10_2368_0_join3 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 384 294 = 783676087359606195350938 :=
  phaseBlock_append rec_7_10_2368_0_part3 rec_7_10_2368_0_join2 rfl rfl rfl
private theorem rec_7_10_2368_0_join4 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 0) 0 678 = 12890968558477861997168770 :=
  phaseBlock_append rec_7_10_2368_0_join1 rec_7_10_2368_0_join3 rfl rfl rfl

private theorem rec_7_10_2368_0 : fastPhase (bank 7 10).shape 179798 2368 20 1 0 23 0 = 12890968558477861997168770 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_7_10_2368_0_join4

private theorem rec_7_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 0 128 = 6730656088744587019117568 := by decide +kernel
private theorem rec_7_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 128 128 = 3620422885565332879770624 := by decide +kernel
private theorem rec_7_10_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 256 128 = 1696060285320659894152934 := by decide +kernel
private theorem rec_7_10_2368_1_part3 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 384 128 = 629957937934997901476100 := by decide +kernel
private theorem rec_7_10_2368_1_part4 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 512 128 = 141725933015330069669573 := by decide +kernel
private theorem rec_7_10_2368_1_part5 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 640 38 = 3820609634848437343559 := by decide +kernel
private theorem rec_7_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 128 256 = 5316483170885992773923558 :=
  phaseBlock_append rec_7_10_2368_1_part1 rec_7_10_2368_1_part2 rfl rfl rfl
private theorem rec_7_10_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 0 384 = 12047139259630579793041126 :=
  phaseBlock_append rec_7_10_2368_1_part0 rec_7_10_2368_1_join0 rfl rfl rfl
private theorem rec_7_10_2368_1_join2 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 512 166 = 145546542650178507013132 :=
  phaseBlock_append rec_7_10_2368_1_part4 rec_7_10_2368_1_part5 rfl rfl rfl
private theorem rec_7_10_2368_1_join3 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 384 294 = 775504480585176408489232 :=
  phaseBlock_append rec_7_10_2368_1_part3 rec_7_10_2368_1_join2 rfl rfl rfl
private theorem rec_7_10_2368_1_join4 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2368 20 1 0 23 1) 0 678 = 12822643740215756201530358 :=
  phaseBlock_append rec_7_10_2368_1_join1 rec_7_10_2368_1_join3 rfl rfl rfl

private theorem rec_7_10_2368_1 : fastPhase (bank 7 10).shape 179798 2368 20 1 0 23 1 = 12822643740215756201530358 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_7_10_2368_1_join4

private theorem rec_7_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 0 128 = 6760462591811199184377984 := by decide +kernel
private theorem rec_7_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 128 128 = 3639594065040800735336576 := by decide +kernel
private theorem rec_7_10_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 256 128 = 1707335566687262356920783 := by decide +kernel
private theorem rec_7_10_2369_0_part3 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 384 128 = 635696290757201205167249 := by decide +kernel
private theorem rec_7_10_2369_0_part4 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 512 128 = 143932692235701692219233 := by decide +kernel
private theorem rec_7_10_2369_0_part5 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 640 38 = 4051274909564300303508 := by decide +kernel
private theorem rec_7_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 128 256 = 5346929631728063092257359 :=
  phaseBlock_append rec_7_10_2369_0_part1 rec_7_10_2369_0_part2 rfl rfl rfl
private theorem rec_7_10_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 0 384 = 12107392223539262276635343 :=
  phaseBlock_append rec_7_10_2369_0_part0 rec_7_10_2369_0_join0 rfl rfl rfl
private theorem rec_7_10_2369_0_join2 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 512 166 = 147983967145265992522741 :=
  phaseBlock_append rec_7_10_2369_0_part4 rec_7_10_2369_0_part5 rfl rfl rfl
private theorem rec_7_10_2369_0_join3 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 384 294 = 783680257902467197689990 :=
  phaseBlock_append rec_7_10_2369_0_part3 rec_7_10_2369_0_join2 rfl rfl rfl
private theorem rec_7_10_2369_0_join4 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 0) 0 678 = 12891072481441729474325333 :=
  phaseBlock_append rec_7_10_2369_0_join1 rec_7_10_2369_0_join3 rfl rfl rfl

private theorem rec_7_10_2369_0 : fastPhase (bank 7 10).shape 179798 2369 20 1 0 23 0 = 12891072481441729474325333 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_7_10_2369_0_join4

private theorem rec_7_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 0 128 = 6730715674748881021209280 := by decide +kernel
private theorem rec_7_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 128 128 = 3620451197096392570268352 := by decide +kernel
private theorem rec_7_10_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 256 128 = 1696071690923918373598923 := by decide +kernel
private theorem rec_7_10_2369_1_part3 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 384 128 = 629961437634926598843735 := by decide +kernel
private theorem rec_7_10_2369_1_part4 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 512 128 = 141726551355239760541176 := by decide +kernel
private theorem rec_7_10_2369_1_part5 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 640 38 = 3820622426303055856644 := by decide +kernel
private theorem rec_7_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 128 256 = 5316522888020310943867275 :=
  phaseBlock_append rec_7_10_2369_1_part1 rec_7_10_2369_1_part2 rfl rfl rfl
private theorem rec_7_10_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 0 384 = 12047238562769191965076555 :=
  phaseBlock_append rec_7_10_2369_1_part0 rec_7_10_2369_1_join0 rfl rfl rfl
private theorem rec_7_10_2369_1_join2 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 512 166 = 145547173781542816397820 :=
  phaseBlock_append rec_7_10_2369_1_part4 rec_7_10_2369_1_part5 rfl rfl rfl
private theorem rec_7_10_2369_1_join3 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 384 294 = 775508611416469415241555 :=
  phaseBlock_append rec_7_10_2369_1_part3 rec_7_10_2369_1_join2 rfl rfl rfl
private theorem rec_7_10_2369_1_join4 :
    phaseBlock (fastLayerG (bank 7 10).shape 179798 2369 20 1 0 23 1) 0 678 = 12822747174185661380318110 :=
  phaseBlock_append rec_7_10_2369_1_join1 rec_7_10_2369_1_join3 rfl rfl rfl

private theorem rec_7_10_2369_1 : fastPhase (bank 7 10).shape 179798 2369 20 1 0 23 1 = 12822747174185661380318110 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_7_10_2369_1_join4

theorem receipt_7_10 : Checked (bank 7 10) 20 0 23 := by
  refine checked_from_values (bank 7 10) 20 0 23
    (P3_7_1.checked (bank 7 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_10_2368_0 rec_7_10_2368_1 rec_7_10_2369_0 rec_7_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 0 128 = 36111004399292111908973600 := by decide +kernel
private theorem rec_7_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 128 128 = 23549445867964765566131232 := by decide +kernel
private theorem rec_7_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 256 128 = 14454616432373085465512992 := by decide +kernel
private theorem rec_7_11_2368_0_part3 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 384 128 = 8159947977785550490434507 := by decide +kernel
private theorem rec_7_11_2368_0_part4 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 512 128 = 4066651957073204790594810 := by decide +kernel
private theorem rec_7_11_2368_0_part5 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 640 128 = 1640373532099196775853418 := by decide +kernel
private theorem rec_7_11_2368_0_part6 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 768 128 = 407883864509871723860812 := by decide +kernel
private theorem rec_7_11_2368_0_part7 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 896 29 = 9000040919517512656920 := by decide +kernel
private theorem rec_7_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 0 256 = 59660450267256877475104832 :=
  phaseBlock_append rec_7_11_2368_0_part0 rec_7_11_2368_0_part1 rfl rfl rfl
private theorem rec_7_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 256 256 = 22614564410158635955947499 :=
  phaseBlock_append rec_7_11_2368_0_part2 rec_7_11_2368_0_part3 rfl rfl rfl
private theorem rec_7_11_2368_0_join2 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 0 512 = 82275014677415513431052331 :=
  phaseBlock_append rec_7_11_2368_0_join0 rec_7_11_2368_0_join1 rfl rfl rfl
private theorem rec_7_11_2368_0_join3 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 512 256 = 5707025489172401566448228 :=
  phaseBlock_append rec_7_11_2368_0_part4 rec_7_11_2368_0_part5 rfl rfl rfl
private theorem rec_7_11_2368_0_join4 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 768 157 = 416883905429389236517732 :=
  phaseBlock_append rec_7_11_2368_0_part6 rec_7_11_2368_0_part7 rfl rfl rfl
private theorem rec_7_11_2368_0_join5 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 512 413 = 6123909394601790802965960 :=
  phaseBlock_append rec_7_11_2368_0_join3 rec_7_11_2368_0_join4 rfl rfl rfl
private theorem rec_7_11_2368_0_join6 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 0) 0 925 = 88398924072017304234018291 :=
  phaseBlock_append rec_7_11_2368_0_join2 rec_7_11_2368_0_join5 rfl rfl rfl

private theorem rec_7_11_2368_0 : fastPhase (bank 7 11).shape 179798 2368 32 1 0 23 0 = 88398924072017304234018291 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_7_11_2368_0_join6

private theorem rec_7_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 0 128 = 35998290793345817128769696 := by decide +kernel
private theorem rec_7_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 128 128 = 23466342734745110180161696 := by decide +kernel
private theorem rec_7_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 256 128 = 14395705916985347326884000 := by decide +kernel
private theorem rec_7_11_2368_1_part3 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 384 128 = 8120344693449046334882262 := by decide +kernel
private theorem rec_7_11_2368_1_part4 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 512 128 = 4041977490057249562449452 := by decide +kernel
private theorem rec_7_11_2368_1_part5 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 640 128 = 1626731050973112143160078 := by decide +kernel
private theorem rec_7_11_2368_1_part6 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 768 128 = 401832696325213501195210 := by decide +kernel
private theorem rec_7_11_2368_1_part7 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 896 29 = 8365193719077092648922 := by decide +kernel
private theorem rec_7_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 0 256 = 59464633528090927308931392 :=
  phaseBlock_append rec_7_11_2368_1_part0 rec_7_11_2368_1_part1 rfl rfl rfl
private theorem rec_7_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 256 256 = 22516050610434393661766262 :=
  phaseBlock_append rec_7_11_2368_1_part2 rec_7_11_2368_1_part3 rfl rfl rfl
private theorem rec_7_11_2368_1_join2 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 0 512 = 81980684138525320970697654 :=
  phaseBlock_append rec_7_11_2368_1_join0 rec_7_11_2368_1_join1 rfl rfl rfl
private theorem rec_7_11_2368_1_join3 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 512 256 = 5668708541030361705609530 :=
  phaseBlock_append rec_7_11_2368_1_part4 rec_7_11_2368_1_part5 rfl rfl rfl
private theorem rec_7_11_2368_1_join4 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 768 157 = 410197890044290593844132 :=
  phaseBlock_append rec_7_11_2368_1_part6 rec_7_11_2368_1_part7 rfl rfl rfl
private theorem rec_7_11_2368_1_join5 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 512 413 = 6078906431074652299453662 :=
  phaseBlock_append rec_7_11_2368_1_join3 rec_7_11_2368_1_join4 rfl rfl rfl
private theorem rec_7_11_2368_1_join6 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2368 32 1 0 23 1) 0 925 = 88059590569599973270151316 :=
  phaseBlock_append rec_7_11_2368_1_join2 rec_7_11_2368_1_join5 rfl rfl rfl

private theorem rec_7_11_2368_1 : fastPhase (bank 7 11).shape 179798 2368 32 1 0 23 1 = 88059590569599973270151316 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_7_11_2368_1_join6

private theorem rec_7_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 0 128 = 36111326711228742595017408 := by decide +kernel
private theorem rec_7_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 128 128 = 23549638384096917521324736 := by decide +kernel
private theorem rec_7_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 256 128 = 14454723258197700338268864 := by decide +kernel
private theorem rec_7_11_2369_0_part3 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 384 128 = 8160001579283322547080090 := by decide +kernel
private theorem rec_7_11_2369_0_part4 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 512 128 = 4066675131250309648925952 := by decide +kernel
private theorem rec_7_11_2369_0_part5 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 640 128 = 1640381401291179748749210 := by decide +kernel
private theorem rec_7_11_2369_0_part6 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 768 128 = 407885455300798466796756 := by decide +kernel
private theorem rec_7_11_2369_0_part7 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 896 29 = 9000069436123889548524 := by decide +kernel
private theorem rec_7_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 0 256 = 59660965095325660116342144 :=
  phaseBlock_append rec_7_11_2369_0_part0 rec_7_11_2369_0_part1 rfl rfl rfl
private theorem rec_7_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 256 256 = 22614724837481022885348954 :=
  phaseBlock_append rec_7_11_2369_0_part2 rec_7_11_2369_0_part3 rfl rfl rfl
private theorem rec_7_11_2369_0_join2 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 0 512 = 82275689932806683001691098 :=
  phaseBlock_append rec_7_11_2369_0_join0 rec_7_11_2369_0_join1 rfl rfl rfl
private theorem rec_7_11_2369_0_join3 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 512 256 = 5707056532541489397675162 :=
  phaseBlock_append rec_7_11_2369_0_part4 rec_7_11_2369_0_part5 rfl rfl rfl
private theorem rec_7_11_2369_0_join4 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 768 157 = 416885524736922356345280 :=
  phaseBlock_append rec_7_11_2369_0_part6 rec_7_11_2369_0_part7 rfl rfl rfl
private theorem rec_7_11_2369_0_join5 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 512 413 = 6123942057278411754020442 :=
  phaseBlock_append rec_7_11_2369_0_join3 rec_7_11_2369_0_join4 rfl rfl rfl
private theorem rec_7_11_2369_0_join6 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 0) 0 925 = 88399631990085094755711540 :=
  phaseBlock_append rec_7_11_2369_0_join2 rec_7_11_2369_0_join5 rfl rfl rfl

private theorem rec_7_11_2369_0 : fastPhase (bank 7 11).shape 179798 2369 32 1 0 23 0 = 88399631990085094755711540 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_7_11_2369_0_join6

private theorem rec_7_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 0 128 = 35998612186602180125611776 := by decide +kernel
private theorem rec_7_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 128 128 = 23466534626780669654259456 := by decide +kernel
private theorem rec_7_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 256 128 = 14395812340271663442712320 := by decide +kernel
private theorem rec_7_11_2369_1_part3 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 384 128 = 8120398052733811191051864 := by decide +kernel
private theorem rec_7_11_2369_1_part4 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 512 128 = 4042000532314357138013946 := by decide +kernel
private theorem rec_7_11_2369_1_part5 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 640 128 = 1626738858251479626544572 := by decide +kernel
private theorem rec_7_11_2369_1_part6 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 768 128 = 401834264685559037129772 := by decide +kernel
private theorem rec_7_11_2369_1_part7 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 896 29 = 8365220259150492424242 := by decide +kernel
private theorem rec_7_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 0 256 = 59465146813382849779871232 :=
  phaseBlock_append rec_7_11_2369_1_part0 rec_7_11_2369_1_part1 rfl rfl rfl
private theorem rec_7_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 256 256 = 22516210393005474633764184 :=
  phaseBlock_append rec_7_11_2369_1_part2 rec_7_11_2369_1_part3 rfl rfl rfl
private theorem rec_7_11_2369_1_join2 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 0 512 = 81981357206388324413635416 :=
  phaseBlock_append rec_7_11_2369_1_join0 rec_7_11_2369_1_join1 rfl rfl rfl
private theorem rec_7_11_2369_1_join3 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 512 256 = 5668739390565836764558518 :=
  phaseBlock_append rec_7_11_2369_1_part4 rec_7_11_2369_1_part5 rfl rfl rfl
private theorem rec_7_11_2369_1_join4 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 768 157 = 410199484944709529554014 :=
  phaseBlock_append rec_7_11_2369_1_part6 rec_7_11_2369_1_part7 rfl rfl rfl
private theorem rec_7_11_2369_1_join5 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 512 413 = 6078938875510546294112532 :=
  phaseBlock_append rec_7_11_2369_1_join3 rec_7_11_2369_1_join4 rfl rfl rfl
private theorem rec_7_11_2369_1_join6 :
    phaseBlock (fastLayerG (bank 7 11).shape 179798 2369 32 1 0 23 1) 0 925 = 88060296081898870707747948 :=
  phaseBlock_append rec_7_11_2369_1_join2 rec_7_11_2369_1_join5 rfl rfl rfl

private theorem rec_7_11_2369_1 : fastPhase (bank 7 11).shape 179798 2369 32 1 0 23 1 = 88060296081898870707747948 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_7_11_2369_1_join6

theorem receipt_7_11 : Checked (bank 7 11) 32 0 23 := by
  refine checked_from_values (bank 7 11) 32 0 23
    (P3_7_1.checked (bank 7 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_11_2368_0 rec_7_11_2368_1 rec_7_11_2369_0 rec_7_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 0 128 = 34159263677759364068674400 := by decide +kernel
private theorem rec_7_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 128 128 = 22125413163018863673809760 := by decide +kernel
private theorem rec_7_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 256 128 = 13462874627866080115174240 := by decide +kernel
private theorem rec_7_12_2368_0_part3 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 384 128 = 7513216261125416701863792 := by decide +kernel
private theorem rec_7_12_2368_0_part4 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 512 128 = 3685448300786169425597082 := by decide +kernel
private theorem rec_7_12_2368_0_part5 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 640 128 = 1452679231297360343772509 := by decide +kernel
private theorem rec_7_12_2368_0_part6 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 768 128 = 348806821961103416911984 := by decide +kernel
private theorem rec_7_12_2368_0_part7 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 896 29 = 7363410341442284829708 := by decide +kernel
private theorem rec_7_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 0 256 = 56284676840778227742484160 :=
  phaseBlock_append rec_7_12_2368_0_part0 rec_7_12_2368_0_part1 rfl rfl rfl
private theorem rec_7_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 256 256 = 20976090888991496817038032 :=
  phaseBlock_append rec_7_12_2368_0_part2 rec_7_12_2368_0_part3 rfl rfl rfl
private theorem rec_7_12_2368_0_join2 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 0 512 = 77260767729769724559522192 :=
  phaseBlock_append rec_7_12_2368_0_join0 rec_7_12_2368_0_join1 rfl rfl rfl
private theorem rec_7_12_2368_0_join3 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 512 256 = 5138127532083529769369591 :=
  phaseBlock_append rec_7_12_2368_0_part4 rec_7_12_2368_0_part5 rfl rfl rfl
private theorem rec_7_12_2368_0_join4 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 768 157 = 356170232302545701741692 :=
  phaseBlock_append rec_7_12_2368_0_part6 rec_7_12_2368_0_part7 rfl rfl rfl
private theorem rec_7_12_2368_0_join5 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 512 413 = 5494297764386075471111283 :=
  phaseBlock_append rec_7_12_2368_0_join3 rec_7_12_2368_0_join4 rfl rfl rfl
private theorem rec_7_12_2368_0_join6 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 0) 0 925 = 82755065494155800030633475 :=
  phaseBlock_append rec_7_12_2368_0_join2 rec_7_12_2368_0_join5 rfl rfl rfl

private theorem rec_7_12_2368_0 : fastPhase (bank 7 12).shape 179798 2368 31 1 0 23 0 = 82755065494155800030633475 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_7_12_2368_0_join6

private theorem rec_7_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 0 128 = 34051025719060654930185824 := by decide +kernel
private theorem rec_7_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 128 128 = 22046017644338023434436192 := by decide +kernel
private theorem rec_7_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 256 128 = 13406967029732590634774112 := by decide +kernel
private theorem rec_7_12_2368_1_part3 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 384 128 = 7475971965656043313002138 := by decide +kernel
private theorem rec_7_12_2368_1_part4 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 512 128 = 3662547099549945180485909 := by decide +kernel
private theorem rec_7_12_2368_1_part5 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 640 128 = 1440279930239420774244372 := by decide +kernel
private theorem rec_7_12_2368_1_part6 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 768 128 = 343521814122935110015720 := by decide +kernel
private theorem rec_7_12_2368_1_part7 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 896 29 = 6841124603602972303536 := by decide +kernel
private theorem rec_7_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 0 256 = 56097043363398678364622016 :=
  phaseBlock_append rec_7_12_2368_1_part0 rec_7_12_2368_1_part1 rfl rfl rfl
private theorem rec_7_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 256 256 = 20882938995388633947776250 :=
  phaseBlock_append rec_7_12_2368_1_part2 rec_7_12_2368_1_part3 rfl rfl rfl
private theorem rec_7_12_2368_1_join2 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 0 512 = 76979982358787312312398266 :=
  phaseBlock_append rec_7_12_2368_1_join0 rec_7_12_2368_1_join1 rfl rfl rfl
private theorem rec_7_12_2368_1_join3 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 512 256 = 5102827029789365954730281 :=
  phaseBlock_append rec_7_12_2368_1_part4 rec_7_12_2368_1_part5 rfl rfl rfl
private theorem rec_7_12_2368_1_join4 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 768 157 = 350362938726538082319256 :=
  phaseBlock_append rec_7_12_2368_1_part6 rec_7_12_2368_1_part7 rfl rfl rfl
private theorem rec_7_12_2368_1_join5 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 512 413 = 5453189968515904037049537 :=
  phaseBlock_append rec_7_12_2368_1_join3 rec_7_12_2368_1_join4 rfl rfl rfl
private theorem rec_7_12_2368_1_join6 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2368 31 1 0 23 1) 0 925 = 82433172327303216349447803 :=
  phaseBlock_append rec_7_12_2368_1_join2 rec_7_12_2368_1_join5 rfl rfl rfl

private theorem rec_7_12_2368_1 : fastPhase (bank 7 12).shape 179798 2368 31 1 0 23 1 = 82433172327303216349447803 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_7_12_2368_1_join6

private theorem rec_7_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 0 128 = 34159568860759617703347360 := by decide +kernel
private theorem rec_7_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 128 128 = 22125594233302949861504160 := by decide +kernel
private theorem rec_7_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 256 128 = 13462974248284327285744800 := by decide +kernel
private theorem rec_7_12_2369_0_part3 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 384 128 = 7513265687578961933833575 := by decide +kernel
private theorem rec_7_12_2369_0_part4 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 512 128 = 3685469341397178981923562 := by decide +kernel
private theorem rec_7_12_2369_0_part5 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 640 128 = 1452686216762439942431952 := by decide +kernel
private theorem rec_7_12_2369_0_part6 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 768 128 = 348808186762051059548766 := by decide +kernel
private theorem rec_7_12_2369_0_part7 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 896 29 = 7363433744399405672295 := by decide +kernel
private theorem rec_7_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 0 256 = 56285163094062567564851520 :=
  phaseBlock_append rec_7_12_2369_0_part0 rec_7_12_2369_0_part1 rfl rfl rfl
private theorem rec_7_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 256 256 = 20976239935863289219578375 :=
  phaseBlock_append rec_7_12_2369_0_part2 rec_7_12_2369_0_part3 rfl rfl rfl
private theorem rec_7_12_2369_0_join2 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 0 512 = 77261403029925856784429895 :=
  phaseBlock_append rec_7_12_2369_0_join0 rec_7_12_2369_0_join1 rfl rfl rfl
private theorem rec_7_12_2369_0_join3 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 512 256 = 5138155558159618924355514 :=
  phaseBlock_append rec_7_12_2369_0_part4 rec_7_12_2369_0_part5 rfl rfl rfl
private theorem rec_7_12_2369_0_join4 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 768 157 = 356171620506450465221061 :=
  phaseBlock_append rec_7_12_2369_0_part6 rec_7_12_2369_0_part7 rfl rfl rfl
private theorem rec_7_12_2369_0_join5 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 512 413 = 5494327178666069389576575 :=
  phaseBlock_append rec_7_12_2369_0_join3 rec_7_12_2369_0_join4 rfl rfl rfl
private theorem rec_7_12_2369_0_join6 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 0) 0 925 = 82755730208591926174006470 :=
  phaseBlock_append rec_7_12_2369_0_join2 rec_7_12_2369_0_join5 rfl rfl rfl

private theorem rec_7_12_2369_0 : fastPhase (bank 7 12).shape 179798 2369 31 1 0 23 0 = 82755730208591926174006470 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_7_12_2369_0_join6

private theorem rec_7_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 0 128 = 34051330017740514398101152 := by decide +kernel
private theorem rec_7_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 128 128 = 22046198116835444536938144 := by decide +kernel
private theorem rec_7_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 256 128 = 13407066267071595276943008 := by decide +kernel
private theorem rec_7_12_2369_1_part3 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 384 128 = 7476021163633866150756045 := by decide +kernel
private theorem rec_7_12_2369_1_part4 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 512 128 = 3662568017309967974063115 := by decide +kernel
private theorem rec_7_12_2369_1_part5 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 640 128 = 1440286859220063295746993 := by decide +kernel
private theorem rec_7_12_2369_1_part6 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 768 128 = 343523159244900922137147 := by decide +kernel
private theorem rec_7_12_2369_1_part7 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 896 29 = 6841146375068017569159 := by decide +kernel
private theorem rec_7_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 0 256 = 56097528134575958935039296 :=
  phaseBlock_append rec_7_12_2369_1_part0 rec_7_12_2369_1_part1 rfl rfl rfl
private theorem rec_7_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 256 256 = 20883087430705461427699053 :=
  phaseBlock_append rec_7_12_2369_1_part2 rec_7_12_2369_1_part3 rfl rfl rfl
private theorem rec_7_12_2369_1_join2 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 0 512 = 76980615565281420362738349 :=
  phaseBlock_append rec_7_12_2369_1_join0 rec_7_12_2369_1_join1 rfl rfl rfl
private theorem rec_7_12_2369_1_join3 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 512 256 = 5102854876530031269810108 :=
  phaseBlock_append rec_7_12_2369_1_part4 rec_7_12_2369_1_part5 rfl rfl rfl
private theorem rec_7_12_2369_1_join4 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 768 157 = 350364305619968939706306 :=
  phaseBlock_append rec_7_12_2369_1_part6 rec_7_12_2369_1_part7 rfl rfl rfl
private theorem rec_7_12_2369_1_join5 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 512 413 = 5453219182150000209516414 :=
  phaseBlock_append rec_7_12_2369_1_join3 rec_7_12_2369_1_join4 rfl rfl rfl
private theorem rec_7_12_2369_1_join6 :
    phaseBlock (fastLayerG (bank 7 12).shape 179798 2369 31 1 0 23 1) 0 925 = 82433834747431420572254763 :=
  phaseBlock_append rec_7_12_2369_1_join2 rec_7_12_2369_1_join5 rfl rfl rfl

private theorem rec_7_12_2369_1 : fastPhase (bank 7 12).shape 179798 2369 31 1 0 23 1 = 82433834747431420572254763 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_7_12_2369_1_join6

theorem receipt_7_12 : Checked (bank 7 12) 31 0 23 := by
  refine checked_from_values (bank 7 12) 31 0 23
    (P3_7_1.checked (bank 7 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_12_2368_0 rec_7_12_2368_1 rec_7_12_2369_0 rec_7_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 0 128 = 172093525896033411798490560 := by decide +kernel
private theorem rec_7_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 128 128 = 126163157676826200079982016 := by decide +kernel
private theorem rec_7_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 256 128 = 89737379692968890472488384 := by decide +kernel
private theorem rec_7_13_2368_0_part3 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 384 128 = 61482097355391610722901440 := by decide +kernel
private theorem rec_7_13_2368_0_part4 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 512 128 = 40159953448648571080891840 := by decide +kernel
private theorem rec_7_13_2368_0_part5 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 640 128 = 24627011137597154147097360 := by decide +kernel
private theorem rec_7_13_2368_0_part6 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 768 128 = 13829421044227292286135679 := by decide +kernel
private theorem rec_7_13_2368_0_part7 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 896 128 = 6800061040520351177557991 := by decide +kernel
private theorem rec_7_13_2368_0_part8 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 1024 128 = 2655265948324275475154732 := by decide +kernel
private theorem rec_7_13_2368_0_part9 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 1152 128 = 591502001105967051188190 := by decide +kernel
private theorem rec_7_13_2368_0_part10 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 1280 14 = 3722830591172117880602 := by decide +kernel
private theorem rec_7_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 0 256 = 298256683572859611878472576 :=
  phaseBlock_append rec_7_13_2368_0_part0 rec_7_13_2368_0_part1 rfl rfl rfl
private theorem rec_7_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 384 256 = 101642050804040181803793280 :=
  phaseBlock_append rec_7_13_2368_0_part3 rec_7_13_2368_0_part4 rfl rfl rfl
private theorem rec_7_13_2368_0_join2 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 256 384 = 191379430497009072276281664 :=
  phaseBlock_append rec_7_13_2368_0_part2 rec_7_13_2368_0_join1 rfl rfl rfl
private theorem rec_7_13_2368_0_join3 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 0 640 = 489636114069868684154754240 :=
  phaseBlock_append rec_7_13_2368_0_join0 rec_7_13_2368_0_join2 rfl rfl rfl
private theorem rec_7_13_2368_0_join4 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 768 256 = 20629482084747643463693670 :=
  phaseBlock_append rec_7_13_2368_0_part6 rec_7_13_2368_0_part7 rfl rfl rfl
private theorem rec_7_13_2368_0_join5 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 640 384 = 45256493222344797610791030 :=
  phaseBlock_append rec_7_13_2368_0_part5 rec_7_13_2368_0_join4 rfl rfl rfl
private theorem rec_7_13_2368_0_join6 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 1152 142 = 595224831697139169068792 :=
  phaseBlock_append rec_7_13_2368_0_part9 rec_7_13_2368_0_part10 rfl rfl rfl
private theorem rec_7_13_2368_0_join7 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 1024 270 = 3250490780021414644223524 :=
  phaseBlock_append rec_7_13_2368_0_part8 rec_7_13_2368_0_join6 rfl rfl rfl
private theorem rec_7_13_2368_0_join8 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 640 654 = 48506984002366212255014554 :=
  phaseBlock_append rec_7_13_2368_0_join5 rec_7_13_2368_0_join7 rfl rfl rfl
private theorem rec_7_13_2368_0_join9 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 0) 0 1294 = 538143098072234896409768794 :=
  phaseBlock_append rec_7_13_2368_0_join3 rec_7_13_2368_0_join8 rfl rfl rfl

private theorem rec_7_13_2368_0 : fastPhase (bank 7 13).shape 179798 2368 44 1 0 23 0 = 538143098072234896409768794 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_7_13_2368_0_join9

private theorem rec_7_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 0 128 = 171696647677059332045276992 := by decide +kernel
private theorem rec_7_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 128 128 = 125845341845505981641557824 := by decide +kernel
private theorem rec_7_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 256 128 = 89487938708608417843709760 := by decide +kernel
private theorem rec_7_13_2368_1_part3 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 384 128 = 61291098335747887960917824 := by decide +kernel
private theorem rec_7_13_2368_1_part4 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 512 128 = 40018192710856659188188992 := by decide +kernel
private theorem rec_7_13_2368_1_part5 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 640 128 = 24525988706983759748937195 := by decide +kernel
private theorem rec_7_13_2368_1_part6 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 768 128 = 13761315172380717400041777 := by decide +kernel
private theorem rec_7_13_2368_1_part7 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 896 128 = 6757702897382144604069800 := by decide +kernel
private theorem rec_7_13_2368_1_part8 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 1024 128 = 2632114142926749960607719 := by decide +kernel
private theorem rec_7_13_2368_1_part9 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 1152 128 = 581617065414848673217709 := by decide +kernel
private theorem rec_7_13_2368_1_part10 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 1280 14 = 3212452051650243696294 := by decide +kernel
private theorem rec_7_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 0 256 = 297541989522565313686834816 :=
  phaseBlock_append rec_7_13_2368_1_part0 rec_7_13_2368_1_part1 rfl rfl rfl
private theorem rec_7_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 384 256 = 101309291046604547149106816 :=
  phaseBlock_append rec_7_13_2368_1_part3 rec_7_13_2368_1_part4 rfl rfl rfl
private theorem rec_7_13_2368_1_join2 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 256 384 = 190797229755212964992816576 :=
  phaseBlock_append rec_7_13_2368_1_part2 rec_7_13_2368_1_join1 rfl rfl rfl
private theorem rec_7_13_2368_1_join3 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 0 640 = 488339219277778278679651392 :=
  phaseBlock_append rec_7_13_2368_1_join0 rec_7_13_2368_1_join2 rfl rfl rfl
private theorem rec_7_13_2368_1_join4 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 768 256 = 20519018069762862004111577 :=
  phaseBlock_append rec_7_13_2368_1_part6 rec_7_13_2368_1_part7 rfl rfl rfl
private theorem rec_7_13_2368_1_join5 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 640 384 = 45045006776746621753048772 :=
  phaseBlock_append rec_7_13_2368_1_part5 rec_7_13_2368_1_join4 rfl rfl rfl
private theorem rec_7_13_2368_1_join6 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 1152 142 = 584829517466498916914003 :=
  phaseBlock_append rec_7_13_2368_1_part9 rec_7_13_2368_1_part10 rfl rfl rfl
private theorem rec_7_13_2368_1_join7 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 1024 270 = 3216943660393248877521722 :=
  phaseBlock_append rec_7_13_2368_1_part8 rec_7_13_2368_1_join6 rfl rfl rfl
private theorem rec_7_13_2368_1_join8 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 640 654 = 48261950437139870630570494 :=
  phaseBlock_append rec_7_13_2368_1_join5 rec_7_13_2368_1_join7 rfl rfl rfl
private theorem rec_7_13_2368_1_join9 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2368 44 1 0 23 1) 0 1294 = 536601169714918149310221886 :=
  phaseBlock_append rec_7_13_2368_1_join3 rec_7_13_2368_1_join8 rfl rfl rfl

private theorem rec_7_13_2368_1 : fastPhase (bank 7 13).shape 179798 2368 44 1 0 23 1 = 536601169714918149310221886 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_7_13_2368_1_join9

private theorem rec_7_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 0 128 = 172095078514971190473215040 := by decide +kernel
private theorem rec_7_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 128 128 = 126164228970767120733678656 := by decide +kernel
private theorem rec_7_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 256 128 = 89738092515834973081308224 := by decide +kernel
private theorem rec_7_13_2369_0_part3 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 384 128 = 61482550948934432782969920 := by decide +kernel
private theorem rec_7_13_2369_0_part4 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 512 128 = 40160226274186661162699840 := by decide +kernel
private theorem rec_7_13_2369_0_part5 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 640 128 = 24627163423459862071487082 := by decide +kernel
private theorem rec_7_13_2369_0_part6 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 768 128 = 13829497785813443854578867 := by decide +kernel
private theorem rec_7_13_2369_0_part7 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 896 128 = 6800094344780154587309940 := by decide +kernel
private theorem rec_7_13_2369_0_part8 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 1024 128 = 2655277190802350644728387 := by decide +kernel
private theorem rec_7_13_2369_0_part9 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 1152 128 = 591504125232520706109673 := by decide +kernel
private theorem rec_7_13_2369_0_part10 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 1280 14 = 3722842042818271074520 := by decide +kernel
private theorem rec_7_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 0 256 = 298259307485738311206893696 :=
  phaseBlock_append rec_7_13_2369_0_part0 rec_7_13_2369_0_part1 rfl rfl rfl
private theorem rec_7_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 384 256 = 101642777223121093945669760 :=
  phaseBlock_append rec_7_13_2369_0_part3 rec_7_13_2369_0_part4 rfl rfl rfl
private theorem rec_7_13_2369_0_join2 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 256 384 = 191380869738956067026977984 :=
  phaseBlock_append rec_7_13_2369_0_part2 rec_7_13_2369_0_join1 rfl rfl rfl
private theorem rec_7_13_2369_0_join3 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 0 640 = 489640177224694378233871680 :=
  phaseBlock_append rec_7_13_2369_0_join0 rec_7_13_2369_0_join2 rfl rfl rfl
private theorem rec_7_13_2369_0_join4 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 768 256 = 20629592130593598441888807 :=
  phaseBlock_append rec_7_13_2369_0_part6 rec_7_13_2369_0_part7 rfl rfl rfl
private theorem rec_7_13_2369_0_join5 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 640 384 = 45256755554053460513375889 :=
  phaseBlock_append rec_7_13_2369_0_part5 rec_7_13_2369_0_join4 rfl rfl rfl
private theorem rec_7_13_2369_0_join6 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 1152 142 = 595226967275338977184193 :=
  phaseBlock_append rec_7_13_2369_0_part9 rec_7_13_2369_0_part10 rfl rfl rfl
private theorem rec_7_13_2369_0_join7 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 1024 270 = 3250504158077689621912580 :=
  phaseBlock_append rec_7_13_2369_0_part8 rec_7_13_2369_0_join6 rfl rfl rfl
private theorem rec_7_13_2369_0_join8 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 640 654 = 48507259712131150135288469 :=
  phaseBlock_append rec_7_13_2369_0_join5 rec_7_13_2369_0_join7 rfl rfl rfl
private theorem rec_7_13_2369_0_join9 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 0) 0 1294 = 538147436936825528369160149 :=
  phaseBlock_append rec_7_13_2369_0_join3 rec_7_13_2369_0_join8 rfl rfl rfl

private theorem rec_7_13_2369_0 : fastPhase (bank 7 13).shape 179798 2369 44 1 0 23 0 = 538147436936825528369160149 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_7_13_2369_0_join9

private theorem rec_7_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 0 128 = 171698197012936355105750848 := by decide +kernel
private theorem rec_7_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 128 128 = 125846410654147200832855872 := by decide +kernel
private theorem rec_7_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 256 128 = 89488649698258369587085120 := by decide +kernel
private theorem rec_7_13_2369_1_part3 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 384 128 = 61291550619147124654710592 := by decide +kernel
private theorem rec_7_13_2369_1_part4 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 512 128 = 40018464636288443301543744 := by decide +kernel
private theorem rec_7_13_2369_1_part5 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 640 128 = 24526140405699937912886158 := by decide +kernel
private theorem rec_7_13_2369_1_part6 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 768 128 = 13761391556570176715056634 := by decide +kernel
private theorem rec_7_13_2369_1_part7 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 896 128 = 6757736004131198898347450 := by decide +kernel
private theorem rec_7_13_2369_1_part8 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 1024 128 = 2632125291396449191947122 := by decide +kernel
private theorem rec_7_13_2369_1_part9 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 1152 128 = 581619155402488862229519 := by decide +kernel
private theorem rec_7_13_2369_1_part10 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 1280 14 = 3212461943024622434146 := by decide +kernel
private theorem rec_7_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 0 256 = 297544607667083555938606720 :=
  phaseBlock_append rec_7_13_2369_1_part0 rec_7_13_2369_1_part1 rfl rfl rfl
private theorem rec_7_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 384 256 = 101310015255435567956254336 :=
  phaseBlock_append rec_7_13_2369_1_part3 rec_7_13_2369_1_part4 rfl rfl rfl
private theorem rec_7_13_2369_1_join2 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 256 384 = 190798664953693937543339456 :=
  phaseBlock_append rec_7_13_2369_1_part2 rec_7_13_2369_1_join1 rfl rfl rfl
private theorem rec_7_13_2369_1_join3 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 0 640 = 488343272620777493481946176 :=
  phaseBlock_append rec_7_13_2369_1_join0 rec_7_13_2369_1_join2 rfl rfl rfl
private theorem rec_7_13_2369_1_join4 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 768 256 = 20519127560701375613404084 :=
  phaseBlock_append rec_7_13_2369_1_part6 rec_7_13_2369_1_part7 rfl rfl rfl
private theorem rec_7_13_2369_1_join5 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 640 384 = 45045267966401313526290242 :=
  phaseBlock_append rec_7_13_2369_1_part5 rec_7_13_2369_1_join4 rfl rfl rfl
private theorem rec_7_13_2369_1_join6 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 1152 142 = 584831617345513484663665 :=
  phaseBlock_append rec_7_13_2369_1_part9 rec_7_13_2369_1_part10 rfl rfl rfl
private theorem rec_7_13_2369_1_join7 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 1024 270 = 3216956908741962676610787 :=
  phaseBlock_append rec_7_13_2369_1_part8 rec_7_13_2369_1_join6 rfl rfl rfl
private theorem rec_7_13_2369_1_join8 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 640 654 = 48262224875143276202901029 :=
  phaseBlock_append rec_7_13_2369_1_join5 rec_7_13_2369_1_join7 rfl rfl rfl
private theorem rec_7_13_2369_1_join9 :
    phaseBlock (fastLayerG (bank 7 13).shape 179798 2369 44 1 0 23 1) 0 1294 = 536605497495920769684847205 :=
  phaseBlock_append rec_7_13_2369_1_join3 rec_7_13_2369_1_join8 rfl rfl rfl

private theorem rec_7_13_2369_1 : fastPhase (bank 7 13).shape 179798 2369 44 1 0 23 1 = 536605497495920769684847205 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_7_13_2369_1_join9

theorem receipt_7_13 : Checked (bank 7 13) 44 0 23 := by
  refine checked_from_values (bank 7 13) 44 0 23
    (P3_7_1.checked (bank 7 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_13_2368_0 rec_7_13_2368_1 rec_7_13_2369_0 rec_7_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 0 128 = 1237713569101815400332495168 := by decide +kernel
private theorem rec_7_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 128 128 = 1012344014589541548686379328 := by decide +kernel
private theorem rec_7_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 256 128 = 817883512512158003848972608 := by decide +kernel
private theorem rec_7_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 384 128 = 651496134548721872733473088 := by decide +kernel
private theorem rec_7_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 512 128 = 510486570138088272678979904 := by decide +kernel
private theorem rec_7_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 640 128 = 392296801605841686587967808 := by decide +kernel
private theorem rec_7_14_2368_0_part6 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 768 128 = 294502779315356069703963747 := by decide +kernel
private theorem rec_7_14_2368_0_part7 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 896 128 = 214811144686079537658005313 := by decide +kernel
private theorem rec_7_14_2368_0_part8 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 1024 128 = 151055868452072013553300301 := by decide +kernel
private theorem rec_7_14_2368_0_part9 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 1152 128 = 101194748326927040489637099 := by decide +kernel
private theorem rec_7_14_2368_0_part10 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 1280 128 = 63306280131702860907473425 := by decide +kernel
private theorem rec_7_14_2368_0_part11 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 1408 128 = 35586353481932301121225968 := by decide +kernel
private theorem rec_7_14_2368_0_part12 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 1536 128 = 16344914826982763638184979 := by decide +kernel
private theorem rec_7_14_2368_0_part13 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 1664 123 = 4006849155108610113021825 := by decide +kernel
private theorem rec_7_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 128 256 = 1830227527101699552535351936 :=
  phaseBlock_append rec_7_14_2368_0_part1 rec_7_14_2368_0_part2 rfl rfl rfl
private theorem rec_7_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 0 384 = 3067941096203514952867847104 :=
  phaseBlock_append rec_7_14_2368_0_part0 rec_7_14_2368_0_join0 rfl rfl rfl
private theorem rec_7_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 384 256 = 1161982704686810145412452992 :=
  phaseBlock_append rec_7_14_2368_0_part3 rec_7_14_2368_0_part4 rfl rfl rfl
private theorem rec_7_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 640 256 = 686799580921197756291931555 :=
  phaseBlock_append rec_7_14_2368_0_part5 rec_7_14_2368_0_part6 rfl rfl rfl
private theorem rec_7_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 384 512 = 1848782285608007901704384547 :=
  phaseBlock_append rec_7_14_2368_0_join2 rec_7_14_2368_0_join3 rfl rfl rfl
private theorem rec_7_14_2368_0_join5 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 0 896 = 4916723381811522854572231651 :=
  phaseBlock_append rec_7_14_2368_0_join1 rec_7_14_2368_0_join4 rfl rfl rfl
private theorem rec_7_14_2368_0_join6 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 1024 256 = 252250616778999054042937400 :=
  phaseBlock_append rec_7_14_2368_0_part8 rec_7_14_2368_0_part9 rfl rfl rfl
private theorem rec_7_14_2368_0_join7 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 896 384 = 467061761465078591700942713 :=
  phaseBlock_append rec_7_14_2368_0_part7 rec_7_14_2368_0_join6 rfl rfl rfl
private theorem rec_7_14_2368_0_join8 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 1280 256 = 98892633613635162028699393 :=
  phaseBlock_append rec_7_14_2368_0_part10 rec_7_14_2368_0_part11 rfl rfl rfl
private theorem rec_7_14_2368_0_join9 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 1536 251 = 20351763982091373751206804 :=
  phaseBlock_append rec_7_14_2368_0_part12 rec_7_14_2368_0_part13 rfl rfl rfl
private theorem rec_7_14_2368_0_join10 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 1280 507 = 119244397595726535779906197 :=
  phaseBlock_append rec_7_14_2368_0_join8 rec_7_14_2368_0_join9 rfl rfl rfl
private theorem rec_7_14_2368_0_join11 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 896 891 = 586306159060805127480848910 :=
  phaseBlock_append rec_7_14_2368_0_join7 rec_7_14_2368_0_join10 rfl rfl rfl
private theorem rec_7_14_2368_0_join12 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 0) 0 1787 = 5503029540872327982053080561 :=
  phaseBlock_append rec_7_14_2368_0_join5 rec_7_14_2368_0_join11 rfl rfl rfl

private theorem rec_7_14_2368_0 : fastPhase (bank 7 14).shape 179798 2368 76 1 0 23 0 = 5503029540872327982053080561 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_7_14_2368_0_join12

private theorem rec_7_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 0 128 = 1235838064558326175056259072 := by decide +kernel
private theorem rec_7_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 128 128 = 1010719169781809656925276160 := by decide +kernel
private theorem rec_7_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 256 128 = 816486890802930052807305216 := by decide +kernel
private theorem rec_7_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 384 128 = 650306390300068959320606720 := by decide +kernel
private theorem rec_7_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 512 128 = 509483423252332920892385280 := by decide +kernel
private theorem rec_7_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 640 128 = 391461012066484784896264192 := by decide +kernel
private theorem rec_7_14_2368_1_part6 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 768 128 = 293816121727946964953838621 := by decide +kernel
private theorem rec_7_14_2368_1_part7 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 896 128 = 214256382699399525750771432 := by decide +kernel
private theorem rec_7_14_2368_1_part8 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 1024 128 = 150616729211614113841377488 := by decide +kernel
private theorem rec_7_14_2368_1_part9 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 1152 128 = 100855897409999554944924955 := by decide +kernel
private theorem rec_7_14_2368_1_part10 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 1280 128 = 63053296100701899536037849 := by decide +kernel
private theorem rec_7_14_2368_1_part11 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 1408 128 = 35405702368371286409338785 := by decide +kernel
private theorem rec_7_14_2368_1_part12 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 1536 128 = 16223924615214869790428021 := by decide +kernel
private theorem rec_7_14_2368_1_part13 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 1664 123 = 3935782453896263879149258 := by decide +kernel
private theorem rec_7_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 128 256 = 1827206060584739709732581376 :=
  phaseBlock_append rec_7_14_2368_1_part1 rec_7_14_2368_1_part2 rfl rfl rfl
private theorem rec_7_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 0 384 = 3063044125143065884788840448 :=
  phaseBlock_append rec_7_14_2368_1_part0 rec_7_14_2368_1_join0 rfl rfl rfl
private theorem rec_7_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 384 256 = 1159789813552401880212992000 :=
  phaseBlock_append rec_7_14_2368_1_part3 rec_7_14_2368_1_part4 rfl rfl rfl
private theorem rec_7_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 640 256 = 685277133794431749850102813 :=
  phaseBlock_append rec_7_14_2368_1_part5 rec_7_14_2368_1_part6 rfl rfl rfl
private theorem rec_7_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 384 512 = 1845066947346833630063094813 :=
  phaseBlock_append rec_7_14_2368_1_join2 rec_7_14_2368_1_join3 rfl rfl rfl
private theorem rec_7_14_2368_1_join5 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 0 896 = 4908111072489899514851935261 :=
  phaseBlock_append rec_7_14_2368_1_join1 rec_7_14_2368_1_join4 rfl rfl rfl
private theorem rec_7_14_2368_1_join6 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 1024 256 = 251472626621613668786302443 :=
  phaseBlock_append rec_7_14_2368_1_part8 rec_7_14_2368_1_part9 rfl rfl rfl
private theorem rec_7_14_2368_1_join7 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 896 384 = 465729009321013194537073875 :=
  phaseBlock_append rec_7_14_2368_1_part7 rec_7_14_2368_1_join6 rfl rfl rfl
private theorem rec_7_14_2368_1_join8 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 1280 256 = 98458998469073185945376634 :=
  phaseBlock_append rec_7_14_2368_1_part10 rec_7_14_2368_1_part11 rfl rfl rfl
private theorem rec_7_14_2368_1_join9 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 1536 251 = 20159707069111133669577279 :=
  phaseBlock_append rec_7_14_2368_1_part12 rec_7_14_2368_1_part13 rfl rfl rfl
private theorem rec_7_14_2368_1_join10 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 1280 507 = 118618705538184319614953913 :=
  phaseBlock_append rec_7_14_2368_1_join8 rec_7_14_2368_1_join9 rfl rfl rfl
private theorem rec_7_14_2368_1_join11 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 896 891 = 584347714859197514152027788 :=
  phaseBlock_append rec_7_14_2368_1_join7 rec_7_14_2368_1_join10 rfl rfl rfl
private theorem rec_7_14_2368_1_join12 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2368 76 1 0 23 1) 0 1787 = 5492458787349097029003963049 :=
  phaseBlock_append rec_7_14_2368_1_join5 rec_7_14_2368_1_join11 rfl rfl rfl

private theorem rec_7_14_2368_1 : fastPhase (bank 7 14).shape 179798 2368 76 1 0 23 1 = 5492458787349097029003963049 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_7_14_2368_1_join12

private theorem rec_7_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 0 128 = 1237724736026379819965655744 := by decide +kernel
private theorem rec_7_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 128 128 = 1012352761243082640127265472 := by decide +kernel
private theorem rec_7_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 256 128 = 817890259011575975439788736 := by decide +kernel
private theorem rec_7_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 384 128 = 651501247588183523511716544 := by decide +kernel
private theorem rec_7_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 512 128 = 510490367142156223242447552 := by decide +kernel
private theorem rec_7_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 640 128 = 392299554766275279741061824 := by decide +kernel
private theorem rec_7_14_2369_0_part6 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 768 128 = 294504719497908892822061448 := by decide +kernel
private theorem rec_7_14_2369_0_part7 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 896 128 = 214812464020975100205957651 := by decide +kernel
private theorem rec_7_14_2369_0_part8 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 1024 128 = 151056726699630683482055721 := by decide +kernel
private theorem rec_7_14_2369_0_part9 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 1152 128 = 101195275699693800360752277 := by decide +kernel
private theorem rec_7_14_2369_0_part10 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 1280 128 = 63306579658798146450944793 := by decide +kernel
private theorem rec_7_14_2369_0_part11 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 1408 128 = 35586504453513103567580367 := by decide +kernel
private theorem rec_7_14_2369_0_part12 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 1536 128 = 16344976103667965823142476 := by decide +kernel
private theorem rec_7_14_2369_0_part13 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 1664 123 = 4006862344187322975306513 := by decide +kernel
private theorem rec_7_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 128 256 = 1830243020254658615567054208 :=
  phaseBlock_append rec_7_14_2369_0_part1 rec_7_14_2369_0_part2 rfl rfl rfl
private theorem rec_7_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 0 384 = 3067967756281038435532709952 :=
  phaseBlock_append rec_7_14_2369_0_part0 rec_7_14_2369_0_join0 rfl rfl rfl
private theorem rec_7_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 384 256 = 1161991614730339746754164096 :=
  phaseBlock_append rec_7_14_2369_0_part3 rec_7_14_2369_0_part4 rfl rfl rfl
private theorem rec_7_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 640 256 = 686804274264184172563123272 :=
  phaseBlock_append rec_7_14_2369_0_part5 rec_7_14_2369_0_part6 rfl rfl rfl
private theorem rec_7_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 384 512 = 1848795888994523919317287368 :=
  phaseBlock_append rec_7_14_2369_0_join2 rec_7_14_2369_0_join3 rfl rfl rfl
private theorem rec_7_14_2369_0_join5 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 0 896 = 4916763645275562354849997320 :=
  phaseBlock_append rec_7_14_2369_0_join1 rec_7_14_2369_0_join4 rfl rfl rfl
private theorem rec_7_14_2369_0_join6 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 1024 256 = 252252002399324483842807998 :=
  phaseBlock_append rec_7_14_2369_0_part8 rec_7_14_2369_0_part9 rfl rfl rfl
private theorem rec_7_14_2369_0_join7 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 896 384 = 467064466420299584048765649 :=
  phaseBlock_append rec_7_14_2369_0_part7 rec_7_14_2369_0_join6 rfl rfl rfl
private theorem rec_7_14_2369_0_join8 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 1280 256 = 98893084112311250018525160 :=
  phaseBlock_append rec_7_14_2369_0_part10 rec_7_14_2369_0_part11 rfl rfl rfl
private theorem rec_7_14_2369_0_join9 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 1536 251 = 20351838447855288798448989 :=
  phaseBlock_append rec_7_14_2369_0_part12 rec_7_14_2369_0_part13 rfl rfl rfl
private theorem rec_7_14_2369_0_join10 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 1280 507 = 119244922560166538816974149 :=
  phaseBlock_append rec_7_14_2369_0_join8 rec_7_14_2369_0_join9 rfl rfl rfl
private theorem rec_7_14_2369_0_join11 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 896 891 = 586309388980466122865739798 :=
  phaseBlock_append rec_7_14_2369_0_join7 rec_7_14_2369_0_join10 rfl rfl rfl
private theorem rec_7_14_2369_0_join12 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 0) 0 1787 = 5503073034256028477715737118 :=
  phaseBlock_append rec_7_14_2369_0_join5 rec_7_14_2369_0_join11 rfl rfl rfl

private theorem rec_7_14_2369_0 : fastPhase (bank 7 14).shape 179798 2369 76 1 0 23 0 = 5503073034256028477715737118 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_7_14_2369_0_join12

private theorem rec_7_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 0 128 = 1235849216106785458904687808 := by decide +kernel
private theorem rec_7_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 128 128 = 1010727903640096677258667200 := by decide +kernel
private theorem rec_7_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 256 128 = 816493626769305249018111168 := by decide +kernel
private theorem rec_7_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 384 128 = 650311494774314969183659200 := by decide +kernel
private theorem rec_7_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 512 128 = 509487213388193111969227968 := by decide +kernel
private theorem rec_7_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 640 128 = 391463759807773455720785088 := by decide +kernel
private theorem rec_7_14_2369_1_part6 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 768 128 = 293818057714687948155685113 := by decide +kernel
private theorem rec_7_14_2369_1_part7 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 896 128 = 214257698860616591145035589 := by decide +kernel
private theorem rec_7_14_2369_1_part8 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 1024 128 = 150617585124344262856080813 := by decide +kernel
private theorem rec_7_14_2369_1_part9 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 1152 128 = 100856423121592451197382874 := by decide +kernel
private theorem rec_7_14_2369_1_part10 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 1280 128 = 63053594494994120528072271 := by decide +kernel
private theorem rec_7_14_2369_1_part11 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 1408 128 = 35405852609379414966140106 := by decide +kernel
private theorem rec_7_14_2369_1_part12 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 1536 128 = 16223985455783429307497502 := by decide +kernel
private theorem rec_7_14_2369_1_part13 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 1664 123 = 3935795417395555903761972 := by decide +kernel
private theorem rec_7_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 128 256 = 1827221530409401926276778368 :=
  phaseBlock_append rec_7_14_2369_1_part1 rec_7_14_2369_1_part2 rfl rfl rfl
private theorem rec_7_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 0 384 = 3063070746516187385181466176 :=
  phaseBlock_append rec_7_14_2369_1_part0 rec_7_14_2369_1_join0 rfl rfl rfl
private theorem rec_7_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 384 256 = 1159798708162508081152887168 :=
  phaseBlock_append rec_7_14_2369_1_part3 rec_7_14_2369_1_part4 rfl rfl rfl
private theorem rec_7_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 640 256 = 685281817522461403876470201 :=
  phaseBlock_append rec_7_14_2369_1_part5 rec_7_14_2369_1_part6 rfl rfl rfl
private theorem rec_7_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 384 512 = 1845080525684969485029357369 :=
  phaseBlock_append rec_7_14_2369_1_join2 rec_7_14_2369_1_join3 rfl rfl rfl
private theorem rec_7_14_2369_1_join5 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 0 896 = 4908151272201156870210823545 :=
  phaseBlock_append rec_7_14_2369_1_join1 rec_7_14_2369_1_join4 rfl rfl rfl
private theorem rec_7_14_2369_1_join6 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 1024 256 = 251474008245936714053463687 :=
  phaseBlock_append rec_7_14_2369_1_part8 rec_7_14_2369_1_part9 rfl rfl rfl
private theorem rec_7_14_2369_1_join7 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 896 384 = 465731707106553305198499276 :=
  phaseBlock_append rec_7_14_2369_1_part7 rec_7_14_2369_1_join6 rfl rfl rfl
private theorem rec_7_14_2369_1_join8 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 1280 256 = 98459447104373535494212377 :=
  phaseBlock_append rec_7_14_2369_1_part10 rec_7_14_2369_1_part11 rfl rfl rfl
private theorem rec_7_14_2369_1_join9 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 1536 251 = 20159780873178985211259474 :=
  phaseBlock_append rec_7_14_2369_1_part12 rec_7_14_2369_1_part13 rfl rfl rfl
private theorem rec_7_14_2369_1_join10 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 1280 507 = 118619227977552520705471851 :=
  phaseBlock_append rec_7_14_2369_1_join8 rec_7_14_2369_1_join9 rfl rfl rfl
private theorem rec_7_14_2369_1_join11 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 896 891 = 584350935084105825903971127 :=
  phaseBlock_append rec_7_14_2369_1_join7 rec_7_14_2369_1_join10 rfl rfl rfl
private theorem rec_7_14_2369_1_join12 :
    phaseBlock (fastLayerG (bank 7 14).shape 179798 2369 76 1 0 23 1) 0 1787 = 5492502207285262696114794672 :=
  phaseBlock_append rec_7_14_2369_1_join5 rec_7_14_2369_1_join11 rfl rfl rfl

private theorem rec_7_14_2369_1 : fastPhase (bank 7 14).shape 179798 2369 76 1 0 23 1 = 5492502207285262696114794672 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_7_14_2369_1_join12

theorem receipt_7_14 : Checked (bank 7 14) 76 0 23 := by
  refine checked_from_values (bank 7 14) 76 0 23
    (P3_7_1.checked (bank 7 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_14_2368_0 rec_7_14_2368_1 rec_7_14_2369_0 rec_7_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 0 128 = 5469227207080520251983087904 := by decide +kernel
private theorem rec_7_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 128 128 = 4716354873177953837275969824 := by decide +kernel
private theorem rec_7_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 256 128 = 4040642271216152799369210144 := by decide +kernel
private theorem rec_7_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 384 128 = 3436851718777161989996337440 := by decide +kernel
private theorem rec_7_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 512 128 = 2899937149865913053505521952 := by decide +kernel
private theorem rec_7_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 640 128 = 2425040790037155781997050144 := by decide +kernel
private theorem rec_7_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 768 128 = 2007489831522389470460799264 := by decide +kernel
private theorem rec_7_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 896 128 = 1642793108356794271913711904 := by decide +kernel
private theorem rec_7_15_2368_0_part8 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1024 128 = 1326637771506162552537270560 := by decide +kernel
private theorem rec_7_15_2368_0_part9 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1152 128 = 1054886011293731927619354345 := by decide +kernel
private theorem rec_7_15_2368_0_part10 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1280 128 = 823571893931267469170153991 := by decide +kernel
private theorem rec_7_15_2368_0_part11 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1408 128 = 628897458109326973260503437 := by decide +kernel
private theorem rec_7_15_2368_0_part12 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1536 128 = 467229652794729188284677535 := by decide +kernel
private theorem rec_7_15_2368_0_part13 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1664 128 = 335097200759414034237759351 := by decide +kernel
private theorem rec_7_15_2368_0_part14 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1792 128 = 229187261548471781534668286 := by decide +kernel
private theorem rec_7_15_2368_0_part15 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1920 128 = 146342094683406123575384016 := by decide +kernel
private theorem rec_7_15_2368_0_part16 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 2048 128 = 83555722756777250587569137 := by decide +kernel
private theorem rec_7_15_2368_0_part17 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 2176 128 = 37970594171456052866494428 := by decide +kernel
private theorem rec_7_15_2368_0_part18 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 2304 99 = 7384456132761340023885837 := by decide +kernel
private theorem rec_7_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 0 256 = 10185582080258474089259057728 :=
  phaseBlock_append rec_7_15_2368_0_part0 rec_7_15_2368_0_part1 rfl rfl rfl
private theorem rec_7_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 256 256 = 7477493989993314789365547584 :=
  phaseBlock_append rec_7_15_2368_0_part2 rec_7_15_2368_0_part3 rfl rfl rfl
private theorem rec_7_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 0 512 = 17663076070251788878624605312 :=
  phaseBlock_append rec_7_15_2368_0_join0 rec_7_15_2368_0_join1 rfl rfl rfl
private theorem rec_7_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 512 256 = 5324977939903068835502572096 :=
  phaseBlock_append rec_7_15_2368_0_part4 rec_7_15_2368_0_part5 rfl rfl rfl
private theorem rec_7_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 896 256 = 2969430879862956824450982464 :=
  phaseBlock_append rec_7_15_2368_0_part7 rec_7_15_2368_0_part8 rfl rfl rfl
private theorem rec_7_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 768 384 = 4976920711385346294911781728 :=
  phaseBlock_append rec_7_15_2368_0_part6 rec_7_15_2368_0_join4 rfl rfl rfl
private theorem rec_7_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 512 640 = 10301898651288415130414353824 :=
  phaseBlock_append rec_7_15_2368_0_join3 rec_7_15_2368_0_join5 rfl rfl rfl
private theorem rec_7_15_2368_0_join7 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 0 1152 = 27964974721540204009038959136 :=
  phaseBlock_append rec_7_15_2368_0_join2 rec_7_15_2368_0_join6 rfl rfl rfl
private theorem rec_7_15_2368_0_join8 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1152 256 = 1878457905224999396789508336 :=
  phaseBlock_append rec_7_15_2368_0_part9 rec_7_15_2368_0_part10 rfl rfl rfl
private theorem rec_7_15_2368_0_join9 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1536 256 = 802326853554143222522436886 :=
  phaseBlock_append rec_7_15_2368_0_part12 rec_7_15_2368_0_part13 rfl rfl rfl
private theorem rec_7_15_2368_0_join10 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1408 384 = 1431224311663470195782940323 :=
  phaseBlock_append rec_7_15_2368_0_part11 rec_7_15_2368_0_join9 rfl rfl rfl
private theorem rec_7_15_2368_0_join11 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1152 640 = 3309682216888469592572448659 :=
  phaseBlock_append rec_7_15_2368_0_join8 rec_7_15_2368_0_join10 rfl rfl rfl
private theorem rec_7_15_2368_0_join12 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1792 256 = 375529356231877905110052302 :=
  phaseBlock_append rec_7_15_2368_0_part14 rec_7_15_2368_0_part15 rfl rfl rfl
private theorem rec_7_15_2368_0_join13 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 2176 227 = 45355050304217392890380265 :=
  phaseBlock_append rec_7_15_2368_0_part17 rec_7_15_2368_0_part18 rfl rfl rfl
private theorem rec_7_15_2368_0_join14 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 2048 355 = 128910773060994643477949402 :=
  phaseBlock_append rec_7_15_2368_0_part16 rec_7_15_2368_0_join13 rfl rfl rfl
private theorem rec_7_15_2368_0_join15 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1792 611 = 504440129292872548588001704 :=
  phaseBlock_append rec_7_15_2368_0_join12 rec_7_15_2368_0_join14 rfl rfl rfl
private theorem rec_7_15_2368_0_join16 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 1152 1251 = 3814122346181342141160450363 :=
  phaseBlock_append rec_7_15_2368_0_join11 rec_7_15_2368_0_join15 rfl rfl rfl
private theorem rec_7_15_2368_0_join17 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 0) 0 2403 = 31779097067721546150199409499 :=
  phaseBlock_append rec_7_15_2368_0_join7 rec_7_15_2368_0_join16 rfl rfl rfl

private theorem rec_7_15_2368_0 : fastPhase (bank 7 15).shape 179798 2368 105 1 0 23 0 = 31779097067721546150199409499 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_7_15_2368_0_join17

private theorem rec_7_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 0 128 = 5463073737286643887841938464 := by decide +kernel
private theorem rec_7_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 128 128 = 4710819620629408463358434336 := by decide +kernel
private theorem rec_7_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 256 128 = 4035684068487154959143283744 := by decide +kernel
private theorem rec_7_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 384 128 = 3432430880522688512797555744 := by decide +kernel
private theorem rec_7_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 512 128 = 2896015447362627991920004128 := by decide +kernel
private theorem rec_7_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 640 128 = 2421581425724337349244541984 := by decide +kernel
private theorem rec_7_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 768 128 = 2004457413542856977777716256 := by decide +kernel
private theorem rec_7_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 896 128 = 1640153625097835065936182304 := by decide +kernel
private theorem rec_7_15_2368_1_part8 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1024 128 = 1324358566140458952684178464 := by decide +kernel
private theorem rec_7_15_2368_1_part9 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1152 128 = 1052935756235892510545176293 := by decide +kernel
private theorem rec_7_15_2368_1_part10 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1280 128 = 821920564954553797211961143 := by decide +kernel
private theorem rec_7_15_2368_1_part11 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1408 128 = 627516309458982428058378162 := by decide +kernel
private theorem rec_7_15_2368_1_part12 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1536 128 = 466091191989128809528321000 := by decide +kernel
private theorem rec_7_15_2368_1_part13 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1664 128 = 334175163074217743612131797 := by decide +kernel
private theorem rec_7_15_2368_1_part14 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1792 128 = 228456584501018295856872858 := by decide +kernel
private theorem rec_7_15_2368_1_part15 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1920 128 = 145778892516731638051946390 := by decide +kernel
private theorem rec_7_15_2368_1_part16 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 2048 128 = 83137260923120733465528940 := by decide +kernel
private theorem rec_7_15_2368_1_part17 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 2176 128 = 37675263816405289189584480 := by decide +kernel
private theorem rec_7_15_2368_1_part18 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 2304 99 = 7227440893251338762008407 := by decide +kernel
private theorem rec_7_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 0 256 = 10173893357916052351200372800 :=
  phaseBlock_append rec_7_15_2368_1_part0 rec_7_15_2368_1_part1 rfl rfl rfl
private theorem rec_7_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 256 256 = 7468114949009843471940839488 :=
  phaseBlock_append rec_7_15_2368_1_part2 rec_7_15_2368_1_part3 rfl rfl rfl
private theorem rec_7_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 0 512 = 17642008306925895823141212288 :=
  phaseBlock_append rec_7_15_2368_1_join0 rec_7_15_2368_1_join1 rfl rfl rfl
private theorem rec_7_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 512 256 = 5317596873086965341164546112 :=
  phaseBlock_append rec_7_15_2368_1_part4 rec_7_15_2368_1_part5 rfl rfl rfl
private theorem rec_7_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 896 256 = 2964512191238294018620360768 :=
  phaseBlock_append rec_7_15_2368_1_part7 rec_7_15_2368_1_part8 rfl rfl rfl
private theorem rec_7_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 768 384 = 4968969604781150996398077024 :=
  phaseBlock_append rec_7_15_2368_1_part6 rec_7_15_2368_1_join4 rfl rfl rfl
private theorem rec_7_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 512 640 = 10286566477868116337562623136 :=
  phaseBlock_append rec_7_15_2368_1_join3 rec_7_15_2368_1_join5 rfl rfl rfl
private theorem rec_7_15_2368_1_join7 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 0 1152 = 27928574784794012160703835424 :=
  phaseBlock_append rec_7_15_2368_1_join2 rec_7_15_2368_1_join6 rfl rfl rfl
private theorem rec_7_15_2368_1_join8 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1152 256 = 1874856321190446307757137436 :=
  phaseBlock_append rec_7_15_2368_1_part9 rec_7_15_2368_1_part10 rfl rfl rfl
private theorem rec_7_15_2368_1_join9 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1536 256 = 800266355063346553140452797 :=
  phaseBlock_append rec_7_15_2368_1_part12 rec_7_15_2368_1_part13 rfl rfl rfl
private theorem rec_7_15_2368_1_join10 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1408 384 = 1427782664522328981198830959 :=
  phaseBlock_append rec_7_15_2368_1_part11 rec_7_15_2368_1_join9 rfl rfl rfl
private theorem rec_7_15_2368_1_join11 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1152 640 = 3302638985712775288955968395 :=
  phaseBlock_append rec_7_15_2368_1_join8 rec_7_15_2368_1_join10 rfl rfl rfl
private theorem rec_7_15_2368_1_join12 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1792 256 = 374235477017749933908819248 :=
  phaseBlock_append rec_7_15_2368_1_part14 rec_7_15_2368_1_part15 rfl rfl rfl
private theorem rec_7_15_2368_1_join13 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 2176 227 = 44902704709656627951592887 :=
  phaseBlock_append rec_7_15_2368_1_part17 rec_7_15_2368_1_part18 rfl rfl rfl
private theorem rec_7_15_2368_1_join14 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 2048 355 = 128039965632777361417121827 :=
  phaseBlock_append rec_7_15_2368_1_part16 rec_7_15_2368_1_join13 rfl rfl rfl
private theorem rec_7_15_2368_1_join15 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1792 611 = 502275442650527295325941075 :=
  phaseBlock_append rec_7_15_2368_1_join12 rec_7_15_2368_1_join14 rfl rfl rfl
private theorem rec_7_15_2368_1_join16 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 1152 1251 = 3804914428363302584281909470 :=
  phaseBlock_append rec_7_15_2368_1_join11 rec_7_15_2368_1_join15 rfl rfl rfl
private theorem rec_7_15_2368_1_join17 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2368 105 1 0 23 1) 0 2403 = 31733489213157314744985744894 :=
  phaseBlock_append rec_7_15_2368_1_join7 rec_7_15_2368_1_join16 rfl rfl rfl

private theorem rec_7_15_2368_1 : fastPhase (bank 7 15).shape 179798 2368 105 1 0 23 1 = 31733489213157314744985744894 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_7_15_2368_1_join17

private theorem rec_7_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 0 128 = 5469276755852337974056511776 := by decide +kernel
private theorem rec_7_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 128 128 = 4716396267642745794975971616 := by decide +kernel
private theorem rec_7_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 256 128 = 4040676572456445611073046816 := by decide +kernel
private theorem rec_7_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 384 128 = 3436879888051673888319330592 := by decide +kernel
private theorem rec_7_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 512 128 = 2899960054282158707729246496 := by decide +kernel
private theorem rec_7_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 640 128 = 2425059208107722790278822176 := by decide +kernel
private theorem rec_7_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 768 128 = 2007504458604886521824463136 := by decide +kernel
private theorem rec_7_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 896 128 = 1642804561977470978021726496 := by decide +kernel
private theorem rec_7_15_2369_0_part8 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1024 128 = 1326646596567200949244094752 := by decide +kernel
private theorem rec_7_15_2369_0_part9 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1152 128 = 1054892682791617653381467329 := by decide +kernel
private theorem rec_7_15_2369_0_part10 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1280 128 = 823576823799742600097325612 := by decide +kernel
private theorem rec_7_15_2369_0_part11 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1408 128 = 628901006115306553678718971 := by decide +kernel
private theorem rec_7_15_2369_0_part12 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1536 128 = 467232125211746878807007158 := by decide +kernel
private theorem rec_7_15_2369_0_part13 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1664 128 = 335098854774143157002628740 := by decide +kernel
private theorem rec_7_15_2369_0_part14 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1792 128 = 229188309961421728497625964 := by decide +kernel
private theorem rec_7_15_2369_0_part15 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1920 128 = 146342710444258221426487487 := by decide +kernel
private theorem rec_7_15_2369_0_part16 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 2048 128 = 83556043326568898101567424 := by decide +kernel
private theorem rec_7_15_2369_0_part17 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 2176 128 = 37970725766965495071639898 := by decide +kernel
private theorem rec_7_15_2369_0_part18 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 2304 99 = 7384479335004396062760225 := by decide +kernel
private theorem rec_7_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 0 256 = 10185673023495083769032483392 :=
  phaseBlock_append rec_7_15_2369_0_part0 rec_7_15_2369_0_part1 rfl rfl rfl
private theorem rec_7_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 256 256 = 7477556460508119499392377408 :=
  phaseBlock_append rec_7_15_2369_0_part2 rec_7_15_2369_0_part3 rfl rfl rfl
private theorem rec_7_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 0 512 = 17663229484003203268424860800 :=
  phaseBlock_append rec_7_15_2369_0_join0 rec_7_15_2369_0_join1 rfl rfl rfl
private theorem rec_7_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 512 256 = 5325019262389881498008068672 :=
  phaseBlock_append rec_7_15_2369_0_part4 rec_7_15_2369_0_part5 rfl rfl rfl
private theorem rec_7_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 896 256 = 2969451158544671927265821248 :=
  phaseBlock_append rec_7_15_2369_0_part7 rec_7_15_2369_0_part8 rfl rfl rfl
private theorem rec_7_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 768 384 = 4976955617149558449090284384 :=
  phaseBlock_append rec_7_15_2369_0_part6 rec_7_15_2369_0_join4 rfl rfl rfl
private theorem rec_7_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 512 640 = 10301974879539439947098353056 :=
  phaseBlock_append rec_7_15_2369_0_join3 rec_7_15_2369_0_join5 rfl rfl rfl
private theorem rec_7_15_2369_0_join7 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 0 1152 = 27965204363542643215523213856 :=
  phaseBlock_append rec_7_15_2369_0_join2 rec_7_15_2369_0_join6 rfl rfl rfl
private theorem rec_7_15_2369_0_join8 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1152 256 = 1878469506591360253478792941 :=
  phaseBlock_append rec_7_15_2369_0_part9 rec_7_15_2369_0_part10 rfl rfl rfl
private theorem rec_7_15_2369_0_join9 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1536 256 = 802330979985890035809635898 :=
  phaseBlock_append rec_7_15_2369_0_part12 rec_7_15_2369_0_part13 rfl rfl rfl
private theorem rec_7_15_2369_0_join10 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1408 384 = 1431231986101196589488354869 :=
  phaseBlock_append rec_7_15_2369_0_part11 rec_7_15_2369_0_join9 rfl rfl rfl
private theorem rec_7_15_2369_0_join11 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1152 640 = 3309701492692556842967147810 :=
  phaseBlock_append rec_7_15_2369_0_join8 rec_7_15_2369_0_join10 rfl rfl rfl
private theorem rec_7_15_2369_0_join12 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1792 256 = 375531020405679949924113451 :=
  phaseBlock_append rec_7_15_2369_0_part14 rec_7_15_2369_0_part15 rfl rfl rfl
private theorem rec_7_15_2369_0_join13 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 2176 227 = 45355205101969891134400123 :=
  phaseBlock_append rec_7_15_2369_0_part17 rec_7_15_2369_0_part18 rfl rfl rfl
private theorem rec_7_15_2369_0_join14 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 2048 355 = 128911248428538789235967547 :=
  phaseBlock_append rec_7_15_2369_0_part16 rec_7_15_2369_0_join13 rfl rfl rfl
private theorem rec_7_15_2369_0_join15 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1792 611 = 504442268834218739160080998 :=
  phaseBlock_append rec_7_15_2369_0_join12 rec_7_15_2369_0_join14 rfl rfl rfl
private theorem rec_7_15_2369_0_join16 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 1152 1251 = 3814143761526775582127228808 :=
  phaseBlock_append rec_7_15_2369_0_join11 rec_7_15_2369_0_join15 rfl rfl rfl
private theorem rec_7_15_2369_0_join17 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 0) 0 2403 = 31779348125069418797650442664 :=
  phaseBlock_append rec_7_15_2369_0_join7 rec_7_15_2369_0_join16 rfl rfl rfl

private theorem rec_7_15_2369_0 : fastPhase (bank 7 15).shape 179798 2369 105 1 0 23 0 = 31779348125069418797650442664 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_7_15_2369_0_join17

private theorem rec_7_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 0 128 = 5463123235392288838931473376 := by decide +kernel
private theorem rec_7_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 128 128 = 4710860970842174493500142560 := by decide +kernel
private theorem rec_7_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 256 128 = 4035718331299901592771789792 := by decide +kernel
private theorem rec_7_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 384 128 = 3432459016637491364034024416 := by decide +kernel
private theorem rec_7_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 512 128 = 2896038323362692887539655648 := by decide +kernel
private theorem rec_7_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 640 128 = 2421599819629586121425466336 := by decide +kernel
private theorem rec_7_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 768 128 = 2004472020249184926630986720 := by decide +kernel
private theorem rec_7_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 896 128 = 1640165061700040091817268192 := by decide +kernel
private theorem rec_7_15_2369_1_part8 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1024 128 = 1324367377138842358285657056 := by decide +kernel
private theorem rec_7_15_2369_1_part9 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1152 128 = 1052942416258146380667172580 := by decide +kernel
private theorem rec_7_15_2369_1_part10 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1280 128 = 821925485595701851865573877 := by decide +kernel
private theorem rec_7_15_2369_1_part11 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1408 128 = 627519850165169429199211461 := by decide +kernel
private theorem rec_7_15_2369_1_part12 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1536 128 = 466093658740084192537757552 := by decide +kernel
private theorem rec_7_15_2369_1_part13 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1664 128 = 334176812789679654669769558 := by decide +kernel
private theorem rec_7_15_2369_1_part14 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1792 128 = 228457629740586244983624875 := by decide +kernel
private theorem rec_7_15_2369_1_part15 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1920 128 = 145779506014387673649408436 := by decide +kernel
private theorem rec_7_15_2369_1_part16 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 2048 128 = 83137579948704001694585838 := by decide +kernel
private theorem rec_7_15_2369_1_part17 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 2176 128 = 37675394419307644992664067 := by decide +kernel
private theorem rec_7_15_2369_1_part18 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 2304 99 = 7227463613754687031419250 := by decide +kernel
private theorem rec_7_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 0 256 = 10173984206234463332431615936 :=
  phaseBlock_append rec_7_15_2369_1_part0 rec_7_15_2369_1_part1 rfl rfl rfl
private theorem rec_7_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 256 256 = 7468177347937392956805814208 :=
  phaseBlock_append rec_7_15_2369_1_part2 rec_7_15_2369_1_part3 rfl rfl rfl
private theorem rec_7_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 0 512 = 17642161554171856289237430144 :=
  phaseBlock_append rec_7_15_2369_1_join0 rec_7_15_2369_1_join1 rfl rfl rfl
private theorem rec_7_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 512 256 = 5317638142992279008965121984 :=
  phaseBlock_append rec_7_15_2369_1_part4 rec_7_15_2369_1_part5 rfl rfl rfl
private theorem rec_7_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 896 256 = 2964532438838882450102925248 :=
  phaseBlock_append rec_7_15_2369_1_part7 rec_7_15_2369_1_part8 rfl rfl rfl
private theorem rec_7_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 768 384 = 4969004459088067376733911968 :=
  phaseBlock_append rec_7_15_2369_1_part6 rec_7_15_2369_1_join4 rfl rfl rfl
private theorem rec_7_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 512 640 = 10286642602080346385699033952 :=
  phaseBlock_append rec_7_15_2369_1_join3 rec_7_15_2369_1_join5 rfl rfl rfl
private theorem rec_7_15_2369_1_join7 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 0 1152 = 27928804156252202674936464096 :=
  phaseBlock_append rec_7_15_2369_1_join2 rec_7_15_2369_1_join6 rfl rfl rfl
private theorem rec_7_15_2369_1_join8 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1152 256 = 1874867901853848232532746457 :=
  phaseBlock_append rec_7_15_2369_1_part9 rec_7_15_2369_1_part10 rfl rfl rfl
private theorem rec_7_15_2369_1_join9 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1536 256 = 800270471529763847207527110 :=
  phaseBlock_append rec_7_15_2369_1_part12 rec_7_15_2369_1_part13 rfl rfl rfl
private theorem rec_7_15_2369_1_join10 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1408 384 = 1427790321694933276406738571 :=
  phaseBlock_append rec_7_15_2369_1_part11 rec_7_15_2369_1_join9 rfl rfl rfl
private theorem rec_7_15_2369_1_join11 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1152 640 = 3302658223548781508939485028 :=
  phaseBlock_append rec_7_15_2369_1_join8 rec_7_15_2369_1_join10 rfl rfl rfl
private theorem rec_7_15_2369_1_join12 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1792 256 = 374237135754973918633033311 :=
  phaseBlock_append rec_7_15_2369_1_part14 rec_7_15_2369_1_part15 rfl rfl rfl
private theorem rec_7_15_2369_1_join13 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 2176 227 = 44902858033062332024083317 :=
  phaseBlock_append rec_7_15_2369_1_part17 rec_7_15_2369_1_part18 rfl rfl rfl
private theorem rec_7_15_2369_1_join14 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 2048 355 = 128040437981766333718669155 :=
  phaseBlock_append rec_7_15_2369_1_part16 rec_7_15_2369_1_join13 rfl rfl rfl
private theorem rec_7_15_2369_1_join15 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1792 611 = 502277573736740252351702466 :=
  phaseBlock_append rec_7_15_2369_1_join12 rec_7_15_2369_1_join14 rfl rfl rfl
private theorem rec_7_15_2369_1_join16 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 1152 1251 = 3804935797285521761291187494 :=
  phaseBlock_append rec_7_15_2369_1_join11 rec_7_15_2369_1_join15 rfl rfl rfl
private theorem rec_7_15_2369_1_join17 :
    phaseBlock (fastLayerG (bank 7 15).shape 179798 2369 105 1 0 23 1) 0 2403 = 31733739953537724436227651590 :=
  phaseBlock_append rec_7_15_2369_1_join7 rec_7_15_2369_1_join16 rfl rfl rfl

private theorem rec_7_15_2369_1 : fastPhase (bank 7 15).shape 179798 2369 105 1 0 23 1 = 31733739953537724436227651590 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_7_15_2369_1_join17

theorem receipt_7_15 : Checked (bank 7 15) 105 0 23 := by
  refine checked_from_values (bank 7 15) 105 0 23
    (P3_7_1.checked (bank 7 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_10849_2402)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_15_2368_0 rec_7_15_2368_1 rec_7_15_2369_0 rec_7_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_7_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 0 128 = 21807818202882879054204014944 := by decide +kernel
private theorem rec_7_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 128 128 = 19488261107744177982319714656 := by decide +kernel
private theorem rec_7_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 256 128 = 17351206070717981826395943264 := by decide +kernel
private theorem rec_7_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 384 128 = 15387233272220686001298669920 := by decide +kernel
private theorem rec_7_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 512 128 = 13587180909334217918636478816 := by decide +kernel
private theorem rec_7_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 640 128 = 11942141870932968341898043744 := by decide +kernel
private theorem rec_7_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 768 128 = 10443460412810722741589602656 := by decide +kernel
private theorem rec_7_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 896 128 = 9082728832807592650372432224 := by decide +kernel
private theorem rec_7_16_2368_0_part8 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1024 128 = 7851784145936947018200322400 := by decide +kernel
private theorem rec_7_16_2368_0_part9 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1152 128 = 6742704759512343567457050976 := by decide +kernel
private theorem rec_7_16_2368_0_part10 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1280 128 = 5747807148274460148093858144 := by decide +kernel
private theorem rec_7_16_2368_0_part11 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1408 128 = 4859642529518026092766921056 := by decide +kernel
private theorem rec_7_16_2368_0_part12 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1536 128 = 4070993601301163129726530063 := by decide +kernel
private theorem rec_7_16_2368_0_part13 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1664 128 = 3374871652564301935700927130 := by decide +kernel
private theorem rec_7_16_2368_0_part14 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1792 128 = 2764512154901666899360609243 := by decide +kernel
private theorem rec_7_16_2368_0_part15 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1920 128 = 2233371632092862499901998705 := by decide +kernel
private theorem rec_7_16_2368_0_part16 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2048 128 = 1775124831566608502444155426 := by decide +kernel
private theorem rec_7_16_2368_0_part17 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2176 128 = 1383661393657668285518725727 := by decide +kernel
private theorem rec_7_16_2368_0_part18 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2304 128 = 1053082513583351329965893422 := by decide +kernel
private theorem rec_7_16_2368_0_part19 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2432 128 = 777697604541463675323277606 := by decide +kernel
private theorem rec_7_16_2368_0_part20 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2560 128 = 552020960996212678981291095 := by decide +kernel
private theorem rec_7_16_2368_0_part21 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2688 128 = 370768421595546296242439156 := by decide +kernel
private theorem rec_7_16_2368_0_part22 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2816 128 = 228854031873635844833005479 := by decide +kernel
private theorem rec_7_16_2368_0_part23 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2944 128 = 121386707401102146123425578 := by decide +kernel
private theorem rec_7_16_2368_0_part24 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 3072 128 = 43666896803139263479884630 := by decide +kernel
private theorem rec_7_16_2368_0_part25 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 3200 35 = 1843721428514968764831387 := by decide +kernel
private theorem rec_7_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 128 256 = 36839467178462159808715657920 :=
  phaseBlock_append rec_7_16_2368_0_part1 rec_7_16_2368_0_part2 rfl rfl rfl
private theorem rec_7_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 0 384 = 58647285381345038862919672864 :=
  phaseBlock_append rec_7_16_2368_0_part0 rec_7_16_2368_0_join0 rfl rfl rfl
private theorem rec_7_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 512 256 = 25529322780267186260534522560 :=
  phaseBlock_append rec_7_16_2368_0_part4 rec_7_16_2368_0_part5 rfl rfl rfl
private theorem rec_7_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 384 384 = 40916556052487872261833192480 :=
  phaseBlock_append rec_7_16_2368_0_part3 rec_7_16_2368_0_join2 rfl rfl rfl
private theorem rec_7_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 0 768 = 99563841433832911124752865344 :=
  phaseBlock_append rec_7_16_2368_0_join1 rec_7_16_2368_0_join3 rfl rfl rfl
private theorem rec_7_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 896 256 = 16934512978744539668572754624 :=
  phaseBlock_append rec_7_16_2368_0_part7 rec_7_16_2368_0_part8 rfl rfl rfl
private theorem rec_7_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 768 384 = 27377973391555262410162357280 :=
  phaseBlock_append rec_7_16_2368_0_part6 rec_7_16_2368_0_join5 rfl rfl rfl
private theorem rec_7_16_2368_0_join7 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1152 256 = 12490511907786803715550909120 :=
  phaseBlock_append rec_7_16_2368_0_part9 rec_7_16_2368_0_part10 rfl rfl rfl
private theorem rec_7_16_2368_0_join8 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1408 256 = 8930636130819189222493451119 :=
  phaseBlock_append rec_7_16_2368_0_part11 rec_7_16_2368_0_part12 rfl rfl rfl
private theorem rec_7_16_2368_0_join9 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1152 512 = 21421148038605992938044360239 :=
  phaseBlock_append rec_7_16_2368_0_join7 rec_7_16_2368_0_join8 rfl rfl rfl
private theorem rec_7_16_2368_0_join10 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 768 896 = 48799121430161255348206717519 :=
  phaseBlock_append rec_7_16_2368_0_join6 rec_7_16_2368_0_join9 rfl rfl rfl
private theorem rec_7_16_2368_0_join11 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 0 1664 = 148362962863994166472959582863 :=
  phaseBlock_append rec_7_16_2368_0_join4 rec_7_16_2368_0_join10 rfl rfl rfl
private theorem rec_7_16_2368_0_join12 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1792 256 = 4997883786994529399262607948 :=
  phaseBlock_append rec_7_16_2368_0_part14 rec_7_16_2368_0_part15 rfl rfl rfl
private theorem rec_7_16_2368_0_join13 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1664 384 = 8372755439558831334963535078 :=
  phaseBlock_append rec_7_16_2368_0_part13 rec_7_16_2368_0_join12 rfl rfl rfl
private theorem rec_7_16_2368_0_join14 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2176 256 = 2436743907241019615484619149 :=
  phaseBlock_append rec_7_16_2368_0_part17 rec_7_16_2368_0_part18 rfl rfl rfl
private theorem rec_7_16_2368_0_join15 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2048 384 = 4211868738807628117928774575 :=
  phaseBlock_append rec_7_16_2368_0_part16 rec_7_16_2368_0_join14 rfl rfl rfl
private theorem rec_7_16_2368_0_join16 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1664 768 = 12584624178366459452892309653 :=
  phaseBlock_append rec_7_16_2368_0_join13 rec_7_16_2368_0_join15 rfl rfl rfl
private theorem rec_7_16_2368_0_join17 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2560 256 = 922789382591758975223730251 :=
  phaseBlock_append rec_7_16_2368_0_part20 rec_7_16_2368_0_part21 rfl rfl rfl
private theorem rec_7_16_2368_0_join18 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2432 384 = 1700486987133222650547007857 :=
  phaseBlock_append rec_7_16_2368_0_part19 rec_7_16_2368_0_join17 rfl rfl rfl
private theorem rec_7_16_2368_0_join19 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2816 256 = 350240739274737990956431057 :=
  phaseBlock_append rec_7_16_2368_0_part22 rec_7_16_2368_0_part23 rfl rfl rfl
private theorem rec_7_16_2368_0_join20 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 3072 163 = 45510618231654232244716017 :=
  phaseBlock_append rec_7_16_2368_0_part24 rec_7_16_2368_0_part25 rfl rfl rfl
private theorem rec_7_16_2368_0_join21 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2816 419 = 395751357506392223201147074 :=
  phaseBlock_append rec_7_16_2368_0_join19 rec_7_16_2368_0_join20 rfl rfl rfl
private theorem rec_7_16_2368_0_join22 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 2432 803 = 2096238344639614873748154931 :=
  phaseBlock_append rec_7_16_2368_0_join18 rec_7_16_2368_0_join21 rfl rfl rfl
private theorem rec_7_16_2368_0_join23 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 1664 1571 = 14680862523006074326640464584 :=
  phaseBlock_append rec_7_16_2368_0_join16 rec_7_16_2368_0_join22 rfl rfl rfl
private theorem rec_7_16_2368_0_join24 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 0) 0 3235 = 163043825387000240799600047447 :=
  phaseBlock_append rec_7_16_2368_0_join11 rec_7_16_2368_0_join23 rfl rfl rfl

private theorem rec_7_16_2368_0 : fastPhase (bank 7 16).shape 179798 2368 138 1 0 23 0 = 163043825387000240799600047447 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_7_16_2368_0_join24

private theorem rec_7_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 0 128 = 21789086688979344139885707232 := by decide +kernel
private theorem rec_7_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 128 128 = 19470980233923139954455621600 := by decide +kernel
private theorem rec_7_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 256 128 = 17335302120713770211681558496 := by decide +kernel
private theorem rec_7_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 384 128 = 15372634521159113769459748832 := by decide +kernel
private theorem rec_7_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 512 128 = 13573817598273508419812081632 := by decide +kernel
private theorem rec_7_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 640 128 = 11929946181404682244023578592 := by decide +kernel
private theorem rec_7_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 768 128 = 10432366441360684967779868640 := by decide +kernel
private theorem rec_7_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 896 128 = 9072672565536819316304662496 := by decide +kernel
private theorem rec_7_16_2368_1_part8 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1024 128 = 7842703433042572369497227232 := by decide +kernel
private theorem rec_7_16_2368_1_part9 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1152 128 = 6734539289828546917069860832 := by decide +kernel
private theorem rec_7_16_2368_1_part10 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1280 128 = 5740498423813392813685366752 := by decide +kernel
private theorem rec_7_16_2368_1_part11 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1408 128 = 4853133840010738334094528480 := by decide +kernel
private theorem rec_7_16_2368_1_part12 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1536 128 = 4065229998652499211317867882 := by decide +kernel
private theorem rec_7_16_2368_1_part13 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1664 128 = 3369799924662834196284893935 := by decide +kernel
private theorem rec_7_16_2368_1_part14 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1792 128 = 2760080800831960826500574643 := by decide +kernel
private theorem rec_7_16_2368_1_part15 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1920 128 = 2229530837256592975530300414 := by decide +kernel
private theorem rec_7_16_2368_1_part16 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2048 128 = 1771826442173905247056956602 := by decide +kernel
private theorem rec_7_16_2368_1_part17 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2176 128 = 1380858891209942019826960272 := by decide +kernel
private theorem rec_7_16_2368_1_part18 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2304 128 = 1050730989357614543119461721 := by decide +kernel
private theorem rec_7_16_2368_1_part19 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2432 128 = 775753734074631457142776896 := by decide +kernel
private theorem rec_7_16_2368_1_part20 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2560 128 = 550442978568801888781589484 := by decide +kernel
private theorem rec_7_16_2368_1_part21 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2688 128 = 369516094715271579241907999 := by decide +kernel
private theorem rec_7_16_2368_1_part22 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2816 128 = 227888635759716900855425008 := by decide +kernel
private theorem rec_7_16_2368_1_part23 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2944 128 = 120670999468236619043422704 := by decide +kernel
private theorem rec_7_16_2368_1_part24 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 3072 128 = 43165091145102574092361692 := by decide +kernel
private theorem rec_7_16_2368_1_part25 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 3200 35 = 1739183356687828517280216 := by decide +kernel
private theorem rec_7_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 128 256 = 36806282354636910166137180096 :=
  phaseBlock_append rec_7_16_2368_1_part1 rec_7_16_2368_1_part2 rfl rfl rfl
private theorem rec_7_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 0 384 = 58595369043616254306022887328 :=
  phaseBlock_append rec_7_16_2368_1_part0 rec_7_16_2368_1_join0 rfl rfl rfl
private theorem rec_7_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 512 256 = 25503763779678190663835660224 :=
  phaseBlock_append rec_7_16_2368_1_part4 rec_7_16_2368_1_part5 rfl rfl rfl
private theorem rec_7_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 384 384 = 40876398300837304433295409056 :=
  phaseBlock_append rec_7_16_2368_1_part3 rec_7_16_2368_1_join2 rfl rfl rfl
private theorem rec_7_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 0 768 = 99471767344453558739318296384 :=
  phaseBlock_append rec_7_16_2368_1_join1 rec_7_16_2368_1_join3 rfl rfl rfl
private theorem rec_7_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 896 256 = 16915375998579391685801889728 :=
  phaseBlock_append rec_7_16_2368_1_part7 rec_7_16_2368_1_part8 rfl rfl rfl
private theorem rec_7_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 768 384 = 27347742439940076653581758368 :=
  phaseBlock_append rec_7_16_2368_1_part6 rec_7_16_2368_1_join5 rfl rfl rfl
private theorem rec_7_16_2368_1_join7 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1152 256 = 12475037713641939730755227584 :=
  phaseBlock_append rec_7_16_2368_1_part9 rec_7_16_2368_1_part10 rfl rfl rfl
private theorem rec_7_16_2368_1_join8 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1408 256 = 8918363838663237545412396362 :=
  phaseBlock_append rec_7_16_2368_1_part11 rec_7_16_2368_1_part12 rfl rfl rfl
private theorem rec_7_16_2368_1_join9 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1152 512 = 21393401552305177276167623946 :=
  phaseBlock_append rec_7_16_2368_1_join7 rec_7_16_2368_1_join8 rfl rfl rfl
private theorem rec_7_16_2368_1_join10 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 768 896 = 48741143992245253929749382314 :=
  phaseBlock_append rec_7_16_2368_1_join6 rec_7_16_2368_1_join9 rfl rfl rfl
private theorem rec_7_16_2368_1_join11 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 0 1664 = 148212911336698812669067678698 :=
  phaseBlock_append rec_7_16_2368_1_join4 rec_7_16_2368_1_join10 rfl rfl rfl
private theorem rec_7_16_2368_1_join12 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1792 256 = 4989611638088553802030875057 :=
  phaseBlock_append rec_7_16_2368_1_part14 rec_7_16_2368_1_part15 rfl rfl rfl
private theorem rec_7_16_2368_1_join13 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1664 384 = 8359411562751387998315768992 :=
  phaseBlock_append rec_7_16_2368_1_part13 rec_7_16_2368_1_join12 rfl rfl rfl
private theorem rec_7_16_2368_1_join14 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2176 256 = 2431589880567556562946421993 :=
  phaseBlock_append rec_7_16_2368_1_part17 rec_7_16_2368_1_part18 rfl rfl rfl
private theorem rec_7_16_2368_1_join15 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2048 384 = 4203416322741461810003378595 :=
  phaseBlock_append rec_7_16_2368_1_part16 rec_7_16_2368_1_join14 rfl rfl rfl
private theorem rec_7_16_2368_1_join16 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1664 768 = 12562827885492849808319147587 :=
  phaseBlock_append rec_7_16_2368_1_join13 rec_7_16_2368_1_join15 rfl rfl rfl
private theorem rec_7_16_2368_1_join17 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2560 256 = 919959073284073468023497483 :=
  phaseBlock_append rec_7_16_2368_1_part20 rec_7_16_2368_1_part21 rfl rfl rfl
private theorem rec_7_16_2368_1_join18 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2432 384 = 1695712807358704925166274379 :=
  phaseBlock_append rec_7_16_2368_1_part19 rec_7_16_2368_1_join17 rfl rfl rfl
private theorem rec_7_16_2368_1_join19 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2816 256 = 348559635227953519898847712 :=
  phaseBlock_append rec_7_16_2368_1_part22 rec_7_16_2368_1_part23 rfl rfl rfl
private theorem rec_7_16_2368_1_join20 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 3072 163 = 44904274501790402609641908 :=
  phaseBlock_append rec_7_16_2368_1_part24 rec_7_16_2368_1_part25 rfl rfl rfl
private theorem rec_7_16_2368_1_join21 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2816 419 = 393463909729743922508489620 :=
  phaseBlock_append rec_7_16_2368_1_join19 rec_7_16_2368_1_join20 rfl rfl rfl
private theorem rec_7_16_2368_1_join22 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 2432 803 = 2089176717088448847674763999 :=
  phaseBlock_append rec_7_16_2368_1_join18 rec_7_16_2368_1_join21 rfl rfl rfl
private theorem rec_7_16_2368_1_join23 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 1664 1571 = 14652004602581298655993911586 :=
  phaseBlock_append rec_7_16_2368_1_join16 rec_7_16_2368_1_join22 rfl rfl rfl
private theorem rec_7_16_2368_1_join24 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2368 138 1 0 23 1) 0 3235 = 162864915939280111325061590284 :=
  phaseBlock_append rec_7_16_2368_1_join11 rec_7_16_2368_1_join23 rfl rfl rfl

private theorem rec_7_16_2368_1 : fastPhase (bank 7 16).shape 179798 2368 138 1 0 23 1 = 162864915939280111325061590284 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_7_16_2368_1_join24

private theorem rec_7_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 0 128 = 21808016713855541824111549152 := by decide +kernel
private theorem rec_7_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 128 128 = 19488434428675801424772713184 := by decide +kernel
private theorem rec_7_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 256 128 = 17351356709467683214874311392 := by decide +kernel
private theorem rec_7_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 384 128 = 15387363557689756417253059296 := by decide +kernel
private theorem rec_7_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 512 128 = 13587292999105722177365301984 := by decide +kernel
private theorem rec_7_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 640 128 = 11942237758795016588205787872 := by decide +kernel
private theorem rec_7_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 768 128 = 10443541936163413715226442464 := by decide +kernel
private theorem rec_7_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 896 128 = 9082797679953628621255142112 := by decide +kernel
private theorem rec_7_16_2369_0_part8 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1024 128 = 7851841863255920391414487776 := by decide +kernel
private theorem rec_7_16_2369_0_part9 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1152 128 = 6742752758518695158040578784 := by decide +kernel
private theorem rec_7_16_2369_0_part10 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1280 128 = 5747846712559109125601786592 := by decide +kernel
private theorem rec_7_16_2369_0_part11 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1408 128 = 4859674821573671595617528544 := by decide +kernel
private theorem rec_7_16_2369_0_part12 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1536 128 = 4071019664274628825398296307 := by decide +kernel
private theorem rec_7_16_2369_0_part13 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1664 128 = 3374892415286950244881808755 := by decide +kernel
private theorem rec_7_16_2369_0_part14 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1792 128 = 2764528462171059914264195112 := by decide +kernel
private theorem rec_7_16_2369_0_part15 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1920 128 = 2233384233242485662596789160 := by decide +kernel
private theorem rec_7_16_2369_0_part16 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2048 128 = 1775134386025399272233395254 := by decide +kernel
private theorem rec_7_16_2369_0_part17 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2176 128 = 1383668477198504637334523757 := by decide +kernel
private theorem rec_7_16_2369_0_part18 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2304 128 = 1053087624359899383673404747 := by decide +kernel
private theorem rec_7_16_2369_0_part19 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2432 128 = 777701169195093247371420249 := by decide +kernel
private theorem rec_7_16_2369_0_part20 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2560 128 = 552023340710037491449691781 := by decide +kernel
private theorem rec_7_16_2369_0_part21 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2688 128 = 370769917716641372922234027 := by decide +kernel
private theorem rec_7_16_2369_0_part22 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2816 128 = 228854891645277070882582950 := by decide +kernel
private theorem rec_7_16_2369_0_part23 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2944 128 = 121387129526043438318601458 := by decide +kernel
private theorem rec_7_16_2369_0_part24 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 3072 128 = 43667036833629909294612600 := by decide +kernel
private theorem rec_7_16_2369_0_part25 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 3200 35 = 1843726957921533939129582 := by decide +kernel
private theorem rec_7_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 128 256 = 36839791138143484639647024576 :=
  phaseBlock_append rec_7_16_2369_0_part1 rec_7_16_2369_0_part2 rfl rfl rfl
private theorem rec_7_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 0 384 = 58647807851999026463758573728 :=
  phaseBlock_append rec_7_16_2369_0_part0 rec_7_16_2369_0_join0 rfl rfl rfl
private theorem rec_7_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 512 256 = 25529530757900738765571089856 :=
  phaseBlock_append rec_7_16_2369_0_part4 rec_7_16_2369_0_part5 rfl rfl rfl
private theorem rec_7_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 384 384 = 40916894315590495182824149152 :=
  phaseBlock_append rec_7_16_2369_0_part3 rec_7_16_2369_0_join2 rfl rfl rfl
private theorem rec_7_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 0 768 = 99564702167589521646582722880 :=
  phaseBlock_append rec_7_16_2369_0_join1 rec_7_16_2369_0_join3 rfl rfl rfl
private theorem rec_7_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 896 256 = 16934639543209549012669629888 :=
  phaseBlock_append rec_7_16_2369_0_part7 rec_7_16_2369_0_part8 rfl rfl rfl
private theorem rec_7_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 768 384 = 27378181479372962727896072352 :=
  phaseBlock_append rec_7_16_2369_0_part6 rec_7_16_2369_0_join5 rfl rfl rfl
private theorem rec_7_16_2369_0_join7 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1152 256 = 12490599471077804283642365376 :=
  phaseBlock_append rec_7_16_2369_0_part9 rec_7_16_2369_0_part10 rfl rfl rfl
private theorem rec_7_16_2369_0_join8 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1408 256 = 8930694485848300421015824851 :=
  phaseBlock_append rec_7_16_2369_0_part11 rec_7_16_2369_0_part12 rfl rfl rfl
private theorem rec_7_16_2369_0_join9 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1152 512 = 21421293956926104704658190227 :=
  phaseBlock_append rec_7_16_2369_0_join7 rec_7_16_2369_0_join8 rfl rfl rfl
private theorem rec_7_16_2369_0_join10 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 768 896 = 48799475436299067432554262579 :=
  phaseBlock_append rec_7_16_2369_0_join6 rec_7_16_2369_0_join9 rfl rfl rfl
private theorem rec_7_16_2369_0_join11 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 0 1664 = 148364177603888589079136985459 :=
  phaseBlock_append rec_7_16_2369_0_join4 rec_7_16_2369_0_join10 rfl rfl rfl
private theorem rec_7_16_2369_0_join12 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1792 256 = 4997912695413545576860984272 :=
  phaseBlock_append rec_7_16_2369_0_part14 rec_7_16_2369_0_part15 rfl rfl rfl
private theorem rec_7_16_2369_0_join13 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1664 384 = 8372805110700495821742793027 :=
  phaseBlock_append rec_7_16_2369_0_part13 rec_7_16_2369_0_join12 rfl rfl rfl
private theorem rec_7_16_2369_0_join14 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2176 256 = 2436756101558404021007928504 :=
  phaseBlock_append rec_7_16_2369_0_part17 rec_7_16_2369_0_part18 rfl rfl rfl
private theorem rec_7_16_2369_0_join15 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2048 384 = 4211890487583803293241323758 :=
  phaseBlock_append rec_7_16_2369_0_part16 rec_7_16_2369_0_join14 rfl rfl rfl
private theorem rec_7_16_2369_0_join16 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1664 768 = 12584695598284299114984116785 :=
  phaseBlock_append rec_7_16_2369_0_join13 rec_7_16_2369_0_join15 rfl rfl rfl
private theorem rec_7_16_2369_0_join17 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2560 256 = 922793258426678864371925808 :=
  phaseBlock_append rec_7_16_2369_0_part20 rec_7_16_2369_0_part21 rfl rfl rfl
private theorem rec_7_16_2369_0_join18 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2432 384 = 1700494427621772111743346057 :=
  phaseBlock_append rec_7_16_2369_0_part19 rec_7_16_2369_0_join17 rfl rfl rfl
private theorem rec_7_16_2369_0_join19 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2816 256 = 350242021171320509201184408 :=
  phaseBlock_append rec_7_16_2369_0_part22 rec_7_16_2369_0_part23 rfl rfl rfl
private theorem rec_7_16_2369_0_join20 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 3072 163 = 45510763791551443233742182 :=
  phaseBlock_append rec_7_16_2369_0_part24 rec_7_16_2369_0_part25 rfl rfl rfl
private theorem rec_7_16_2369_0_join21 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2816 419 = 395752784962871952434926590 :=
  phaseBlock_append rec_7_16_2369_0_join19 rec_7_16_2369_0_join20 rfl rfl rfl
private theorem rec_7_16_2369_0_join22 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 2432 803 = 2096247212584644064178272647 :=
  phaseBlock_append rec_7_16_2369_0_join18 rec_7_16_2369_0_join21 rfl rfl rfl
private theorem rec_7_16_2369_0_join23 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 1664 1571 = 14680942810868943179162389432 :=
  phaseBlock_append rec_7_16_2369_0_join16 rec_7_16_2369_0_join22 rfl rfl rfl
private theorem rec_7_16_2369_0_join24 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 0) 0 3235 = 163045120414757532258299374891 :=
  phaseBlock_append rec_7_16_2369_0_join11 rec_7_16_2369_0_join23 rfl rfl rfl

private theorem rec_7_16_2369_0 : fastPhase (bank 7 16).shape 179798 2369 138 1 0 23 0 = 163045120414757532258299374891 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_7_16_2369_0_join24

private theorem rec_7_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 0 128 = 21789285044522452905368573856 := by decide +kernel
private theorem rec_7_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 128 128 = 19471153414521703825570301856 := by decide +kernel
private theorem rec_7_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 256 128 = 17335452633172469268669511584 := by decide +kernel
private theorem rec_7_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 384 128 = 15372764693369206543593695136 := by decide +kernel
private theorem rec_7_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 512 128 = 13573929586851741119812343712 := by decide +kernel
private theorem rec_7_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 640 128 = 11930041979215869652255721376 := by decide +kernel
private theorem rec_7_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 768 128 = 10432447884923963006233638816 := by decide +kernel
private theorem rec_7_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 896 128 = 9072741342315569282354227104 := by decide +kernel
private theorem rec_7_16_2369_1_part8 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1024 128 = 7842761088618016841442711456 := by decide +kernel
private theorem rec_7_16_2369_1_part9 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1152 128 = 6734587234957017329460184992 := by decide +kernel
private theorem rec_7_16_2369_1_part10 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1280 128 = 5740537941367268702422382496 := by decide +kernel
private theorem rec_7_16_2369_1_part11 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1408 128 = 4853166091803058251318454176 := by decide +kernel
private theorem rec_7_16_2369_1_part12 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1536 128 = 4065256027195344259634050914 := by decide +kernel
private theorem rec_7_16_2369_1_part13 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1664 128 = 3369820658200636777317449874 := by decide +kernel
private theorem rec_7_16_2369_1_part14 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1792 128 = 2760097083589590090563912106 := by decide +kernel
private theorem rec_7_16_2369_1_part15 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1920 128 = 2229543418030631880639329469 := by decide +kernel
private theorem rec_7_16_2369_1_part16 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2048 128 = 1771835979892531258989718218 := by decide +kernel
private theorem rec_7_16_2369_1_part17 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2176 128 = 1380865961180696011055512722 := by decide +kernel
private theorem rec_7_16_2369_1_part18 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2304 128 = 1050736089303772957900001052 := by decide +kernel
private theorem rec_7_16_2369_1_part19 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2432 128 = 775757290241322646014199011 := by decide +kernel
private theorem rec_7_16_2369_1_part20 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2560 128 = 550445351775976744103349225 := by decide +kernel
private theorem rec_7_16_2369_1_part21 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2688 128 = 369517585979566342540758387 := by decide +kernel
private theorem rec_7_16_2369_1_part22 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2816 128 = 227889492025838461731046134 := by decide +kernel
private theorem rec_7_16_2369_1_part23 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2944 128 = 120671419171414997298206424 := by decide +kernel
private theorem rec_7_16_2369_1_part24 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 3072 128 = 43165229600428036188115716 := by decide +kernel
private theorem rec_7_16_2369_1_part25 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 3200 35 = 1739188574707535989151625 := by decide +kernel
private theorem rec_7_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 128 256 = 36806606047694173094239813440 :=
  phaseBlock_append rec_7_16_2369_1_part1 rec_7_16_2369_1_part2 rfl rfl rfl
private theorem rec_7_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 0 384 = 58595891092216625999608387296 :=
  phaseBlock_append rec_7_16_2369_1_part0 rec_7_16_2369_1_join0 rfl rfl rfl
private theorem rec_7_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 512 256 = 25503971566067610772068065088 :=
  phaseBlock_append rec_7_16_2369_1_part4 rec_7_16_2369_1_part5 rfl rfl rfl
private theorem rec_7_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 384 384 = 40876736259436817315661760224 :=
  phaseBlock_append rec_7_16_2369_1_part3 rec_7_16_2369_1_join2 rfl rfl rfl
private theorem rec_7_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 0 768 = 99472627351653443315270147520 :=
  phaseBlock_append rec_7_16_2369_1_join1 rec_7_16_2369_1_join3 rfl rfl rfl
private theorem rec_7_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 896 256 = 16915502430933586123796938560 :=
  phaseBlock_append rec_7_16_2369_1_part7 rec_7_16_2369_1_part8 rfl rfl rfl
private theorem rec_7_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 768 384 = 27347950315857549130030577376 :=
  phaseBlock_append rec_7_16_2369_1_part6 rec_7_16_2369_1_join5 rfl rfl rfl
private theorem rec_7_16_2369_1_join7 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1152 256 = 12475125176324286031882567488 :=
  phaseBlock_append rec_7_16_2369_1_part9 rec_7_16_2369_1_part10 rfl rfl rfl
private theorem rec_7_16_2369_1_join8 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1408 256 = 8918422118998402510952505090 :=
  phaseBlock_append rec_7_16_2369_1_part11 rec_7_16_2369_1_part12 rfl rfl rfl
private theorem rec_7_16_2369_1_join9 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1152 512 = 21393547295322688542835072578 :=
  phaseBlock_append rec_7_16_2369_1_join7 rec_7_16_2369_1_join8 rfl rfl rfl
private theorem rec_7_16_2369_1_join10 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 768 896 = 48741497611180237672865649954 :=
  phaseBlock_append rec_7_16_2369_1_join6 rec_7_16_2369_1_join9 rfl rfl rfl
private theorem rec_7_16_2369_1_join11 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 0 1664 = 148214124962833680988135797474 :=
  phaseBlock_append rec_7_16_2369_1_join4 rec_7_16_2369_1_join10 rfl rfl rfl
private theorem rec_7_16_2369_1_join12 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1792 256 = 4989640501620221971203241575 :=
  phaseBlock_append rec_7_16_2369_1_part14 rec_7_16_2369_1_part15 rfl rfl rfl
private theorem rec_7_16_2369_1_join13 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1664 384 = 8359461159820858748520691449 :=
  phaseBlock_append rec_7_16_2369_1_part13 rec_7_16_2369_1_join12 rfl rfl rfl
private theorem rec_7_16_2369_1_join14 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2176 256 = 2431602050484468968955513774 :=
  phaseBlock_append rec_7_16_2369_1_part17 rec_7_16_2369_1_part18 rfl rfl rfl
private theorem rec_7_16_2369_1_join15 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2048 384 = 4203438030377000227945231992 :=
  phaseBlock_append rec_7_16_2369_1_part16 rec_7_16_2369_1_join14 rfl rfl rfl
private theorem rec_7_16_2369_1_join16 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1664 768 = 12562899190197858976465923441 :=
  phaseBlock_append rec_7_16_2369_1_join13 rec_7_16_2369_1_join15 rfl rfl rfl
private theorem rec_7_16_2369_1_join17 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2560 256 = 919962937755543086644107612 :=
  phaseBlock_append rec_7_16_2369_1_part20 rec_7_16_2369_1_part21 rfl rfl rfl
private theorem rec_7_16_2369_1_join18 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2432 384 = 1695720227996865732658306623 :=
  phaseBlock_append rec_7_16_2369_1_part19 rec_7_16_2369_1_join17 rfl rfl rfl
private theorem rec_7_16_2369_1_join19 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2816 256 = 348560911197253459029252558 :=
  phaseBlock_append rec_7_16_2369_1_part22 rec_7_16_2369_1_part23 rfl rfl rfl
private theorem rec_7_16_2369_1_join20 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 3072 163 = 44904418175135572177267341 :=
  phaseBlock_append rec_7_16_2369_1_part24 rec_7_16_2369_1_part25 rfl rfl rfl
private theorem rec_7_16_2369_1_join21 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2816 419 = 393465329372389031206519899 :=
  phaseBlock_append rec_7_16_2369_1_join19 rec_7_16_2369_1_join20 rfl rfl rfl
private theorem rec_7_16_2369_1_join22 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 2432 803 = 2089185557369254763864826522 :=
  phaseBlock_append rec_7_16_2369_1_join18 rec_7_16_2369_1_join21 rfl rfl rfl
private theorem rec_7_16_2369_1_join23 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 1664 1571 = 14652084747567113740330749963 :=
  phaseBlock_append rec_7_16_2369_1_join16 rec_7_16_2369_1_join22 rfl rfl rfl
private theorem rec_7_16_2369_1_join24 :
    phaseBlock (fastLayerG (bank 7 16).shape 179798 2369 138 1 0 23 1) 0 3235 = 162866209710400794728466547437 :=
  phaseBlock_append rec_7_16_2369_1_join11 rec_7_16_2369_1_join23 rfl rfl rfl

private theorem rec_7_16_2369_1 : fastPhase (bank 7 16).shape 179798 2369 138 1 0 23 1 = 162866209710400794728466547437 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_7_16_2369_1_join24

theorem receipt_7_16 : Checked (bank 7 16) 138 0 23 := by
  refine checked_from_values (bank 7 16) 138 0 23
    (P3_7_1.checked (bank 7 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_14605_3234)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_7_16_2368_0 rec_7_16_2368_1 rec_7_16_2369_0 rec_7_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect7_checked (i : Fin 17) :
    Checked (bank 7 i) (reserve i) (excess 7) (seed 7) := by
  fin_cases i
  · exact receipt_7_0
  · exact receipt_7_1
  · exact receipt_7_2
  · exact receipt_7_3
  · exact receipt_7_4
  · exact receipt_7_5
  · exact receipt_7_6
  · exact receipt_7_7
  · exact receipt_7_8
  · exact receipt_7_9
  · exact receipt_7_10
  · exact receipt_7_11
  · exact receipt_7_12
  · exact receipt_7_13
  · exact receipt_7_14
  · exact receipt_7_15
  · exact receipt_7_16

end Lower6961.Lo.RescueSource
