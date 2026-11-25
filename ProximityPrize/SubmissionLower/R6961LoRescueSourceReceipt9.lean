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


private theorem rec_9_0_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2368 0 1 1 17 0) 0 128 = 22357809310703832344736 := by decide +kernel
private theorem rec_9_0_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2368 0 1 1 17 0) 128 63 = 1504067252312240421456 := by decide +kernel
private theorem rec_9_0_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2368 0 1 1 17 0) 0 191 = 23861876563016072766192 :=
  phaseBlock_append rec_9_0_2368_0_part0 rec_9_0_2368_0_part1 rfl rfl rfl

private theorem rec_9_0_2368_0 : fastPhase (bank 9 0).shape 179798 2368 0 1 1 17 0 = 23861876563016072766192 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_0_2368_0_join0

private theorem rec_9_0_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2368 0 1 1 17 1) 0 128 = 22072280464137351762720 := by decide +kernel
private theorem rec_9_0_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2368 0 1 1 17 1) 128 63 = 1450226874909924802992 := by decide +kernel
private theorem rec_9_0_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2368 0 1 1 17 1) 0 191 = 23522507339047276565712 :=
  phaseBlock_append rec_9_0_2368_1_part0 rec_9_0_2368_1_part1 rfl rfl rfl

private theorem rec_9_0_2368_1 : fastPhase (bank 9 0).shape 179798 2368 0 1 1 17 1 = 23522507339047276565712 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_0_2368_1_join0

private theorem rec_9_0_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2369 0 1 1 17 0) 0 128 = 22357972681453855931904 := by decide +kernel
private theorem rec_9_0_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2369 0 1 1 17 0) 128 63 = 1504071366038129210112 := by decide +kernel
private theorem rec_9_0_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2369 0 1 1 17 0) 0 191 = 23862044047491985142016 :=
  phaseBlock_append rec_9_0_2369_0_part0 rec_9_0_2369_0_part1 rfl rfl rfl

private theorem rec_9_0_2369_0 : fastPhase (bank 9 0).shape 179798 2369 0 1 1 17 0 = 23862044047491985142016 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_0_2369_0_join0

private theorem rec_9_0_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2369 0 1 1 17 1) 0 128 = 22072441641417703556160 := by decide +kernel
private theorem rec_9_0_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2369 0 1 1 17 1) 128 63 = 1450230850286841198240 := by decide +kernel
private theorem rec_9_0_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 0).shape 179798 2369 0 1 1 17 1) 0 191 = 23522672491704544754400 :=
  phaseBlock_append rec_9_0_2369_1_part0 rec_9_0_2369_1_part1 rfl rfl rfl

private theorem rec_9_0_2369_1 : fastPhase (bank 9 0).shape 179798 2369 0 1 1 17 1 = 23522672491704544754400 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_0_2369_1_join0

theorem receipt_9_0 : Checked (bank 9 0) 0 1 17 := by
  refine checked_from_values (bank 9 0) 0 1 17
    (P3_7_1.checked (bank 9 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_0_2368_0 rec_9_0_2368_1 rec_9_0_2369_0 rec_9_0_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2368 1 1 1 17 0) 0 128 = 31139014542745230884320 := by decide +kernel
private theorem rec_9_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2368 1 1 1 17 0) 128 63 = 2248924808813076781296 := by decide +kernel
private theorem rec_9_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2368 1 1 1 17 0) 0 191 = 33387939351558307665616 :=
  phaseBlock_append rec_9_1_2368_0_part0 rec_9_1_2368_0_part1 rfl rfl rfl

private theorem rec_9_1_2368_0 : fastPhase (bank 9 1).shape 179798 2368 1 1 1 17 0 = 33387939351558307665616 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_1_2368_0_join0

private theorem rec_9_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2368 1 1 1 17 1) 0 128 = 30757905567818774109408 := by decide +kernel
private theorem rec_9_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2368 1 1 1 17 1) 128 63 = 2169734999457454772784 := by decide +kernel
private theorem rec_9_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2368 1 1 1 17 1) 0 191 = 32927640567276228882192 :=
  phaseBlock_append rec_9_1_2368_1_part0 rec_9_1_2368_1_part1 rfl rfl rfl

private theorem rec_9_1_2368_1 : fastPhase (bank 9 1).shape 179798 2368 1 1 1 17 1 = 32927640567276228882192 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_1_2368_1_join0

private theorem rec_9_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2369 1 1 1 17 0) 0 128 = 31139239871787966416640 := by decide +kernel
private theorem rec_9_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2369 1 1 1 17 0) 128 63 = 2248930858985167351680 := by decide +kernel
private theorem rec_9_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2369 1 1 1 17 0) 0 191 = 33388170730773133768320 :=
  phaseBlock_append rec_9_1_2369_0_part0 rec_9_1_2369_0_part1 rfl rfl rfl

private theorem rec_9_1_2369_0 : fastPhase (bank 9 1).shape 179798 2369 1 1 1 17 0 = 33388170730773133768320 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_1_2369_0_join0

private theorem rec_9_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2369 1 1 1 17 1) 0 128 = 30758127989684056508736 := by decide +kernel
private theorem rec_9_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2369 1 1 1 17 1) 128 63 = 2169740850436962002592 := by decide +kernel
private theorem rec_9_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 1).shape 179798 2369 1 1 1 17 1) 0 191 = 32927868840121018511328 :=
  phaseBlock_append rec_9_1_2369_1_part0 rec_9_1_2369_1_part1 rfl rfl rfl

private theorem rec_9_1_2369_1 : fastPhase (bank 9 1).shape 179798 2369 1 1 1 17 1 = 32927868840121018511328 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_1_2369_1_join0

theorem receipt_9_1 : Checked (bank 9 1) 1 1 17 := by
  refine checked_from_values (bank 9 1) 1 1 17
    (P3_7_1.checked (bank 9 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_1_2368_0 rec_9_1_2368_1 rec_9_1_2369_0 rec_9_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2368 2 1 1 17 0) 0 128 = 47027841309145877012640 := by decide +kernel
private theorem rec_9_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2368 2 1 1 17 0) 128 63 = 3645141102364492142160 := by decide +kernel
private theorem rec_9_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2368 2 1 1 17 0) 0 191 = 50672982411510369154800 :=
  phaseBlock_append rec_9_2_2368_0_part0 rec_9_2_2368_0_part1 rfl rfl rfl

private theorem rec_9_2_2368_0 : fastPhase (bank 9 2).shape 179798 2368 2 1 1 17 0 = 50672982411510369154800 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_2_2368_0_join0

private theorem rec_9_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2368 2 1 1 17 1) 0 128 = 46478169637925743606560 := by decide +kernel
private theorem rec_9_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2368 2 1 1 17 1) 128 63 = 3518830845434251076016 := by decide +kernel
private theorem rec_9_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2368 2 1 1 17 1) 0 191 = 49997000483359994682576 :=
  phaseBlock_append rec_9_2_2368_1_part0 rec_9_2_2368_1_part1 rfl rfl rfl

private theorem rec_9_2_2368_1 : fastPhase (bank 9 2).shape 179798 2368 2 1 1 17 1 = 49997000483359994682576 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_2_2368_1_join0

private theorem rec_9_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2369 2 1 1 17 0) 0 128 = 47028178219462677221760 := by decide +kernel
private theorem rec_9_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2369 2 1 1 17 0) 128 63 = 3645150746298965652672 := by decide +kernel
private theorem rec_9_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2369 2 1 1 17 0) 0 191 = 50673328965761642874432 :=
  phaseBlock_append rec_9_2_2369_0_part0 rec_9_2_2369_0_part1 rfl rfl rfl

private theorem rec_9_2_2369_0 : fastPhase (bank 9 2).shape 179798 2369 2 1 1 17 0 = 50673328965761642874432 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_2_2369_0_join0

private theorem rec_9_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2369 2 1 1 17 1) 0 128 = 46478502385116859173312 := by decide +kernel
private theorem rec_9_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2369 2 1 1 17 1) 128 63 = 3518840178483190390368 := by decide +kernel
private theorem rec_9_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 2).shape 179798 2369 2 1 1 17 1) 0 191 = 49997342563600049563680 :=
  phaseBlock_append rec_9_2_2369_1_part0 rec_9_2_2369_1_part1 rfl rfl rfl

private theorem rec_9_2_2369_1 : fastPhase (bank 9 2).shape 179798 2369 2 1 1 17 1 = 49997342563600049563680 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_2_2369_1_join0

theorem receipt_9_2 : Checked (bank 9 2) 2 1 17 := by
  refine checked_from_values (bank 9 2) 2 1 17
    (P3_7_1.checked (bank 9 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_2_2368_0 rec_9_2_2368_1 rec_9_2_2369_0 rec_9_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2368 3 1 1 17 0) 0 128 = 81007118330742580059840 := by decide +kernel
private theorem rec_9_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2368 3 1 1 17 0) 128 63 = 6739070224126621333344 := by decide +kernel
private theorem rec_9_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2368 3 1 1 17 0) 0 191 = 87746188554869201393184 :=
  phaseBlock_append rec_9_3_2368_0_part0 rec_9_3_2368_0_part1 rfl rfl rfl

private theorem rec_9_3_2368_0 : fastPhase (bank 9 3).shape 179798 2368 3 1 1 17 0 = 87746188554869201393184 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_3_2368_0_join0

private theorem rec_9_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2368 3 1 1 17 1) 0 128 = 80106731619998115725952 := by decide +kernel
private theorem rec_9_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2368 3 1 1 17 1) 128 63 = 6509196941563995410928 := by decide +kernel
private theorem rec_9_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2368 3 1 1 17 1) 0 191 = 86615928561562111136880 :=
  phaseBlock_append rec_9_3_2368_1_part0 rec_9_3_2368_1_part1 rfl rfl rfl

private theorem rec_9_3_2368_1 : fastPhase (bank 9 3).shape 179798 2368 3 1 1 17 1 = 86615928561562111136880 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_3_2368_1_join0

private theorem rec_9_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2369 3 1 1 17 0) 0 128 = 81007692699407613020640 := by decide +kernel
private theorem rec_9_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2369 3 1 1 17 0) 128 63 = 6739087754816621843184 := by decide +kernel
private theorem rec_9_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2369 3 1 1 17 0) 0 191 = 87746780454224234863824 :=
  phaseBlock_append rec_9_3_2369_0_part0 rec_9_3_2369_0_part1 rfl rfl rfl

private theorem rec_9_3_2369_0 : fastPhase (bank 9 3).shape 179798 2369 3 1 1 17 0 = 87746780454224234863824 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_3_2369_0_join0

private theorem rec_9_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2369 3 1 1 17 1) 0 128 = 80107299218698036756128 := by decide +kernel
private theorem rec_9_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2369 3 1 1 17 1) 128 63 = 6509213918894675724624 := by decide +kernel
private theorem rec_9_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 3).shape 179798 2369 3 1 1 17 1) 0 191 = 86616513137592712480752 :=
  phaseBlock_append rec_9_3_2369_1_part0 rec_9_3_2369_1_part1 rfl rfl rfl

private theorem rec_9_3_2369_1 : fastPhase (bank 9 3).shape 179798 2369 3 1 1 17 1 = 86616513137592712480752 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_9_3_2369_1_join0

theorem receipt_9_3 : Checked (bank 9 3) 3 1 17 := by
  refine checked_from_values (bank 9 3) 3 1 17
    (P3_7_1.checked (bank 9 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_3_2368_0 rec_9_3_2368_1 rec_9_3_2369_0 rec_9_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2368 4 1 1 17 0) 0 128 = 158607509065839138529280 := by decide +kernel
private theorem rec_9_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2368 4 1 1 17 0) 128 128 = 38531521400834751381504 := by decide +kernel
private theorem rec_9_4_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2368 4 1 1 17 0) 256 22 = 557196271919680269646 := by decide +kernel
private theorem rec_9_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2368 4 1 1 17 0) 128 150 = 39088717672754431651150 :=
  phaseBlock_append rec_9_4_2368_0_part1 rec_9_4_2368_0_part2 rfl rfl rfl
private theorem rec_9_4_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2368 4 1 1 17 0) 0 278 = 197696226738593570180430 :=
  phaseBlock_append rec_9_4_2368_0_part0 rec_9_4_2368_0_join0 rfl rfl rfl

private theorem rec_9_4_2368_0 : fastPhase (bank 9 4).shape 179798 2368 4 1 1 17 0 = 197696226738593570180430 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_4_2368_0_join1

private theorem rec_9_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2368 4 1 1 17 1) 0 128 = 157286315542520414461824 := by decide +kernel
private theorem rec_9_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2368 4 1 1 17 1) 128 128 = 37940729364761774350208 := by decide +kernel
private theorem rec_9_4_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2368 4 1 1 17 1) 256 22 = 506858696746444069027 := by decide +kernel
private theorem rec_9_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2368 4 1 1 17 1) 128 150 = 38447588061508218419235 :=
  phaseBlock_append rec_9_4_2368_1_part1 rec_9_4_2368_1_part2 rfl rfl rfl
private theorem rec_9_4_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2368 4 1 1 17 1) 0 278 = 195733903604028632881059 :=
  phaseBlock_append rec_9_4_2368_1_part0 rec_9_4_2368_1_join0 rfl rfl rfl

private theorem rec_9_4_2368_1 : fastPhase (bank 9 4).shape 179798 2368 4 1 1 17 1 = 195733903604028632881059 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_4_2368_1_join1

private theorem rec_9_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2369 4 1 1 17 0) 0 128 = 158608726462967917544992 := by decide +kernel
private theorem rec_9_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2369 4 1 1 17 0) 128 128 = 38531672822950575617568 := by decide +kernel
private theorem rec_9_4_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2369 4 1 1 17 0) 256 22 = 557196939449110541042 := by decide +kernel
private theorem rec_9_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2369 4 1 1 17 0) 128 150 = 39088869762399686158610 :=
  phaseBlock_append rec_9_4_2369_0_part1 rec_9_4_2369_0_part2 rfl rfl rfl
private theorem rec_9_4_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2369 4 1 1 17 0) 0 278 = 197697596225367603703602 :=
  phaseBlock_append rec_9_4_2369_0_part0 rec_9_4_2369_0_join0 rfl rfl rfl

private theorem rec_9_4_2369_0 : fastPhase (bank 9 4).shape 179798 2369 4 1 1 17 0 = 197697596225367603703602 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_4_2369_0_join1

private theorem rec_9_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2369 4 1 1 17 1) 0 128 = 157287521990066335466208 := by decide +kernel
private theorem rec_9_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2369 4 1 1 17 1) 128 128 = 37940878474139013116640 := by decide +kernel
private theorem rec_9_4_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2369 4 1 1 17 1) 256 22 = 506859306780471223425 := by decide +kernel
private theorem rec_9_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2369 4 1 1 17 1) 128 150 = 38447737780919484340065 :=
  phaseBlock_append rec_9_4_2369_1_part1 rec_9_4_2369_1_part2 rfl rfl rfl
private theorem rec_9_4_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 4).shape 179798 2369 4 1 1 17 1) 0 278 = 195735259770985819806273 :=
  phaseBlock_append rec_9_4_2369_1_part0 rec_9_4_2369_1_join0 rfl rfl rfl

private theorem rec_9_4_2369_1 : fastPhase (bank 9 4).shape 179798 2369 4 1 1 17 1 = 195735259770985819806273 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_4_2369_1_join1

theorem receipt_9_4 : Checked (bank 9 4) 4 1 17 := by
  refine checked_from_values (bank 9 4) 4 1 17
    (P3_7_1.checked (bank 9 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_4_2368_0 rec_9_4_2368_1 rec_9_4_2369_0 rec_9_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2368 5 1 1 17 0) 0 128 = 194414138521111460929312 := by decide +kernel
private theorem rec_9_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2368 5 1 1 17 0) 128 128 = 49033552632757912653600 := by decide +kernel
private theorem rec_9_5_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2368 5 1 1 17 0) 256 22 = 737581914004109953460 := by decide +kernel
private theorem rec_9_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2368 5 1 1 17 0) 128 150 = 49771134546762022607060 :=
  phaseBlock_append rec_9_5_2368_0_part1 rec_9_5_2368_0_part2 rfl rfl rfl
private theorem rec_9_5_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2368 5 1 1 17 0) 0 278 = 244185273067873483536372 :=
  phaseBlock_append rec_9_5_2368_0_part0 rec_9_5_2368_0_join0 rfl rfl rfl

private theorem rec_9_5_2368_0 : fastPhase (bank 9 5).shape 179798 2368 5 1 1 17 0 = 244185273067873483536372 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_5_2368_0_join1

private theorem rec_9_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2368 5 1 1 17 1) 0 128 = 192844488610067035132896 := by decide +kernel
private theorem rec_9_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2368 5 1 1 17 1) 128 128 = 48296727535121193296864 := by decide +kernel
private theorem rec_9_5_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2368 5 1 1 17 1) 256 22 = 671178241950691096006 := by decide +kernel
private theorem rec_9_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2368 5 1 1 17 1) 128 150 = 48967905777071884392870 :=
  phaseBlock_append rec_9_5_2368_1_part1 rec_9_5_2368_1_part2 rfl rfl rfl
private theorem rec_9_5_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2368 5 1 1 17 1) 0 278 = 241812394387138919525766 :=
  phaseBlock_append rec_9_5_2368_1_part0 rec_9_5_2368_1_join0 rfl rfl rfl

private theorem rec_9_5_2368_1 : fastPhase (bank 9 5).shape 179798 2368 5 1 1 17 1 = 241812394387138919525766 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_5_2368_1_join1

private theorem rec_9_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2369 5 1 1 17 0) 0 128 = 194415623409291219088000 := by decide +kernel
private theorem rec_9_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2369 5 1 1 17 0) 128 128 = 49033743482626716537472 := by decide +kernel
private theorem rec_9_5_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2369 5 1 1 17 0) 256 22 = 737582778860327811928 := by decide +kernel
private theorem rec_9_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2369 5 1 1 17 0) 128 150 = 49771326261487044349400 :=
  phaseBlock_append rec_9_5_2369_0_part1 rec_9_5_2369_0_part2 rfl rfl rfl
private theorem rec_9_5_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2369 5 1 1 17 0) 0 278 = 244186949670778263437400 :=
  phaseBlock_append rec_9_5_2369_0_part0 rec_9_5_2369_0_join0 rfl rfl rfl

private theorem rec_9_5_2369_0 : fastPhase (bank 9 5).shape 179798 2369 5 1 1 17 0 = 244186949670778263437400 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_5_2369_0_join1

private theorem rec_9_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2369 5 1 1 17 1) 0 128 = 192845960516382463222080 := by decide +kernel
private theorem rec_9_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2369 5 1 1 17 1) 128 128 = 48296915530891888828736 := by decide +kernel
private theorem rec_9_5_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2369 5 1 1 17 1) 256 22 = 671179032693537154094 := by decide +kernel
private theorem rec_9_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2369 5 1 1 17 1) 128 150 = 48968094563585425982830 :=
  phaseBlock_append rec_9_5_2369_1_part1 rec_9_5_2369_1_part2 rfl rfl rfl
private theorem rec_9_5_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 5).shape 179798 2369 5 1 1 17 1) 0 278 = 241814055079967889204910 :=
  phaseBlock_append rec_9_5_2369_1_part0 rec_9_5_2369_1_join0 rfl rfl rfl

private theorem rec_9_5_2369_1 : fastPhase (bank 9 5).shape 179798 2369 5 1 1 17 1 = 241814055079967889204910 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_5_2369_1_join1

theorem receipt_9_5 : Checked (bank 9 5) 5 1 17 := by
  refine checked_from_values (bank 9 5) 5 1 17
    (P3_7_1.checked (bank 9 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_5_2368_0 rec_9_5_2368_1 rec_9_5_2369_0 rec_9_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2368 7 1 1 17 0) 0 128 = 322006347594254000960352 := by decide +kernel
private theorem rec_9_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2368 7 1 1 17 0) 128 128 = 87613442408030271636320 := by decide +kernel
private theorem rec_9_6_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2368 7 1 1 17 0) 256 22 = 1420717828715565952990 := by decide +kernel
private theorem rec_9_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2368 7 1 1 17 0) 128 150 = 89034160236745837589310 :=
  phaseBlock_append rec_9_6_2368_0_part1 rec_9_6_2368_0_part2 rfl rfl rfl
private theorem rec_9_6_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2368 7 1 1 17 0) 0 278 = 411040507830999838549662 :=
  phaseBlock_append rec_9_6_2368_0_part0 rec_9_6_2368_0_join0 rfl rfl rfl

private theorem rec_9_6_2368_0 : fastPhase (bank 9 6).shape 179798 2368 7 1 1 17 0 = 411040507830999838549662 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_6_2368_0_join1

private theorem rec_9_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2368 7 1 1 17 1) 0 128 = 319578422859163284212384 := by decide +kernel
private theorem rec_9_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2368 7 1 1 17 1) 128 128 = 86349531232440718375584 := by decide +kernel
private theorem rec_9_6_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2368 7 1 1 17 1) 256 22 = 1293634098659841516886 := by decide +kernel
private theorem rec_9_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2368 7 1 1 17 1) 128 150 = 87643165331100559892470 :=
  phaseBlock_append rec_9_6_2368_1_part1 rec_9_6_2368_1_part2 rfl rfl rfl
private theorem rec_9_6_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2368 7 1 1 17 1) 0 278 = 407221588190263844104854 :=
  phaseBlock_append rec_9_6_2368_1_part0 rec_9_6_2368_1_join0 rfl rfl rfl

private theorem rec_9_6_2368_1 : fastPhase (bank 9 6).shape 179798 2368 7 1 1 17 1 = 407221588190263844104854 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_6_2368_1_join1

private theorem rec_9_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2369 7 1 1 17 0) 0 128 = 322008782359954477611072 := by decide +kernel
private theorem rec_9_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2369 7 1 1 17 0) 128 128 = 87613776854671440951360 := by decide +kernel
private theorem rec_9_6_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2369 7 1 1 17 0) 256 22 = 1420719422316561361500 := by decide +kernel
private theorem rec_9_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2369 7 1 1 17 0) 128 150 = 89034496276988002312860 :=
  phaseBlock_append rec_9_6_2369_0_part1 rec_9_6_2369_0_part2 rfl rfl rfl
private theorem rec_9_6_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2369 7 1 1 17 0) 0 278 = 411043278636942479923932 :=
  phaseBlock_append rec_9_6_2369_0_part0 rec_9_6_2369_0_join0 rfl rfl rfl

private theorem rec_9_6_2369_0 : fastPhase (bank 9 6).shape 179798 2369 7 1 1 17 0 = 411043278636942479923932 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_6_2369_0_join1

private theorem rec_9_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2369 7 1 1 17 1) 0 128 = 319580837617432204372608 := by decide +kernel
private theorem rec_9_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2369 7 1 1 17 1) 128 128 = 86349860888297469545088 := by decide +kernel
private theorem rec_9_6_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2369 7 1 1 17 1) 256 22 = 1293635557039967593452 := by decide +kernel
private theorem rec_9_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2369 7 1 1 17 1) 128 150 = 87643496445337437138540 :=
  phaseBlock_append rec_9_6_2369_1_part1 rec_9_6_2369_1_part2 rfl rfl rfl
private theorem rec_9_6_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 6).shape 179798 2369 7 1 1 17 1) 0 278 = 407224334062769641511148 :=
  phaseBlock_append rec_9_6_2369_1_part0 rec_9_6_2369_1_join0 rfl rfl rfl

private theorem rec_9_6_2369_1 : fastPhase (bank 9 6).shape 179798 2369 7 1 1 17 1 = 407224334062769641511148 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_9_6_2369_1_join1

theorem receipt_9_6 : Checked (bank 9 6) 7 1 17 := by
  refine checked_from_values (bank 9 6) 7 1 17
    (P3_7_1.checked (bank 9 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_6_2368_0 rec_9_6_2368_1 rec_9_6_2369_0 rec_9_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2368 10 1 1 17 0) 0 128 = 906169976241031767428736 := by decide +kernel
private theorem rec_9_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2368 10 1 1 17 0) 128 128 = 369177538143863672024704 := by decide +kernel
private theorem rec_9_7_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2368 10 1 1 17 0) 256 114 = 73567593121806090830720 := by decide +kernel
private theorem rec_9_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2368 10 1 1 17 0) 128 242 = 442745131265669762855424 :=
  phaseBlock_append rec_9_7_2368_0_part1 rec_9_7_2368_0_part2 rfl rfl rfl
private theorem rec_9_7_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2368 10 1 1 17 0) 0 370 = 1348915107506701530284160 :=
  phaseBlock_append rec_9_7_2368_0_part0 rec_9_7_2368_0_join0 rfl rfl rfl

private theorem rec_9_7_2368_0 : fastPhase (bank 9 7).shape 179798 2368 10 1 1 17 0 = 1348915107506701530284160 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_9_7_2368_0_join1

private theorem rec_9_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2368 10 1 1 17 1) 0 128 = 900885538914871990828992 := by decide +kernel
private theorem rec_9_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2368 10 1 1 17 1) 128 128 = 366046166785489498783680 := by decide +kernel
private theorem rec_9_7_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2368 10 1 1 17 1) 256 114 = 72117085837501031298426 := by decide +kernel
private theorem rec_9_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2368 10 1 1 17 1) 128 242 = 438163252622990530082106 :=
  phaseBlock_append rec_9_7_2368_1_part1 rec_9_7_2368_1_part2 rfl rfl rfl
private theorem rec_9_7_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2368 10 1 1 17 1) 0 370 = 1339048791537862520911098 :=
  phaseBlock_append rec_9_7_2368_1_part0 rec_9_7_2368_1_join0 rfl rfl rfl

private theorem rec_9_7_2368_1 : fastPhase (bank 9 7).shape 179798 2368 10 1 1 17 1 = 1339048791537862520911098 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_9_7_2368_1_join1

private theorem rec_9_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2369 10 1 1 17 0) 0 128 = 906177162047815319119680 := by decide +kernel
private theorem rec_9_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2369 10 1 1 17 0) 128 128 = 369179361778780690573120 := by decide +kernel
private theorem rec_9_7_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2369 10 1 1 17 0) 256 114 = 73567770493307751388010 := by decide +kernel
private theorem rec_9_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2369 10 1 1 17 0) 128 242 = 442747132272088441961130 :=
  phaseBlock_append rec_9_7_2369_0_part1 rec_9_7_2369_0_part2 rfl rfl rfl
private theorem rec_9_7_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2369 10 1 1 17 0) 0 370 = 1348924294319903761080810 :=
  phaseBlock_append rec_9_7_2369_0_part0 rec_9_7_2369_0_join0 rfl rfl rfl

private theorem rec_9_7_2369_0 : fastPhase (bank 9 7).shape 179798 2369 10 1 1 17 0 = 1348924294319903761080810 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_9_7_2369_0_join1

private theorem rec_9_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2369 10 1 1 17 1) 0 128 = 900892678875723118274816 := by decide +kernel
private theorem rec_9_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2369 10 1 1 17 1) 128 128 = 366047973931551635278080 := by decide +kernel
private theorem rec_9_7_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2369 10 1 1 17 1) 256 114 = 72117259951702422417688 := by decide +kernel
private theorem rec_9_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2369 10 1 1 17 1) 128 242 = 438165233883254057695768 :=
  phaseBlock_append rec_9_7_2369_1_part1 rec_9_7_2369_1_part2 rfl rfl rfl
private theorem rec_9_7_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 7).shape 179798 2369 10 1 1 17 1) 0 370 = 1339057912758977175970584 :=
  phaseBlock_append rec_9_7_2369_1_part0 rec_9_7_2369_1_join0 rfl rfl rfl

private theorem rec_9_7_2369_1 : fastPhase (bank 9 7).shape 179798 2369 10 1 1 17 1 = 1339057912758977175970584 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_9_7_2369_1_join1

theorem receipt_9_7 : Checked (bank 9 7) 10 1 17 := by
  refine checked_from_values (bank 9 7) 10 1 17
    (P3_7_1.checked (bank 9 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_7_2368_0 rec_9_7_2368_1 rec_9_7_2369_0 rec_9_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 0) 0 128 = 3800010995889098824133600 := by decide +kernel
private theorem rec_9_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 0) 128 128 = 2032029958717454358739936 := by decide +kernel
private theorem rec_9_8_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 0) 256 128 = 866362441226832148253664 := by decide +kernel
private theorem rec_9_8_2368_0_part3 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 0) 384 109 = 174326582779633330952400 := by decide +kernel
private theorem rec_9_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 0) 0 256 = 5832040954606553182873536 :=
  phaseBlock_append rec_9_8_2368_0_part0 rec_9_8_2368_0_part1 rfl rfl rfl
private theorem rec_9_8_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 0) 256 237 = 1040689024006465479206064 :=
  phaseBlock_append rec_9_8_2368_0_part2 rec_9_8_2368_0_part3 rfl rfl rfl
private theorem rec_9_8_2368_0_join2 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 0) 0 493 = 6872729978613018662079600 :=
  phaseBlock_append rec_9_8_2368_0_join0 rec_9_8_2368_0_join1 rfl rfl rfl

private theorem rec_9_8_2368_0 : fastPhase (bank 9 8).shape 179798 2368 16 1 1 17 0 = 6872729978613018662079600 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_9_8_2368_0_join2

private theorem rec_9_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 1) 0 128 = 3783646178132979229429536 := by decide +kernel
private theorem rec_9_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 1) 128 128 = 2020837851863962014621472 := by decide +kernel
private theorem rec_9_8_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 1) 256 128 = 859301841224606950928160 := by decide +kernel
private theorem rec_9_8_2368_1_part3 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 1) 384 109 = 170831838916211001407469 := by decide +kernel
private theorem rec_9_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 1) 0 256 = 5804484029996941244051008 :=
  phaseBlock_append rec_9_8_2368_1_part0 rec_9_8_2368_1_part1 rfl rfl rfl
private theorem rec_9_8_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 1) 256 237 = 1030133680140817952335629 :=
  phaseBlock_append rec_9_8_2368_1_part2 rec_9_8_2368_1_part3 rfl rfl rfl
private theorem rec_9_8_2368_1_join2 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2368 16 1 1 17 1) 0 493 = 6834617710137759196386637 :=
  phaseBlock_append rec_9_8_2368_1_join0 rec_9_8_2368_1_join1 rfl rfl rfl

private theorem rec_9_8_2368_1 : fastPhase (bank 9 8).shape 179798 2368 16 1 1 17 1 = 6834617710137759196386637 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_9_8_2368_1_join2

private theorem rec_9_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 0) 0 128 = 3800042115884965388067840 := by decide +kernel
private theorem rec_9_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 0) 128 128 = 2032041912320006811878400 := by decide +kernel
private theorem rec_9_8_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 0) 256 128 = 866365658274352641500160 := by decide +kernel
private theorem rec_9_8_2369_0_part3 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 0) 384 109 = 174326909832180051709950 := by decide +kernel
private theorem rec_9_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 0) 0 256 = 5832084028204972199946240 :=
  phaseBlock_append rec_9_8_2369_0_part0 rec_9_8_2369_0_part1 rfl rfl rfl
private theorem rec_9_8_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 0) 256 237 = 1040692568106532693210110 :=
  phaseBlock_append rec_9_8_2369_0_part2 rec_9_8_2369_0_part3 rfl rfl rfl
private theorem rec_9_8_2369_0_join2 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 0) 0 493 = 6872776596311504893156350 :=
  phaseBlock_append rec_9_8_2369_0_join0 rec_9_8_2369_0_join1 rfl rfl rfl

private theorem rec_9_8_2369_0 : fastPhase (bank 9 8).shape 179798 2369 16 1 1 17 0 = 6872776596311504893156350 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_9_8_2369_0_join2

private theorem rec_9_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 1) 0 128 = 3783677150860817070194496 := by decide +kernel
private theorem rec_9_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 1) 128 128 = 2020849733970898670419776 := by decide +kernel
private theorem rec_9_8_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 1) 256 128 = 859305030506781211656000 := by decide +kernel
private theorem rec_9_8_2369_1_part3 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 1) 384 109 = 170832159876907695623382 := by decide +kernel
private theorem rec_9_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 1) 0 256 = 5804526884831715740614272 :=
  phaseBlock_append rec_9_8_2369_1_part0 rec_9_8_2369_1_part1 rfl rfl rfl
private theorem rec_9_8_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 1) 256 237 = 1030137190383688907279382 :=
  phaseBlock_append rec_9_8_2369_1_part2 rec_9_8_2369_1_part3 rfl rfl rfl
private theorem rec_9_8_2369_1_join2 :
    phaseBlock (fastLayerG (bank 9 8).shape 179798 2369 16 1 1 17 1) 0 493 = 6834664075215404647893654 :=
  phaseBlock_append rec_9_8_2369_1_join0 rec_9_8_2369_1_join1 rfl rfl rfl

private theorem rec_9_8_2369_1 : fastPhase (bank 9 8).shape 179798 2369 16 1 1 17 1 = 6834664075215404647893654 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_9_8_2369_1_join2

theorem receipt_9_8 : Checked (bank 9 8) 16 1 17 := by
  refine checked_from_values (bank 9 8) 16 1 17
    (P3_7_1.checked (bank 9 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_8_2368_0 rec_9_8_2368_1 rec_9_8_2369_0 rec_9_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2368 10 1 1 17 0) 0 128 = 906169976241031767428736 := by decide +kernel
private theorem rec_9_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2368 10 1 1 17 0) 128 128 = 369177538143863672024704 := by decide +kernel
private theorem rec_9_9_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2368 10 1 1 17 0) 256 114 = 73567593121806090830720 := by decide +kernel
private theorem rec_9_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2368 10 1 1 17 0) 128 242 = 442745131265669762855424 :=
  phaseBlock_append rec_9_9_2368_0_part1 rec_9_9_2368_0_part2 rfl rfl rfl
private theorem rec_9_9_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2368 10 1 1 17 0) 0 370 = 1348915107506701530284160 :=
  phaseBlock_append rec_9_9_2368_0_part0 rec_9_9_2368_0_join0 rfl rfl rfl

private theorem rec_9_9_2368_0 : fastPhase (bank 9 9).shape 179798 2368 10 1 1 17 0 = 1348915107506701530284160 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_9_9_2368_0_join1

private theorem rec_9_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2368 10 1 1 17 1) 0 128 = 900885538914871990828992 := by decide +kernel
private theorem rec_9_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2368 10 1 1 17 1) 128 128 = 366046166785489498783680 := by decide +kernel
private theorem rec_9_9_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2368 10 1 1 17 1) 256 114 = 72117085837501031298426 := by decide +kernel
private theorem rec_9_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2368 10 1 1 17 1) 128 242 = 438163252622990530082106 :=
  phaseBlock_append rec_9_9_2368_1_part1 rec_9_9_2368_1_part2 rfl rfl rfl
private theorem rec_9_9_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2368 10 1 1 17 1) 0 370 = 1339048791537862520911098 :=
  phaseBlock_append rec_9_9_2368_1_part0 rec_9_9_2368_1_join0 rfl rfl rfl

private theorem rec_9_9_2368_1 : fastPhase (bank 9 9).shape 179798 2368 10 1 1 17 1 = 1339048791537862520911098 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_9_9_2368_1_join1

private theorem rec_9_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2369 10 1 1 17 0) 0 128 = 906177162047815319119680 := by decide +kernel
private theorem rec_9_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2369 10 1 1 17 0) 128 128 = 369179361778780690573120 := by decide +kernel
private theorem rec_9_9_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2369 10 1 1 17 0) 256 114 = 73567770493307751388010 := by decide +kernel
private theorem rec_9_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2369 10 1 1 17 0) 128 242 = 442747132272088441961130 :=
  phaseBlock_append rec_9_9_2369_0_part1 rec_9_9_2369_0_part2 rfl rfl rfl
private theorem rec_9_9_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2369 10 1 1 17 0) 0 370 = 1348924294319903761080810 :=
  phaseBlock_append rec_9_9_2369_0_part0 rec_9_9_2369_0_join0 rfl rfl rfl

private theorem rec_9_9_2369_0 : fastPhase (bank 9 9).shape 179798 2369 10 1 1 17 0 = 1348924294319903761080810 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_9_9_2369_0_join1

private theorem rec_9_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2369 10 1 1 17 1) 0 128 = 900892678875723118274816 := by decide +kernel
private theorem rec_9_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2369 10 1 1 17 1) 128 128 = 366047973931551635278080 := by decide +kernel
private theorem rec_9_9_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2369 10 1 1 17 1) 256 114 = 72117259951702422417688 := by decide +kernel
private theorem rec_9_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2369 10 1 1 17 1) 128 242 = 438165233883254057695768 :=
  phaseBlock_append rec_9_9_2369_1_part1 rec_9_9_2369_1_part2 rfl rfl rfl
private theorem rec_9_9_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 9).shape 179798 2369 10 1 1 17 1) 0 370 = 1339057912758977175970584 :=
  phaseBlock_append rec_9_9_2369_1_part0 rec_9_9_2369_1_join0 rfl rfl rfl

private theorem rec_9_9_2369_1 : fastPhase (bank 9 9).shape 179798 2369 10 1 1 17 1 = 1339057912758977175970584 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_9_9_2369_1_join1

theorem receipt_9_9 : Checked (bank 9 9) 10 1 17 := by
  refine checked_from_values (bank 9 9) 10 1 17
    (P3_7_1.checked (bank 9 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_9_2368_0 rec_9_9_2368_1 rec_9_9_2369_0 rec_9_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 0) 0 128 = 6387129007663018957178336 := by decide +kernel
private theorem rec_9_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 0) 128 128 = 3573423722816904136275424 := by decide +kernel
private theorem rec_9_10_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 0) 256 128 = 1606421927568735543223776 := by decide +kernel
private theorem rec_9_10_2368_0_part3 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 0) 384 109 = 341681563887650986905675 := by decide +kernel
private theorem rec_9_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 0) 0 256 = 9960552730479923093453760 :=
  phaseBlock_append rec_9_10_2368_0_part0 rec_9_10_2368_0_part1 rfl rfl rfl
private theorem rec_9_10_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 0) 256 237 = 1948103491456386530129451 :=
  phaseBlock_append rec_9_10_2368_0_part2 rec_9_10_2368_0_part3 rfl rfl rfl
private theorem rec_9_10_2368_0_join2 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 0) 0 493 = 11908656221936309623583211 :=
  phaseBlock_append rec_9_10_2368_0_join0 rec_9_10_2368_0_join1 rfl rfl rfl

private theorem rec_9_10_2368_0 : fastPhase (bank 9 10).shape 179798 2368 20 1 1 17 0 = 11908656221936309623583211 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_9_10_2368_0_join2

private theorem rec_9_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 1) 0 128 = 6361696390376850965010720 := by decide +kernel
private theorem rec_9_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 1) 128 128 = 3555101805176646030641440 := by decide +kernel
private theorem rec_9_10_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 1) 256 128 = 1594038382341318663960864 := by decide +kernel
private theorem rec_9_10_2368_1_part3 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 1) 384 109 = 334959349095070017708177 := by decide +kernel
private theorem rec_9_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 1) 0 256 = 9916798195553496995652160 :=
  phaseBlock_append rec_9_10_2368_1_part0 rec_9_10_2368_1_part1 rfl rfl rfl
private theorem rec_9_10_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 1) 256 237 = 1928997731436388681669041 :=
  phaseBlock_append rec_9_10_2368_1_part2 rec_9_10_2368_1_part3 rfl rfl rfl
private theorem rec_9_10_2368_1_join2 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2368 20 1 1 17 1) 0 493 = 11845795926989885677321201 :=
  phaseBlock_append rec_9_10_2368_1_join0 rec_9_10_2368_1_join1 rfl rfl rfl

private theorem rec_9_10_2368_1 : fastPhase (bank 9 10).shape 179798 2368 20 1 1 17 1 = 11845795926989885677321201 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_9_10_2368_1_join2

private theorem rec_9_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 0) 0 128 = 6387180878602473432751008 := by decide +kernel
private theorem rec_9_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 0) 128 128 = 3573444500389342819986336 := by decide +kernel
private theorem rec_9_10_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 0) 256 128 = 1606427783493069983529888 := by decide +kernel
private theorem rec_9_10_2369_0_part3 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 0) 384 109 = 341682183481159856703753 := by decide +kernel
private theorem rec_9_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 0) 0 256 = 9960625378991816252737344 :=
  phaseBlock_append rec_9_10_2369_0_part0 rec_9_10_2369_0_part1 rfl rfl rfl
private theorem rec_9_10_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 0) 256 237 = 1948109966974229840233641 :=
  phaseBlock_append rec_9_10_2369_0_part2 rec_9_10_2369_0_part3 rfl rfl rfl
private theorem rec_9_10_2369_0_join2 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 0) 0 493 = 11908735345966046092970985 :=
  phaseBlock_append rec_9_10_2369_0_join0 rec_9_10_2369_0_join1 rfl rfl rfl

private theorem rec_9_10_2369_0 : fastPhase (bank 9 10).shape 179798 2369 20 1 1 17 0 = 11908735345966046092970985 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_9_10_2369_0_join2

private theorem rec_9_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 1) 0 128 = 6361748032530846417043680 := by decide +kernel
private theorem rec_9_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 1) 128 128 = 3555122466278067421155552 := by decide +kernel
private theorem rec_9_10_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 1) 256 128 = 1594044190263498069827808 := by decide +kernel
private theorem rec_9_10_2369_1_part3 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 1) 384 109 = 334959957446253015082815 := by decide +kernel
private theorem rec_9_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 1) 0 256 = 9916870498808913838199232 :=
  phaseBlock_append rec_9_10_2369_1_part0 rec_9_10_2369_1_part1 rfl rfl rfl
private theorem rec_9_10_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 1) 256 237 = 1929004147709751084910623 :=
  phaseBlock_append rec_9_10_2369_1_part2 rec_9_10_2369_1_part3 rfl rfl rfl
private theorem rec_9_10_2369_1_join2 :
    phaseBlock (fastLayerG (bank 9 10).shape 179798 2369 20 1 1 17 1) 0 493 = 11845874646518664923109855 :=
  phaseBlock_append rec_9_10_2369_1_join0 rec_9_10_2369_1_join1 rfl rfl rfl

private theorem rec_9_10_2369_1 : fastPhase (bank 9 10).shape 179798 2369 20 1 1 17 1 = 11845874646518664923109855 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_9_10_2369_1_join2

theorem receipt_9_10 : Checked (bank 9 10) 20 1 17 := by
  refine checked_from_values (bank 9 10) 20 1 17
    (P3_7_1.checked (bank 9 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_10_2368_0 rec_9_10_2368_1 rec_9_10_2369_0 rec_9_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 0 128 = 36298067362493337583117984 := by decide +kernel
private theorem rec_9_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 128 128 = 24542667783387609399039648 := by decide +kernel
private theorem rec_9_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 256 128 = 15276634737888212165183136 := by decide +kernel
private theorem rec_9_11_2368_0_part3 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 384 128 = 8202192495601781728573088 := by decide +kernel
private theorem rec_9_11_2368_0_part4 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 512 128 = 3026311769063638564415136 := by decide +kernel
private theorem rec_9_11_2368_0_part5 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 640 38 = 147026705633051059638082 := by decide +kernel
private theorem rec_9_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 128 256 = 39819302521275821564222784 :=
  phaseBlock_append rec_9_11_2368_0_part1 rec_9_11_2368_0_part2 rfl rfl rfl
private theorem rec_9_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 0 384 = 76117369883769159147340768 :=
  phaseBlock_append rec_9_11_2368_0_part0 rec_9_11_2368_0_join0 rfl rfl rfl
private theorem rec_9_11_2368_0_join2 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 512 166 = 3173338474696689624053218 :=
  phaseBlock_append rec_9_11_2368_0_part4 rec_9_11_2368_0_part5 rfl rfl rfl
private theorem rec_9_11_2368_0_join3 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 384 294 = 11375530970298471352626306 :=
  phaseBlock_append rec_9_11_2368_0_part3 rec_9_11_2368_0_join2 rfl rfl rfl
private theorem rec_9_11_2368_0_join4 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 0) 0 678 = 87492900854067630499967074 :=
  phaseBlock_append rec_9_11_2368_0_join1 rec_9_11_2368_0_join3 rfl rfl rfl

private theorem rec_9_11_2368_0 : fastPhase (bank 9 11).shape 179798 2368 32 1 1 17 0 = 87492900854067630499967074 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_9_11_2368_0_join4

private theorem rec_9_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 0 128 = 36196765757349043718498848 := by decide +kernel
private theorem rec_9_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 128 128 = 24461653677118555259132448 := by decide +kernel
private theorem rec_9_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 256 128 = 15213645035781305438112288 := by decide +kernel
private theorem rec_9_11_2368_1_part3 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 384 128 = 8154979370337392427416096 := by decide +kernel
private theorem rec_9_11_2368_1_part4 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 512 128 = 2992664835497814015044128 := by decide +kernel
private theorem rec_9_11_2368_1_part5 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 640 38 = 139330412714645429999550 := by decide +kernel
private theorem rec_9_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 128 256 = 39675298712899860697244736 :=
  phaseBlock_append rec_9_11_2368_1_part1 rec_9_11_2368_1_part2 rfl rfl rfl
private theorem rec_9_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 0 384 = 75872064470248904415743584 :=
  phaseBlock_append rec_9_11_2368_1_part0 rec_9_11_2368_1_join0 rfl rfl rfl
private theorem rec_9_11_2368_1_join2 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 512 166 = 3131995248212459445043678 :=
  phaseBlock_append rec_9_11_2368_1_part4 rec_9_11_2368_1_part5 rfl rfl rfl
private theorem rec_9_11_2368_1_join3 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 384 294 = 11286974618549851872459774 :=
  phaseBlock_append rec_9_11_2368_1_part3 rec_9_11_2368_1_join2 rfl rfl rfl
private theorem rec_9_11_2368_1_join4 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2368 32 1 1 17 1) 0 678 = 87159039088798756288203358 :=
  phaseBlock_append rec_9_11_2368_1_join1 rec_9_11_2368_1_join3 rfl rfl rfl

private theorem rec_9_11_2368_1 : fastPhase (bank 9 11).shape 179798 2368 32 1 1 17 1 = 87159039088798756288203358 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_9_11_2368_1_join4

private theorem rec_9_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 0 128 = 36298370404434966861371040 := by decide +kernel
private theorem rec_9_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 128 128 = 24542830748493133493634720 := by decide +kernel
private theorem rec_9_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 256 128 = 15276711032452459665897120 := by decide +kernel
private theorem rec_9_11_2369_0_part3 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 384 128 = 8202220516664790240028320 := by decide +kernel
private theorem rec_9_11_2369_0_part4 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 512 128 = 3026317670681442315507360 := by decide +kernel
private theorem rec_9_11_2369_0_part5 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 640 38 = 147026832427100759970330 := by decide +kernel
private theorem rec_9_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 128 256 = 39819541780945593159531840 :=
  phaseBlock_append rec_9_11_2369_0_part1 rec_9_11_2369_0_part2 rfl rfl rfl
private theorem rec_9_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 0 384 = 76117912185380560020902880 :=
  phaseBlock_append rec_9_11_2369_0_part0 rec_9_11_2369_0_join0 rfl rfl rfl
private theorem rec_9_11_2369_0_join2 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 512 166 = 3173344503108543075477690 :=
  phaseBlock_append rec_9_11_2369_0_part4 rec_9_11_2369_0_part5 rfl rfl rfl
private theorem rec_9_11_2369_0_join3 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 384 294 = 11375565019773333315506010 :=
  phaseBlock_append rec_9_11_2369_0_part3 rec_9_11_2369_0_join2 rfl rfl rfl
private theorem rec_9_11_2369_0_join4 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 0) 0 678 = 87493477205153893336408890 :=
  phaseBlock_append rec_9_11_2369_0_join1 rec_9_11_2369_0_join3 rfl rfl rfl

private theorem rec_9_11_2369_0 : fastPhase (bank 9 11).shape 179798 2369 32 1 1 17 0 = 87493477205153893336408890 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_9_11_2369_0_join4

private theorem rec_9_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 0 128 = 36197067857705266091699616 := by decide +kernel
private theorem rec_9_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 128 128 = 24461816047787902766439840 := by decide +kernel
private theorem rec_9_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 256 128 = 15213720985946780587003296 := by decide +kernel
private theorem rec_9_11_2369_1_part3 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 384 128 = 8155007217780114479365536 := by decide +kernel
private theorem rec_9_11_2369_1_part4 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 512 128 = 2992670671239292435262880 := by decide +kernel
private theorem rec_9_11_2369_1_part5 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 640 38 = 139330533203367607310508 := by decide +kernel
private theorem rec_9_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 128 256 = 39675537033734683353443136 :=
  phaseBlock_append rec_9_11_2369_1_part1 rec_9_11_2369_1_part2 rfl rfl rfl
private theorem rec_9_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 0 384 = 75872604891439949445142752 :=
  phaseBlock_append rec_9_11_2369_1_part0 rec_9_11_2369_1_join0 rfl rfl rfl
private theorem rec_9_11_2369_1_join2 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 512 166 = 3132001204442660042573388 :=
  phaseBlock_append rec_9_11_2369_1_part4 rec_9_11_2369_1_part5 rfl rfl rfl
private theorem rec_9_11_2369_1_join3 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 384 294 = 11287008422222774521938924 :=
  phaseBlock_append rec_9_11_2369_1_part3 rec_9_11_2369_1_join2 rfl rfl rfl
private theorem rec_9_11_2369_1_join4 :
    phaseBlock (fastLayerG (bank 9 11).shape 179798 2369 32 1 1 17 1) 0 678 = 87159613313662723967081676 :=
  phaseBlock_append rec_9_11_2369_1_join1 rec_9_11_2369_1_join3 rfl rfl rfl

private theorem rec_9_11_2369_1 : fastPhase (bank 9 11).shape 179798 2369 32 1 1 17 1 = 87159613313662723967081676 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_9_11_2369_1_join4

theorem receipt_9_11 : Checked (bank 9 11) 32 1 17 := by
  refine checked_from_values (bank 9 11) 32 1 17
    (P3_7_1.checked (bank 9 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_11_2368_0 rec_9_11_2368_1 rec_9_11_2369_0 rec_9_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 0 128 = 32431890470582285636181280 := by decide +kernel
private theorem rec_9_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 128 128 = 21798099484059787860938016 := by decide +kernel
private theorem rec_9_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 256 128 = 13478848470860911774104864 := by decide +kernel
private theorem rec_9_12_2368_0_part3 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 384 128 = 7184125331952216268762400 := by decide +kernel
private theorem rec_9_12_2368_0_part4 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 512 128 = 2629881722039927926644000 := by decide +kernel
private theorem rec_9_12_2368_0_part5 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 640 38 = 126923632776960141203770 := by decide +kernel
private theorem rec_9_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 128 256 = 35276947954920699635042880 :=
  phaseBlock_append rec_9_12_2368_0_part1 rec_9_12_2368_0_part2 rfl rfl rfl
private theorem rec_9_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 0 384 = 67708838425502985271224160 :=
  phaseBlock_append rec_9_12_2368_0_part0 rec_9_12_2368_0_join0 rfl rfl rfl
private theorem rec_9_12_2368_0_join2 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 512 166 = 2756805354816888067847770 :=
  phaseBlock_append rec_9_12_2368_0_part4 rec_9_12_2368_0_part5 rfl rfl rfl
private theorem rec_9_12_2368_0_join3 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 384 294 = 9940930686769104336610170 :=
  phaseBlock_append rec_9_12_2368_0_part3 rec_9_12_2368_0_join2 rfl rfl rfl
private theorem rec_9_12_2368_0_join4 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 0) 0 678 = 77649769112272089607834330 :=
  phaseBlock_append rec_9_12_2368_0_join1 rec_9_12_2368_0_join3 rfl rfl rfl

private theorem rec_9_12_2368_0 : fastPhase (bank 9 12).shape 179798 2368 31 1 1 17 0 = 77649769112272089607834330 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_9_12_2368_0_join4

private theorem rec_9_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 0 128 = 32339944676038256894977696 := by decide +kernel
private theorem rec_9_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 128 128 = 21725079307168548259108512 := by decide +kernel
private theorem rec_9_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 256 128 = 13422541217316772934551200 := by decide +kernel
private theorem rec_9_12_2368_1_part3 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 384 128 = 7142343556577063801124512 := by decide +kernel
private theorem rec_9_12_2368_1_part4 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 512 128 = 2600485403565436415141536 := by decide +kernel
private theorem rec_9_12_2368_1_part5 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 640 38 = 120273527257497868567110 := by decide +kernel
private theorem rec_9_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 128 256 = 35147620524485321193659712 :=
  phaseBlock_append rec_9_12_2368_1_part1 rec_9_12_2368_1_part2 rfl rfl rfl
private theorem rec_9_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 0 384 = 67487565200523578088637408 :=
  phaseBlock_append rec_9_12_2368_1_part0 rec_9_12_2368_1_join0 rfl rfl rfl
private theorem rec_9_12_2368_1_join2 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 512 166 = 2720758930822934283708646 :=
  phaseBlock_append rec_9_12_2368_1_part4 rec_9_12_2368_1_part5 rfl rfl rfl
private theorem rec_9_12_2368_1_join3 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 384 294 = 9863102487399998084833158 :=
  phaseBlock_append rec_9_12_2368_1_part3 rec_9_12_2368_1_join2 rfl rfl rfl
private theorem rec_9_12_2368_1_join4 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2368 31 1 1 17 1) 0 678 = 77350667687923576173470566 :=
  phaseBlock_append rec_9_12_2368_1_join1 rec_9_12_2368_1_join3 rfl rfl rfl

private theorem rec_9_12_2368_1 : fastPhase (bank 9 12).shape 179798 2368 31 1 1 17 1 = 77350667687923576173470566 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_9_12_2368_1_join4

private theorem rec_9_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 0 128 = 32432161616619994212185760 := by decide +kernel
private theorem rec_9_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 128 128 = 21798244479505347319785120 := by decide +kernel
private theorem rec_9_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 256 128 = 13478915943115697359623840 := by decide +kernel
private theorem rec_9_12_2369_0_part3 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 384 128 = 7184149957639647086036640 := by decide +kernel
private theorem rec_9_12_2369_0_part4 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 512 128 = 2629886880362045375936160 := by decide +kernel
private theorem rec_9_12_2369_0_part5 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 640 38 = 126923743545276362611290 := by decide +kernel
private theorem rec_9_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 128 256 = 35277160422621044679408960 :=
  phaseBlock_append rec_9_12_2369_0_part1 rec_9_12_2369_0_part2 rfl rfl rfl
private theorem rec_9_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 0 384 = 67709322039241038891594720 :=
  phaseBlock_append rec_9_12_2369_0_part0 rec_9_12_2369_0_join0 rfl rfl rfl
private theorem rec_9_12_2369_0_join2 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 512 166 = 2756810623907321738547450 :=
  phaseBlock_append rec_9_12_2369_0_part4 rec_9_12_2369_0_part5 rfl rfl rfl
private theorem rec_9_12_2369_0_join3 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 384 294 = 9940960581546968824584090 :=
  phaseBlock_append rec_9_12_2369_0_part3 rec_9_12_2369_0_join2 rfl rfl rfl
private theorem rec_9_12_2369_0_join4 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 0) 0 678 = 77650282620788007716178810 :=
  phaseBlock_append rec_9_12_2369_0_join1 rec_9_12_2369_0_join3 rfl rfl rfl

private theorem rec_9_12_2369_0 : fastPhase (bank 9 12).shape 179798 2369 31 1 1 17 0 = 77650282620788007716178810 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_9_12_2369_0_join4

private theorem rec_9_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 0 128 = 32340214967688769799434656 := by decide +kernel
private theorem rec_9_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 128 128 = 21725223766700422805954976 := by decide +kernel
private theorem rec_9_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 256 128 = 13422608381389121818169760 := by decide +kernel
private theorem rec_9_12_2369_1_part3 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 384 128 = 7142368028240919445995936 := by decide +kernel
private theorem rec_9_12_2369_1_part4 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 512 128 = 2600490503991815250080160 := by decide +kernel
private theorem rec_9_12_2369_1_part5 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 640 38 = 120273632508037262254578 := by decide +kernel
private theorem rec_9_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 128 256 = 35147832148089544624124736 :=
  phaseBlock_append rec_9_12_2369_1_part1 rec_9_12_2369_1_part2 rfl rfl rfl
private theorem rec_9_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 0 384 = 67488047115778314423559392 :=
  phaseBlock_append rec_9_12_2369_1_part0 rec_9_12_2369_1_join0 rfl rfl rfl
private theorem rec_9_12_2369_1_join2 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 512 166 = 2720764136499852512334738 :=
  phaseBlock_append rec_9_12_2369_1_part4 rec_9_12_2369_1_part5 rfl rfl rfl
private theorem rec_9_12_2369_1_join3 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 384 294 = 9863132164740771958330674 :=
  phaseBlock_append rec_9_12_2369_1_part3 rec_9_12_2369_1_join2 rfl rfl rfl
private theorem rec_9_12_2369_1_join4 :
    phaseBlock (fastLayerG (bank 9 12).shape 179798 2369 31 1 1 17 1) 0 678 = 77351179280519086381890066 :=
  phaseBlock_append rec_9_12_2369_1_join1 rec_9_12_2369_1_join3 rfl rfl rfl

private theorem rec_9_12_2369_1 : fastPhase (bank 9 12).shape 179798 2369 31 1 1 17 1 = 77351179280519086381890066 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_9_12_2369_1_join4

theorem receipt_9_12 : Checked (bank 9 12) 31 1 17 := by
  refine checked_from_values (bank 9 12) 31 1 17
    (P3_7_1.checked (bank 9 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_12_2368_0 rec_9_12_2368_1 rec_9_12_2369_0 rec_9_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 0 128 = 138297166992679683302569472 := by decide +kernel
private theorem rec_9_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 128 128 = 103989659879724100218828288 := by decide +kernel
private theorem rec_9_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 256 128 = 75306508193732000963769856 := by decide +kernel
private theorem rec_9_13_2368_0_part3 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 384 128 = 51721561686784083973879296 := by decide +kernel
private theorem rec_9_13_2368_0_part4 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 512 128 = 32716359974837821979309568 := by decide +kernel
private theorem rec_9_13_2368_0_part5 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 640 128 = 17782862556621645633992192 := by decide +kernel
private theorem rec_9_13_2368_0_part6 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 768 128 = 6426178832529127145747968 := by decide +kernel
private theorem rec_9_13_2368_0_part7 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 896 29 = 206740747971775435905585 := by decide +kernel
private theorem rec_9_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 0 256 = 242286826872403783521397760 :=
  phaseBlock_append rec_9_13_2368_0_part0 rec_9_13_2368_0_part1 rfl rfl rfl
private theorem rec_9_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 256 256 = 127028069880516084937649152 :=
  phaseBlock_append rec_9_13_2368_0_part2 rec_9_13_2368_0_part3 rfl rfl rfl
private theorem rec_9_13_2368_0_join2 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 0 512 = 369314896752919868459046912 :=
  phaseBlock_append rec_9_13_2368_0_join0 rec_9_13_2368_0_join1 rfl rfl rfl
private theorem rec_9_13_2368_0_join3 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 512 256 = 50499222531459467613301760 :=
  phaseBlock_append rec_9_13_2368_0_part4 rec_9_13_2368_0_part5 rfl rfl rfl
private theorem rec_9_13_2368_0_join4 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 768 157 = 6632919580500902581653553 :=
  phaseBlock_append rec_9_13_2368_0_part6 rec_9_13_2368_0_part7 rfl rfl rfl
private theorem rec_9_13_2368_0_join5 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 512 413 = 57132142111960370194955313 :=
  phaseBlock_append rec_9_13_2368_0_join3 rec_9_13_2368_0_join4 rfl rfl rfl
private theorem rec_9_13_2368_0_join6 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 0) 0 925 = 426447038864880238654002225 :=
  phaseBlock_append rec_9_13_2368_0_join2 rec_9_13_2368_0_join5 rfl rfl rfl

private theorem rec_9_13_2368_0 : fastPhase (bank 9 13).shape 179798 2368 44 1 1 17 0 = 426447038864880238654002225 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_9_13_2368_0_join6

private theorem rec_9_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 0 128 = 138008658187522087665027392 := by decide +kernel
private theorem rec_9_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 128 128 = 103746452806909343881300288 := by decide +kernel
private theorem rec_9_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 256 128 = 75104593755258563173402944 := by decide +kernel
private theorem rec_9_13_2368_1_part3 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 384 128 = 51556965780975917412026688 := by decide +kernel
private theorem rec_9_13_2368_1_part4 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 512 128 = 32585165671126567749372224 := by decide +kernel
private theorem rec_9_13_2368_1_part5 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 640 128 = 17681232270328848249260352 := by decide +kernel
private theorem rec_9_13_2368_1_part6 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 768 128 = 6350376499648449517242688 := by decide +kernel
private theorem rec_9_13_2368_1_part7 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 896 29 = 192780211416054935013894 := by decide +kernel
private theorem rec_9_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 0 256 = 241755110994431431546327680 :=
  phaseBlock_append rec_9_13_2368_1_part0 rec_9_13_2368_1_part1 rfl rfl rfl
private theorem rec_9_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 256 256 = 126661559536234480585429632 :=
  phaseBlock_append rec_9_13_2368_1_part2 rec_9_13_2368_1_part3 rfl rfl rfl
private theorem rec_9_13_2368_1_join2 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 0 512 = 368416670530665912131757312 :=
  phaseBlock_append rec_9_13_2368_1_join0 rec_9_13_2368_1_join1 rfl rfl rfl
private theorem rec_9_13_2368_1_join3 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 512 256 = 50266397941455415998632576 :=
  phaseBlock_append rec_9_13_2368_1_part4 rec_9_13_2368_1_part5 rfl rfl rfl
private theorem rec_9_13_2368_1_join4 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 768 157 = 6543156711064504452256582 :=
  phaseBlock_append rec_9_13_2368_1_part6 rec_9_13_2368_1_part7 rfl rfl rfl
private theorem rec_9_13_2368_1_join5 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 512 413 = 56809554652519920450889158 :=
  phaseBlock_append rec_9_13_2368_1_join3 rec_9_13_2368_1_join4 rfl rfl rfl
private theorem rec_9_13_2368_1_join6 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2368 44 1 1 17 1) 0 925 = 425226225183185832582646470 :=
  phaseBlock_append rec_9_13_2368_1_join2 rec_9_13_2368_1_join5 rfl rfl rfl

private theorem rec_9_13_2368_1 : fastPhase (bank 9 13).shape 179798 2368 44 1 1 17 1 = 425226225183185832582646470 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_9_13_2368_1_join6

private theorem rec_9_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 0 128 = 138298350175768403290416768 := by decide +kernel
private theorem rec_9_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 128 128 = 103990417740109964183832192 := by decide +kernel
private theorem rec_9_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 256 128 = 75306964030004062220592768 := by decide +kernel
private theorem rec_9_13_2369_0_part3 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 384 128 = 51721812575920987023918720 := by decide +kernel
private theorem rec_9_13_2369_0_part4 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 512 128 = 32716480430272336602556032 := by decide +kernel
private theorem rec_9_13_2369_0_part5 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 640 128 = 17782907932098112639075968 := by decide +kernel
private theorem rec_9_13_2369_0_part6 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 768 128 = 6426188471753815778174592 := by decide +kernel
private theorem rec_9_13_2369_0_part7 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 896 29 = 206740897843938903555810 := by decide +kernel
private theorem rec_9_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 0 256 = 242288767915878367474248960 :=
  phaseBlock_append rec_9_13_2369_0_part0 rec_9_13_2369_0_part1 rfl rfl rfl
private theorem rec_9_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 256 256 = 127028776605925049244511488 :=
  phaseBlock_append rec_9_13_2369_0_part2 rec_9_13_2369_0_part3 rfl rfl rfl
private theorem rec_9_13_2369_0_join2 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 0 512 = 369317544521803416718760448 :=
  phaseBlock_append rec_9_13_2369_0_join0 rec_9_13_2369_0_join1 rfl rfl rfl
private theorem rec_9_13_2369_0_join3 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 512 256 = 50499388362370449241632000 :=
  phaseBlock_append rec_9_13_2369_0_part4 rec_9_13_2369_0_part5 rfl rfl rfl
private theorem rec_9_13_2369_0_join4 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 768 157 = 6632929369597754681730402 :=
  phaseBlock_append rec_9_13_2369_0_part6 rec_9_13_2369_0_part7 rfl rfl rfl
private theorem rec_9_13_2369_0_join5 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 512 413 = 57132317731968203923362402 :=
  phaseBlock_append rec_9_13_2369_0_join3 rec_9_13_2369_0_join4 rfl rfl rfl
private theorem rec_9_13_2369_0_join6 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 0) 0 925 = 426449862253771620642122850 :=
  phaseBlock_append rec_9_13_2369_0_join2 rec_9_13_2369_0_join5 rfl rfl rfl

private theorem rec_9_13_2369_0 : fastPhase (bank 9 13).shape 179798 2369 44 1 1 17 0 = 426449862253771620642122850 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_9_13_2369_0_join6

private theorem rec_9_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 0 128 = 138009838627529293700749056 := by decide +kernel
private theorem rec_9_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 128 128 = 103747208706660741391316736 := by decide +kernel
private theorem rec_9_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 256 128 = 75105048246116225965397760 := by decide +kernel
private theorem rec_9_13_2369_1_part3 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 384 128 = 51557215796132104099673856 := by decide +kernel
private theorem rec_9_13_2369_1_part4 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 512 128 = 32585285602039741684504320 := by decide +kernel
private theorem rec_9_13_2369_1_part5 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 640 128 = 17681277368952609112225536 := by decide +kernel
private theorem rec_9_13_2369_1_part6 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 768 128 = 6350386026453376565450496 := by decide +kernel
private theorem rec_9_13_2369_1_part7 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 896 29 = 192780351510852226449300 := by decide +kernel
private theorem rec_9_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 0 256 = 241757047334190035092065792 :=
  phaseBlock_append rec_9_13_2369_1_part0 rec_9_13_2369_1_part1 rfl rfl rfl
private theorem rec_9_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 256 256 = 126662264042248330065071616 :=
  phaseBlock_append rec_9_13_2369_1_part2 rec_9_13_2369_1_part3 rfl rfl rfl
private theorem rec_9_13_2369_1_join2 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 0 512 = 368419311376438365157137408 :=
  phaseBlock_append rec_9_13_2369_1_join0 rec_9_13_2369_1_join1 rfl rfl rfl
private theorem rec_9_13_2369_1_join3 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 512 256 = 50266562970992350796729856 :=
  phaseBlock_append rec_9_13_2369_1_part4 rec_9_13_2369_1_part5 rfl rfl rfl
private theorem rec_9_13_2369_1_join4 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 768 157 = 6543166377964228791899796 :=
  phaseBlock_append rec_9_13_2369_1_part6 rec_9_13_2369_1_part7 rfl rfl rfl
private theorem rec_9_13_2369_1_join5 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 512 413 = 56809729348956579588629652 :=
  phaseBlock_append rec_9_13_2369_1_join3 rec_9_13_2369_1_join4 rfl rfl rfl
private theorem rec_9_13_2369_1_join6 :
    phaseBlock (fastLayerG (bank 9 13).shape 179798 2369 44 1 1 17 1) 0 925 = 425229040725394944745767060 :=
  phaseBlock_append rec_9_13_2369_1_join2 rec_9_13_2369_1_join5 rfl rfl rfl

private theorem rec_9_13_2369_1 : fastPhase (bank 9 13).shape 179798 2369 44 1 1 17 1 = 425229040725394944745767060 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_9_13_2369_1_join6

theorem receipt_9_13 : Checked (bank 9 13) 44 1 17 := by
  refine checked_from_values (bank 9 13) 44 1 17
    (P3_7_1.checked (bank 9 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_13_2368_0 rec_9_13_2368_1 rec_9_13_2369_0 rec_9_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 0 128 = 1459798488235136362784865728 := by decide +kernel
private theorem rec_9_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 128 128 = 1217853966284721582267137472 := by decide +kernel
private theorem rec_9_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 256 128 = 999836799814906747724578240 := by decide +kernel
private theorem rec_9_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 384 128 = 804572232260132502466657728 := by decide +kernel
private theorem rec_9_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 512 128 = 630879384073040241118199232 := by decide +kernel
private theorem rec_9_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 640 128 = 477573982743366293249490368 := by decide +kernel
private theorem rec_9_14_2368_0_part6 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 768 128 = 343471092816836107006393792 := by decide +kernel
private theorem rec_9_14_2368_0_part7 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 896 128 = 227387845914058432740457920 := by decide +kernel
private theorem rec_9_14_2368_0_part8 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 1024 128 = 128146170749419506639027648 := by decide +kernel
private theorem rec_9_14_2368_0_part9 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 1152 128 = 44575523149977234355355072 := by decide +kernel
private theorem rec_9_14_2368_0_part10 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 1280 14 = 435250640772521527811200 := by decide +kernel
private theorem rec_9_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 0 256 = 2677652454519857945052003200 :=
  phaseBlock_append rec_9_14_2368_0_part0 rec_9_14_2368_0_part1 rfl rfl rfl
private theorem rec_9_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 384 256 = 1435451616333172743584856960 :=
  phaseBlock_append rec_9_14_2368_0_part3 rec_9_14_2368_0_part4 rfl rfl rfl
private theorem rec_9_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 256 384 = 2435288416148079491309435200 :=
  phaseBlock_append rec_9_14_2368_0_part2 rec_9_14_2368_0_join1 rfl rfl rfl
private theorem rec_9_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 0 640 = 5112940870667937436361438400 :=
  phaseBlock_append rec_9_14_2368_0_join0 rec_9_14_2368_0_join2 rfl rfl rfl
private theorem rec_9_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 768 256 = 570858938730894539746851712 :=
  phaseBlock_append rec_9_14_2368_0_part6 rec_9_14_2368_0_part7 rfl rfl rfl
private theorem rec_9_14_2368_0_join5 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 640 384 = 1048432921474260832996342080 :=
  phaseBlock_append rec_9_14_2368_0_part5 rec_9_14_2368_0_join4 rfl rfl rfl
private theorem rec_9_14_2368_0_join6 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 1152 142 = 45010773790749755883166272 :=
  phaseBlock_append rec_9_14_2368_0_part9 rec_9_14_2368_0_part10 rfl rfl rfl
private theorem rec_9_14_2368_0_join7 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 1024 270 = 173156944540169262522193920 :=
  phaseBlock_append rec_9_14_2368_0_part8 rec_9_14_2368_0_join6 rfl rfl rfl
private theorem rec_9_14_2368_0_join8 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 640 654 = 1221589866014430095518536000 :=
  phaseBlock_append rec_9_14_2368_0_join5 rec_9_14_2368_0_join7 rfl rfl rfl
private theorem rec_9_14_2368_0_join9 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 0) 0 1294 = 6334530736682367531879974400 :=
  phaseBlock_append rec_9_14_2368_0_join3 rec_9_14_2368_0_join8 rfl rfl rfl

private theorem rec_9_14_2368_0 : fastPhase (bank 9 14).shape 179798 2368 76 1 1 17 0 = 6334530736682367531879974400 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_9_14_2368_0_join9

private theorem rec_9_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 0 128 = 1457832826309205586356516672 := by decide +kernel
private theorem rec_9_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 128 128 = 1216076247300065731602380608 := by decide +kernel
private theorem rec_9_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 256 128 = 998238268407265420436453184 := by decide +kernel
private theorem rec_9_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 384 128 = 803144048183661163367823168 := by decide +kernel
private theorem rec_9_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 512 128 = 629612644375092437208774464 := by decide +kernel
private theorem rec_9_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 640 128 = 476459743939275868704896832 := by decide +kernel
private theorem rec_9_14_2368_1_part6 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 768 128 = 342500393064699418165196608 := by decide +kernel
private theorem rec_9_14_2368_1_part7 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 896 128 = 226551727189516563092207424 := by decide +kernel
private theorem rec_9_14_2368_1_part8 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 1024 128 = 127435701020440481812100928 := by decide +kernel
private theorem rec_9_14_2368_1_part9 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 1152 128 = 43981818551638237104797504 := by decide +kernel
private theorem rec_9_14_2368_1_part10 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 1280 14 = 377021452604496773614996 := by decide +kernel
private theorem rec_9_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 0 256 = 2673909073609271317958897280 :=
  phaseBlock_append rec_9_14_2368_1_part0 rec_9_14_2368_1_part1 rfl rfl rfl
private theorem rec_9_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 384 256 = 1432756692558753600576597632 :=
  phaseBlock_append rec_9_14_2368_1_part3 rec_9_14_2368_1_part4 rfl rfl rfl
private theorem rec_9_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 256 384 = 2430994960966019021013050816 :=
  phaseBlock_append rec_9_14_2368_1_part2 rec_9_14_2368_1_join1 rfl rfl rfl
private theorem rec_9_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 0 640 = 5104904034575290338971948096 :=
  phaseBlock_append rec_9_14_2368_1_join0 rec_9_14_2368_1_join2 rfl rfl rfl
private theorem rec_9_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 768 256 = 569052120254215981257404032 :=
  phaseBlock_append rec_9_14_2368_1_part6 rec_9_14_2368_1_part7 rfl rfl rfl
private theorem rec_9_14_2368_1_join5 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 640 384 = 1045511864193491849962300864 :=
  phaseBlock_append rec_9_14_2368_1_part5 rec_9_14_2368_1_join4 rfl rfl rfl
private theorem rec_9_14_2368_1_join6 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 1152 142 = 44358840004242733878412500 :=
  phaseBlock_append rec_9_14_2368_1_part9 rec_9_14_2368_1_part10 rfl rfl rfl
private theorem rec_9_14_2368_1_join7 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 1024 270 = 171794541024683215690513428 :=
  phaseBlock_append rec_9_14_2368_1_part8 rec_9_14_2368_1_join6 rfl rfl rfl
private theorem rec_9_14_2368_1_join8 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 640 654 = 1217306405218175065652814292 :=
  phaseBlock_append rec_9_14_2368_1_join5 rec_9_14_2368_1_join7 rfl rfl rfl
private theorem rec_9_14_2368_1_join9 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2368 76 1 1 17 1) 0 1294 = 6322210439793465404624762388 :=
  phaseBlock_append rec_9_14_2368_1_join3 rec_9_14_2368_1_join8 rfl rfl rfl

private theorem rec_9_14_2368_1 : fastPhase (bank 9 14).shape 179798 2368 76 1 1 17 1 = 6322210439793465404624762388 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_9_14_2368_1_join9

private theorem rec_9_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 0 128 = 1459811097363333163199646240 := by decide +kernel
private theorem rec_9_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 128 128 = 1217863374551061374680807968 := by decide +kernel
private theorem rec_9_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 256 128 = 999843628328096132061538848 := by decide +kernel
private theorem rec_9_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 384 128 = 804577019700751275276671520 := by decide +kernel
private theorem rec_9_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 512 128 = 630882593381549982259350048 := by decide +kernel
private theorem rec_9_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 640 128 = 477576007553911864229329440 := by decide +kernel
private theorem rec_9_14_2369_0_part6 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 768 128 = 343472263636840060981275168 := by decide +kernel
private theorem rec_9_14_2369_0_part7 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 896 128 = 227388436049608336173062688 := by decide +kernel
private theorem rec_9_14_2369_0_part8 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 1024 128 = 128146401976448172614076960 := by decide +kernel
private theorem rec_9_14_2369_0_part9 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 1152 128 = 44575571131235867553511968 := by decide +kernel
private theorem rec_9_14_2369_0_part10 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 1280 14 = 435250877416578875262324 := by decide +kernel
private theorem rec_9_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 0 256 = 2677674471914394537880454208 :=
  phaseBlock_append rec_9_14_2369_0_part0 rec_9_14_2369_0_part1 rfl rfl rfl
private theorem rec_9_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 384 256 = 1435459613082301257536021568 :=
  phaseBlock_append rec_9_14_2369_0_part3 rec_9_14_2369_0_part4 rfl rfl rfl
private theorem rec_9_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 256 384 = 2435303241410397389597560416 :=
  phaseBlock_append rec_9_14_2369_0_part2 rec_9_14_2369_0_join1 rfl rfl rfl
private theorem rec_9_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 0 640 = 5112977713324791927478014624 :=
  phaseBlock_append rec_9_14_2369_0_join0 rec_9_14_2369_0_join2 rfl rfl rfl
private theorem rec_9_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 768 256 = 570860699686448397154337856 :=
  phaseBlock_append rec_9_14_2369_0_part6 rec_9_14_2369_0_part7 rfl rfl rfl
private theorem rec_9_14_2369_0_join5 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 640 384 = 1048436707240360261383667296 :=
  phaseBlock_append rec_9_14_2369_0_part5 rec_9_14_2369_0_join4 rfl rfl rfl
private theorem rec_9_14_2369_0_join6 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 1152 142 = 45010822008652446428774292 :=
  phaseBlock_append rec_9_14_2369_0_part9 rec_9_14_2369_0_part10 rfl rfl rfl
private theorem rec_9_14_2369_0_join7 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 1024 270 = 173157223985100619042851252 :=
  phaseBlock_append rec_9_14_2369_0_part8 rec_9_14_2369_0_join6 rfl rfl rfl
private theorem rec_9_14_2369_0_join8 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 640 654 = 1221593931225460880426518548 :=
  phaseBlock_append rec_9_14_2369_0_join5 rec_9_14_2369_0_join7 rfl rfl rfl
private theorem rec_9_14_2369_0_join9 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 0) 0 1294 = 6334571644550252807904533172 :=
  phaseBlock_append rec_9_14_2369_0_join3 rec_9_14_2369_0_join8 rfl rfl rfl

private theorem rec_9_14_2369_0 : fastPhase (bank 9 14).shape 179798 2369 76 1 1 17 0 = 6334571644550252807904533172 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_9_14_2369_0_join9

private theorem rec_9_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 0 128 = 1457845416359320400642668704 := by decide +kernel
private theorem rec_9_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 128 128 = 1216085640190765902444554400 := by decide +kernel
private theorem rec_9_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 256 128 = 998245084742111281457813664 := by decide +kernel
private theorem rec_9_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 384 128 = 803148826180145466903480480 := by decide +kernel
private theorem rec_9_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 512 128 = 629615846551020426829052064 := by decide +kernel
private theorem rec_9_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 640 128 = 476461763544938263396788384 := by decide +kernel
private theorem rec_9_14_2369_1_part6 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 768 128 = 342501560260838308172011680 := by decide +kernel
private theorem rec_9_14_2369_1_part7 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 896 128 = 226552314971084217411405984 := by decide +kernel
private theorem rec_9_14_2369_1_part8 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 1024 128 = 127435930886151067351316640 := by decide +kernel
private theorem rec_9_14_2369_1_part9 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 1152 128 = 43981865919312449496049824 := by decide +kernel
private theorem rec_9_14_2369_1_part10 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 1280 14 = 377021658080047539469092 := by decide +kernel
private theorem rec_9_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 0 256 = 2673931056550086303087223104 :=
  phaseBlock_append rec_9_14_2369_1_part0 rec_9_14_2369_1_part1 rfl rfl rfl
private theorem rec_9_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 384 256 = 1432764672731165893732532544 :=
  phaseBlock_append rec_9_14_2369_1_part3 rec_9_14_2369_1_part4 rfl rfl rfl
private theorem rec_9_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 256 384 = 2431009757473277175190346208 :=
  phaseBlock_append rec_9_14_2369_1_part2 rec_9_14_2369_1_join1 rfl rfl rfl
private theorem rec_9_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 0 640 = 5104940814023363478277569312 :=
  phaseBlock_append rec_9_14_2369_1_join0 rec_9_14_2369_1_join2 rfl rfl rfl
private theorem rec_9_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 768 256 = 569053875231922525583417664 :=
  phaseBlock_append rec_9_14_2369_1_part6 rec_9_14_2369_1_part7 rfl rfl rfl
private theorem rec_9_14_2369_1_join5 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 640 384 = 1045515638776860788980206048 :=
  phaseBlock_append rec_9_14_2369_1_part5 rec_9_14_2369_1_join4 rfl rfl rfl
private theorem rec_9_14_2369_1_join6 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 1152 142 = 44358887577392497035518916 :=
  phaseBlock_append rec_9_14_2369_1_part9 rec_9_14_2369_1_part10 rfl rfl rfl
private theorem rec_9_14_2369_1_join7 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 1024 270 = 171794818463543564386835556 :=
  phaseBlock_append rec_9_14_2369_1_part8 rec_9_14_2369_1_join6 rfl rfl rfl
private theorem rec_9_14_2369_1_join8 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 640 654 = 1217310457240404353367041604 :=
  phaseBlock_append rec_9_14_2369_1_join5 rec_9_14_2369_1_join7 rfl rfl rfl
private theorem rec_9_14_2369_1_join9 :
    phaseBlock (fastLayerG (bank 9 14).shape 179798 2369 76 1 1 17 1) 0 1294 = 6322251271263767831644610916 :=
  phaseBlock_append rec_9_14_2369_1_join3 rec_9_14_2369_1_join8 rfl rfl rfl

private theorem rec_9_14_2369_1 : fastPhase (bank 9 14).shape 179798 2369 76 1 1 17 1 = 6322251271263767831644610916 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_9_14_2369_1_join9

theorem receipt_9_14 : Checked (bank 9 14) 76 1 17 := by
  refine checked_from_values (bank 9 14) 76 1 17
    (P3_7_1.checked (bank 9 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_14_2368_0 rec_9_14_2368_1 rec_9_14_2369_0 rec_9_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 0 128 = 6128991532845904889335798656 := by decide +kernel
private theorem rec_9_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 128 128 = 5372678415417396977624988544 := by decide +kernel
private theorem rec_9_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 256 128 = 4672922255954213101844372352 := by decide +kernel
private theorem rec_9_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 384 128 = 4027567965407422785042873216 := by decide +kernel
private theorem rec_9_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 512 128 = 3434456319356781526082771840 := by decide +kernel
private theorem rec_9_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 640 128 = 2891426688029624983269817216 := by decide +kernel
private theorem rec_9_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 768 128 = 2396319766319763157983337344 := by decide +kernel
private theorem rec_9_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 896 128 = 1946980303806374578306349952 := by decide +kernel
private theorem rec_9_15_2368_0_part8 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 1024 128 = 1541259834772900482655673216 := by decide +kernel
private theorem rec_9_15_2368_0_part9 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 1152 128 = 1177019408225939003412036480 := by decide +kernel
private theorem rec_9_15_2368_0_part10 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 1280 128 = 852132317914139350550190976 := by decide +kernel
private theorem rec_9_15_2368_0_part11 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 1408 128 = 564486832347095995269020544 := by decide +kernel
private theorem rec_9_15_2368_0_part12 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 1536 128 = 311988924814242853621652352 := by decide +kernel
private theorem rec_9_15_2368_0_part13 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 1664 123 = 92680320468771616706916360 := by decide +kernel
private theorem rec_9_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 128 256 = 10045600671371610079469360896 :=
  phaseBlock_append rec_9_15_2368_0_part1 rec_9_15_2368_0_part2 rfl rfl rfl
private theorem rec_9_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 0 384 = 16174592204217514968805159552 :=
  phaseBlock_append rec_9_15_2368_0_part0 rec_9_15_2368_0_join0 rfl rfl rfl
private theorem rec_9_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 384 256 = 7462024284764204311125645056 :=
  phaseBlock_append rec_9_15_2368_0_part3 rec_9_15_2368_0_part4 rfl rfl rfl
private theorem rec_9_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 640 256 = 5287746454349388141253154560 :=
  phaseBlock_append rec_9_15_2368_0_part5 rec_9_15_2368_0_part6 rfl rfl rfl
private theorem rec_9_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 384 512 = 12749770739113592452378799616 :=
  phaseBlock_append rec_9_15_2368_0_join2 rec_9_15_2368_0_join3 rfl rfl rfl
private theorem rec_9_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 0 896 = 28924362943331107421183959168 :=
  phaseBlock_append rec_9_15_2368_0_join1 rec_9_15_2368_0_join4 rfl rfl rfl
private theorem rec_9_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 1024 256 = 2718279242998839486067709696 :=
  phaseBlock_append rec_9_15_2368_0_part8 rec_9_15_2368_0_part9 rfl rfl rfl
private theorem rec_9_15_2368_0_join7 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 896 384 = 4665259546805214064374059648 :=
  phaseBlock_append rec_9_15_2368_0_part7 rec_9_15_2368_0_join6 rfl rfl rfl
private theorem rec_9_15_2368_0_join8 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 1280 256 = 1416619150261235345819211520 :=
  phaseBlock_append rec_9_15_2368_0_part10 rec_9_15_2368_0_part11 rfl rfl rfl
private theorem rec_9_15_2368_0_join9 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 1536 251 = 404669245283014470328568712 :=
  phaseBlock_append rec_9_15_2368_0_part12 rec_9_15_2368_0_part13 rfl rfl rfl
private theorem rec_9_15_2368_0_join10 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 1280 507 = 1821288395544249816147780232 :=
  phaseBlock_append rec_9_15_2368_0_join8 rec_9_15_2368_0_join9 rfl rfl rfl
private theorem rec_9_15_2368_0_join11 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 896 891 = 6486547942349463880521839880 :=
  phaseBlock_append rec_9_15_2368_0_join7 rec_9_15_2368_0_join10 rfl rfl rfl
private theorem rec_9_15_2368_0_join12 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 0) 0 1787 = 35410910885680571301705799048 :=
  phaseBlock_append rec_9_15_2368_0_join5 rec_9_15_2368_0_join11 rfl rfl rfl

private theorem rec_9_15_2368_0 : fastPhase (bank 9 15).shape 179798 2368 105 1 1 17 0 = 35410910885680571301705799048 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_9_15_2368_0_join12

private theorem rec_9_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 0 128 = 6122919836308708140116587264 := by decide +kernel
private theorem rec_9_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 128 128 = 5367048914806525311245390592 := by decide +kernel
private theorem rec_9_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 256 128 = 4667718807793799012932743936 := by decide +kernel
private theorem rec_9_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 384 128 = 4022774348819183423831036672 := by decide +kernel
private theorem rec_9_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 512 128 = 3430056258234800913393857280 := by decide +kernel
private theorem rec_9_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 640 128 = 2887403873215136225506104064 := by decide +kernel
private theorem rec_9_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 768 128 = 2392657877775930662114095872 := by decide +kernel
private theorem rec_9_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 896 128 = 1943663032793076266855682816 := by decide +kernel
private theorem rec_9_15_2368_1_part8 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 1024 128 = 1538270906021510008690356992 := by decide +kernel
private theorem rec_9_15_2368_1_part9 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 1152 128 = 1174342602114107965529363200 := by decide +kernel
private theorem rec_9_15_2368_1_part10 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 1280 128 = 849751492640579507865809664 := by decide +kernel
private theorem rec_9_15_2368_1_part11 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 1408 128 = 562385946106361482404778752 := by decide +kernel
private theorem rec_9_15_2368_1_part12 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 1536 128 = 310152057971512395693437696 := by decide +kernel
private theorem rec_9_15_2368_1_part13 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 1664 123 = 91149286245864865620632704 := by decide +kernel
private theorem rec_9_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 128 256 = 10034767722600324324178134528 :=
  phaseBlock_append rec_9_15_2368_1_part1 rec_9_15_2368_1_part2 rfl rfl rfl
private theorem rec_9_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 0 384 = 16157687558909032464294721792 :=
  phaseBlock_append rec_9_15_2368_1_part0 rec_9_15_2368_1_join0 rfl rfl rfl
private theorem rec_9_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 384 256 = 7452830607053984337224893952 :=
  phaseBlock_append rec_9_15_2368_1_part3 rec_9_15_2368_1_part4 rfl rfl rfl
private theorem rec_9_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 640 256 = 5280061750991066887620199936 :=
  phaseBlock_append rec_9_15_2368_1_part5 rec_9_15_2368_1_part6 rfl rfl rfl
private theorem rec_9_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 384 512 = 12732892358045051224845093888 :=
  phaseBlock_append rec_9_15_2368_1_join2 rec_9_15_2368_1_join3 rfl rfl rfl
private theorem rec_9_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 0 896 = 28890579916954083689139815680 :=
  phaseBlock_append rec_9_15_2368_1_join1 rec_9_15_2368_1_join4 rfl rfl rfl
private theorem rec_9_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 1024 256 = 2712613508135617974219720192 :=
  phaseBlock_append rec_9_15_2368_1_part8 rec_9_15_2368_1_part9 rfl rfl rfl
private theorem rec_9_15_2368_1_join7 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 896 384 = 4656276540928694241075403008 :=
  phaseBlock_append rec_9_15_2368_1_part7 rec_9_15_2368_1_join6 rfl rfl rfl
private theorem rec_9_15_2368_1_join8 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 1280 256 = 1412137438746940990270588416 :=
  phaseBlock_append rec_9_15_2368_1_part10 rec_9_15_2368_1_part11 rfl rfl rfl
private theorem rec_9_15_2368_1_join9 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 1536 251 = 401301344217377261314070400 :=
  phaseBlock_append rec_9_15_2368_1_part12 rec_9_15_2368_1_part13 rfl rfl rfl
private theorem rec_9_15_2368_1_join10 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 1280 507 = 1813438782964318251584658816 :=
  phaseBlock_append rec_9_15_2368_1_join8 rec_9_15_2368_1_join9 rfl rfl rfl
private theorem rec_9_15_2368_1_join11 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 896 891 = 6469715323893012492660061824 :=
  phaseBlock_append rec_9_15_2368_1_join7 rec_9_15_2368_1_join10 rfl rfl rfl
private theorem rec_9_15_2368_1_join12 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2368 105 1 1 17 1) 0 1787 = 35360295240847096181799877504 :=
  phaseBlock_append rec_9_15_2368_1_join5 rec_9_15_2368_1_join11 rfl rfl rfl

private theorem rec_9_15_2368_1 : fastPhase (bank 9 15).shape 179798 2368 105 1 1 17 1 = 35360295240847096181799877504 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_9_15_2368_1_join12

private theorem rec_9_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 0 128 = 6129045200536984744779457056 := by decide +kernel
private theorem rec_9_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 128 128 = 5372721891952846626210664992 := by decide +kernel
private theorem rec_9_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 256 128 = 4672957007068058729756525088 := by decide +kernel
private theorem rec_9_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 384 128 = 4027595312007658485945578016 := by decide +kernel
private theorem rec_9_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 512 128 = 3434477446359244360356651552 := by decide +kernel
private theorem rec_9_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 640 128 = 2891442652937662948907160096 := by decide +kernel
private theorem rec_9_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 768 128 = 2396331507549696073141404192 := by decide +kernel
private theorem rec_9_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 896 128 = 1946988648758747875518870048 := by decide +kernel
private theorem rec_9_15_2369_0_part8 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 1024 128 = 1541265507649531914702529056 := by decide +kernel
private theorem rec_9_15_2369_0_part9 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 1152 128 = 1177023037592758260847137312 := by decide +kernel
private theorem rec_9_15_2369_0_part10 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 1280 128 = 852134444009820590887535136 := by decide +kernel
private theorem rec_9_15_2369_0_part11 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 1408 128 = 564487914137483283826946592 := by decide +kernel
private theorem rec_9_15_2369_0_part12 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 1536 128 = 311989346792568516025279008 := by decide +kernel
private theorem rec_9_15_2369_0_part13 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 1664 123 = 92680399255982307814247373 := by decide +kernel
private theorem rec_9_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 128 256 = 10045678899020905355967190080 :=
  phaseBlock_append rec_9_15_2369_0_part1 rec_9_15_2369_0_part2 rfl rfl rfl
private theorem rec_9_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 0 384 = 16174724099557890100746647136 :=
  phaseBlock_append rec_9_15_2369_0_part0 rec_9_15_2369_0_join0 rfl rfl rfl
private theorem rec_9_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 384 256 = 7462072758366902846302229568 :=
  phaseBlock_append rec_9_15_2369_0_part3 rec_9_15_2369_0_part4 rfl rfl rfl
private theorem rec_9_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 640 256 = 5287774160487359022048564288 :=
  phaseBlock_append rec_9_15_2369_0_part5 rec_9_15_2369_0_part6 rfl rfl rfl
private theorem rec_9_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 384 512 = 12749846918854261868350793856 :=
  phaseBlock_append rec_9_15_2369_0_join2 rec_9_15_2369_0_join3 rfl rfl rfl
private theorem rec_9_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 0 896 = 28924571018412151969097440992 :=
  phaseBlock_append rec_9_15_2369_0_join1 rec_9_15_2369_0_join4 rfl rfl rfl
private theorem rec_9_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 1024 256 = 2718288545242290175549666368 :=
  phaseBlock_append rec_9_15_2369_0_part8 rec_9_15_2369_0_part9 rfl rfl rfl
private theorem rec_9_15_2369_0_join7 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 896 384 = 4665277194001038051068536416 :=
  phaseBlock_append rec_9_15_2369_0_part7 rec_9_15_2369_0_join6 rfl rfl rfl
private theorem rec_9_15_2369_0_join8 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 1280 256 = 1416622358147303874714481728 :=
  phaseBlock_append rec_9_15_2369_0_part10 rec_9_15_2369_0_part11 rfl rfl rfl
private theorem rec_9_15_2369_0_join9 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 1536 251 = 404669746048550823839526381 :=
  phaseBlock_append rec_9_15_2369_0_part12 rec_9_15_2369_0_part13 rfl rfl rfl
private theorem rec_9_15_2369_0_join10 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 1280 507 = 1821292104195854698554008109 :=
  phaseBlock_append rec_9_15_2369_0_join8 rec_9_15_2369_0_join9 rfl rfl rfl
private theorem rec_9_15_2369_0_join11 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 896 891 = 6486569298196892749622544525 :=
  phaseBlock_append rec_9_15_2369_0_join7 rec_9_15_2369_0_join10 rfl rfl rfl
private theorem rec_9_15_2369_0_join12 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 0) 0 1787 = 35411140316609044718719985517 :=
  phaseBlock_append rec_9_15_2369_0_join5 rec_9_15_2369_0_join11 rfl rfl rfl

private theorem rec_9_15_2369_0 : fastPhase (bank 9 15).shape 179798 2369 105 1 1 17 0 = 35411140316609044718719985517 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_9_15_2369_0_join12

private theorem rec_9_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 0 128 = 6122973444380460757966493664 := by decide +kernel
private theorem rec_9_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 128 128 = 5367092340383245351026968544 := by decide +kernel
private theorem rec_9_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 256 128 = 4667753515726150146765289440 := by decide +kernel
private theorem rec_9_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 384 128 = 4022801659187221948169824224 := by decide +kernel
private theorem rec_9_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 512 128 = 3430077355180222294107379680 := by decide +kernel
private theorem rec_9_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 640 128 = 2887419813519314554611501024 := by decide +kernel
private theorem rec_9_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 768 128 = 2392669599183751026170771424 := by decide +kernel
private theorem rec_9_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 896 128 = 1943671362082560027017111520 := by decide +kernel
private theorem rec_9_15_2369_1_part8 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 1024 128 = 1538276566819232992414078944 := by decide +kernel
private theorem rec_9_15_2369_1_part9 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 1152 128 = 1174346222456411569945167840 := by decide +kernel
private theorem rec_9_15_2369_1_part10 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 1280 128 = 849753612280574714802108384 := by decide +kernel
private theorem rec_9_15_2369_1_part11 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 1408 128 = 562387023566725785073166304 := by decide +kernel
private theorem rec_9_15_2369_1_part12 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 1536 128 = 310152477343079637031442400 := by decide +kernel
private theorem rec_9_15_2369_1_part13 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 1664 123 = 91149363813611748394957050 := by decide +kernel
private theorem rec_9_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 128 256 = 10034845856109395497792257984 :=
  phaseBlock_append rec_9_15_2369_1_part1 rec_9_15_2369_1_part2 rfl rfl rfl
private theorem rec_9_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 0 384 = 16157819300489856255758751648 :=
  phaseBlock_append rec_9_15_2369_1_part0 rec_9_15_2369_1_join0 rfl rfl rfl
private theorem rec_9_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 384 256 = 7452879014367444242277203904 :=
  phaseBlock_append rec_9_15_2369_1_part3 rec_9_15_2369_1_part4 rfl rfl rfl
private theorem rec_9_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 640 256 = 5280089412703065580782272448 :=
  phaseBlock_append rec_9_15_2369_1_part5 rec_9_15_2369_1_part6 rfl rfl rfl
private theorem rec_9_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 384 512 = 12732968427070509823059476352 :=
  phaseBlock_append rec_9_15_2369_1_join2 rec_9_15_2369_1_join3 rfl rfl rfl
private theorem rec_9_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 0 896 = 28890787727560366078818228000 :=
  phaseBlock_append rec_9_15_2369_1_join1 rec_9_15_2369_1_join4 rfl rfl rfl
private theorem rec_9_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 1024 256 = 2712622789275644562359246784 :=
  phaseBlock_append rec_9_15_2369_1_part8 rec_9_15_2369_1_part9 rfl rfl rfl
private theorem rec_9_15_2369_1_join7 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 896 384 = 4656294151358204589376358304 :=
  phaseBlock_append rec_9_15_2369_1_part7 rec_9_15_2369_1_join6 rfl rfl rfl
private theorem rec_9_15_2369_1_join8 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 1280 256 = 1412140635847300499875274688 :=
  phaseBlock_append rec_9_15_2369_1_part10 rec_9_15_2369_1_part11 rfl rfl rfl
private theorem rec_9_15_2369_1_join9 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 1536 251 = 401301841156691385426399450 :=
  phaseBlock_append rec_9_15_2369_1_part12 rec_9_15_2369_1_part13 rfl rfl rfl
private theorem rec_9_15_2369_1_join10 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 1280 507 = 1813442477003991885301674138 :=
  phaseBlock_append rec_9_15_2369_1_join8 rec_9_15_2369_1_join9 rfl rfl rfl
private theorem rec_9_15_2369_1_join11 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 896 891 = 6469736628362196474678032442 :=
  phaseBlock_append rec_9_15_2369_1_join7 rec_9_15_2369_1_join10 rfl rfl rfl
private theorem rec_9_15_2369_1_join12 :
    phaseBlock (fastLayerG (bank 9 15).shape 179798 2369 105 1 1 17 1) 0 1787 = 35360524355922562553496260442 :=
  phaseBlock_append rec_9_15_2369_1_join5 rec_9_15_2369_1_join11 rfl rfl rfl

private theorem rec_9_15_2369_1 : fastPhase (bank 9 15).shape 179798 2369 105 1 1 17 1 = 35360524355922562553496260442 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_9_15_2369_1_join12

theorem receipt_9_15 : Checked (bank 9 15) 105 1 17 := by
  refine checked_from_values (bank 9 15) 105 1 17
    (P3_7_1.checked (bank 9 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_15_2368_0 rec_9_15_2368_1 rec_9_15_2369_0 rec_9_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 0 128 = 21811659669622413565068310112 := by decide +kernel
private theorem rec_9_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 128 128 = 19743343722782843253635212896 := by decide +kernel
private theorem rec_9_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 256 128 = 17796410042605962802434004576 := by decide +kernel
private theorem rec_9_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 384 128 = 15967121458613730171262256736 := by decide +kernel
private theorem rec_9_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 512 128 = 14251742301886150188244907616 := by decide +kernel
private theorem rec_9_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 640 128 = 12646541135080168733464372832 := by decide +kernel
private theorem rec_9_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 768 128 = 11147793482448566922590656096 := by decide +kernel
private theorem rec_9_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 896 128 = 9751784559858855290511459936 := by decide +kernel
private theorem rec_9_16_2368_0_part8 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1024 128 = 8454812004812167974962296416 := by decide +kernel
private theorem rec_9_16_2368_0_part9 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1152 128 = 7253188606462156900156597856 := by decide +kernel
private theorem rec_9_16_2368_0_part10 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1280 128 = 6143245035633885960415827552 := by decide +kernel
private theorem rec_9_16_2368_0_part11 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1408 128 = 5121332574842725203799590496 := by decide +kernel
private theorem rec_9_16_2368_0_part12 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1536 128 = 4183825848313245015735744096 := by decide +kernel
private theorem rec_9_16_2368_0_part13 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1664 128 = 3327125551998110302650508896 := by decide +kernel
private theorem rec_9_16_2368_0_part14 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1792 128 = 2547661183596974675598579296 := by decide +kernel
private theorem rec_9_16_2368_0_part15 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1920 128 = 1841893772575374633893234272 := by decide +kernel
private theorem rec_9_16_2368_0_part16 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 2048 128 = 1206318610183623748736448096 := by decide +kernel
private theorem rec_9_16_2368_0_part17 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 2176 128 = 637467979475706846849001056 := by decide +kernel
private theorem rec_9_16_2368_0_part18 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 2304 99 = 143165357200242598232362065 := by decide +kernel
private theorem rec_9_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 0 256 = 41555003392405256818703523008 :=
  phaseBlock_append rec_9_16_2368_0_part0 rec_9_16_2368_0_part1 rfl rfl rfl
private theorem rec_9_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 256 256 = 33763531501219692973696261312 :=
  phaseBlock_append rec_9_16_2368_0_part2 rec_9_16_2368_0_part3 rfl rfl rfl
private theorem rec_9_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 0 512 = 75318534893624949792399784320 :=
  phaseBlock_append rec_9_16_2368_0_join0 rec_9_16_2368_0_join1 rfl rfl rfl
private theorem rec_9_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 512 256 = 26898283436966318921709280448 :=
  phaseBlock_append rec_9_16_2368_0_part4 rec_9_16_2368_0_part5 rfl rfl rfl
private theorem rec_9_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 896 256 = 18206596564671023265473756352 :=
  phaseBlock_append rec_9_16_2368_0_part7 rec_9_16_2368_0_part8 rfl rfl rfl
private theorem rec_9_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 768 384 = 29354390047119590188064412448 :=
  phaseBlock_append rec_9_16_2368_0_part6 rec_9_16_2368_0_join4 rfl rfl rfl
private theorem rec_9_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 512 640 = 56252673484085909109773692896 :=
  phaseBlock_append rec_9_16_2368_0_join3 rec_9_16_2368_0_join5 rfl rfl rfl
private theorem rec_9_16_2368_0_join7 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 0 1152 = 131571208377710858902173477216 :=
  phaseBlock_append rec_9_16_2368_0_join2 rec_9_16_2368_0_join6 rfl rfl rfl
private theorem rec_9_16_2368_0_join8 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1152 256 = 13396433642096042860572425408 :=
  phaseBlock_append rec_9_16_2368_0_part9 rec_9_16_2368_0_part10 rfl rfl rfl
private theorem rec_9_16_2368_0_join9 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1536 256 = 7510951400311355318386252992 :=
  phaseBlock_append rec_9_16_2368_0_part12 rec_9_16_2368_0_part13 rfl rfl rfl
private theorem rec_9_16_2368_0_join10 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1408 384 = 12632283975154080522185843488 :=
  phaseBlock_append rec_9_16_2368_0_part11 rec_9_16_2368_0_join9 rfl rfl rfl
private theorem rec_9_16_2368_0_join11 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1152 640 = 26028717617250123382758268896 :=
  phaseBlock_append rec_9_16_2368_0_join8 rec_9_16_2368_0_join10 rfl rfl rfl
private theorem rec_9_16_2368_0_join12 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1792 256 = 4389554956172349309491813568 :=
  phaseBlock_append rec_9_16_2368_0_part14 rec_9_16_2368_0_part15 rfl rfl rfl
private theorem rec_9_16_2368_0_join13 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 2176 227 = 780633336675949445081363121 :=
  phaseBlock_append rec_9_16_2368_0_part17 rec_9_16_2368_0_part18 rfl rfl rfl
private theorem rec_9_16_2368_0_join14 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 2048 355 = 1986951946859573193817811217 :=
  phaseBlock_append rec_9_16_2368_0_part16 rec_9_16_2368_0_join13 rfl rfl rfl
private theorem rec_9_16_2368_0_join15 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1792 611 = 6376506903031922503309624785 :=
  phaseBlock_append rec_9_16_2368_0_join12 rec_9_16_2368_0_join14 rfl rfl rfl
private theorem rec_9_16_2368_0_join16 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 1152 1251 = 32405224520282045886067893681 :=
  phaseBlock_append rec_9_16_2368_0_join11 rec_9_16_2368_0_join15 rfl rfl rfl
private theorem rec_9_16_2368_0_join17 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 0) 0 2403 = 163976432897992904788241370897 :=
  phaseBlock_append rec_9_16_2368_0_join7 rec_9_16_2368_0_join16 rfl rfl rfl

private theorem rec_9_16_2368_0 : fastPhase (bank 9 16).shape 179798 2368 138 1 1 17 0 = 163976432897992904788241370897 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_9_16_2368_0_join17

private theorem rec_9_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 0 128 = 21795184433893225404355661472 := by decide +kernel
private theorem rec_9_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 128 128 = 19727814999755322346837130912 := by decide +kernel
private theorem rec_9_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 256 128 = 17781799701964353582384492192 := by decide +kernel
private theorem rec_9_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 384 128 = 15953401327840918423145946784 := by decide +kernel
private theorem rec_9_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 512 128 = 14238884188438445264584904352 := by decide +kernel
private theorem rec_9_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 640 128 = 12634516848562085769110093472 := by decide +kernel
private theorem rec_9_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 768 128 = 11136574856787609049705672352 := by decide +kernel
private theorem rec_9_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 896 128 = 9741343475480295853561339552 := by decide +kernel
private theorem rec_9_16_2368_1_part8 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1024 128 = 8445120410813832745702444704 := by decide +kernel
private theorem rec_9_16_2368_1_part9 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1152 128 = 7244218542789206292620099232 := by decide +kernel
private theorem rec_9_16_2368_1_part10 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1280 128 = 6134968655253597245901287072 := by decide +kernel
private theorem rec_9_16_2368_1_part11 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1408 128 = 5113722165919274725858975392 := by decide +kernel
private theorem rec_9_16_2368_1_part12 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1536 128 = 4176853856382490405162225312 := by decide +kernel
private theorem rec_9_16_2368_1_part13 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1664 128 = 3320764602142372692466302624 := by decide +kernel
private theorem rec_9_16_2368_1_part14 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1792 128 = 2541884102619820916042788512 := by decide +kernel
private theorem rec_9_16_2368_1_part15 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1920 128 = 1836673611176399507409690272 := by decide +kernel
private theorem rec_9_16_2368_1_part16 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 2048 128 = 1201628665133232184961552032 := by decide +kernel
private theorem rec_9_16_2368_1_part17 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 2176 128 = 633281815789896137599565472 := by decide +kernel
private theorem rec_9_16_2368_1_part18 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 2304 99 = 140256537923819121164584455 := by decide +kernel
private theorem rec_9_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 0 256 = 41522999433648547751192792384 :=
  phaseBlock_append rec_9_16_2368_1_part0 rec_9_16_2368_1_part1 rfl rfl rfl
private theorem rec_9_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 256 256 = 33735201029805272005530438976 :=
  phaseBlock_append rec_9_16_2368_1_part2 rec_9_16_2368_1_part3 rfl rfl rfl
private theorem rec_9_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 0 512 = 75258200463453819756723231360 :=
  phaseBlock_append rec_9_16_2368_1_join0 rec_9_16_2368_1_join1 rfl rfl rfl
private theorem rec_9_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 512 256 = 26873401037000531033694997824 :=
  phaseBlock_append rec_9_16_2368_1_part4 rec_9_16_2368_1_part5 rfl rfl rfl
private theorem rec_9_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 896 256 = 18186463886294128599263784256 :=
  phaseBlock_append rec_9_16_2368_1_part7 rec_9_16_2368_1_part8 rfl rfl rfl
private theorem rec_9_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 768 384 = 29323038743081737648969456608 :=
  phaseBlock_append rec_9_16_2368_1_part6 rec_9_16_2368_1_join4 rfl rfl rfl
private theorem rec_9_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 512 640 = 56196439780082268682664454432 :=
  phaseBlock_append rec_9_16_2368_1_join3 rec_9_16_2368_1_join5 rfl rfl rfl
private theorem rec_9_16_2368_1_join7 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 0 1152 = 131454640243536088439387685792 :=
  phaseBlock_append rec_9_16_2368_1_join2 rec_9_16_2368_1_join6 rfl rfl rfl
private theorem rec_9_16_2368_1_join8 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1152 256 = 13379187198042803538521386304 :=
  phaseBlock_append rec_9_16_2368_1_part9 rec_9_16_2368_1_part10 rfl rfl rfl
private theorem rec_9_16_2368_1_join9 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1536 256 = 7497618458524863097628527936 :=
  phaseBlock_append rec_9_16_2368_1_part12 rec_9_16_2368_1_part13 rfl rfl rfl
private theorem rec_9_16_2368_1_join10 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1408 384 = 12611340624444137823487503328 :=
  phaseBlock_append rec_9_16_2368_1_part11 rec_9_16_2368_1_join9 rfl rfl rfl
private theorem rec_9_16_2368_1_join11 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1152 640 = 25990527822486941362008889632 :=
  phaseBlock_append rec_9_16_2368_1_join8 rec_9_16_2368_1_join10 rfl rfl rfl
private theorem rec_9_16_2368_1_join12 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1792 256 = 4378557713796220423452478784 :=
  phaseBlock_append rec_9_16_2368_1_part14 rec_9_16_2368_1_part15 rfl rfl rfl
private theorem rec_9_16_2368_1_join13 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 2176 227 = 773538353713715258764149927 :=
  phaseBlock_append rec_9_16_2368_1_part17 rec_9_16_2368_1_part18 rfl rfl rfl
private theorem rec_9_16_2368_1_join14 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 2048 355 = 1975167018846947443725701959 :=
  phaseBlock_append rec_9_16_2368_1_part16 rec_9_16_2368_1_join13 rfl rfl rfl
private theorem rec_9_16_2368_1_join15 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1792 611 = 6353724732643167867178180743 :=
  phaseBlock_append rec_9_16_2368_1_join12 rec_9_16_2368_1_join14 rfl rfl rfl
private theorem rec_9_16_2368_1_join16 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 1152 1251 = 32344252555130109229187070375 :=
  phaseBlock_append rec_9_16_2368_1_join11 rec_9_16_2368_1_join15 rfl rfl rfl
private theorem rec_9_16_2368_1_join17 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2368 138 1 1 17 1) 0 2403 = 163798892798666197668574756167 :=
  phaseBlock_append rec_9_16_2368_1_join7 rec_9_16_2368_1_join16 rfl rfl rfl

private theorem rec_9_16_2368_1 : fastPhase (bank 9 16).shape 179798 2368 138 1 1 17 1 = 163798892798666197668574756167 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_9_16_2368_1_join17

private theorem rec_9_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 0 128 = 21811852677114508934360786560 := by decide +kernel
private theorem rec_9_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 128 128 = 19743508640635665432529913472 := by decide +kernel
private theorem rec_9_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 256 128 = 17796549961805846284293547648 := by decide +kernel
private theorem rec_9_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 384 128 = 15967239234383137949924755072 := by decide +kernel
private theorem rec_9_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 512 128 = 14251840564907088438287296128 := by decide +kernel
private theorem rec_9_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 640 128 = 12646622302463394402123925120 := by decide +kernel
private theorem rec_9_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 768 128 = 11147859768448588233344689792 := by decide +kernel
private theorem rec_9_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 896 128 = 9751837986334725158315230848 := by decide +kernel
private theorem rec_9_16_2369_0_part8 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1024 128 = 8454854411434070333145081472 := by decide +kernel
private theorem rec_9_16_2369_0_part9 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1152 128 = 7253221660663785938975966848 := by decide +kernel
private theorem rec_9_16_2369_0_part10 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1280 128 = 6143270242310618277270103680 := by decide +kernel
private theorem rec_9_16_2369_0_part11 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1408 128 = 5121351285795584865098499712 := by decide +kernel
private theorem rec_9_16_2369_0_part12 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1536 128 = 4183839271438661530429253248 := by decide +kernel
private theorem rec_9_16_2369_0_part13 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1664 128 = 3327134760223469507415852672 := by decide +kernel
private theorem rec_9_16_2369_0_part14 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1792 128 = 2547667123561962531685475968 := by decide +kernel
private theorem rec_9_16_2369_0_part15 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1920 128 = 1841897273059113935627290240 := by decide +kernel
private theorem rec_9_16_2369_0_part16 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 2048 128 = 1206320390277603743680751232 := by decide +kernel
private theorem rec_9_16_2369_0_part17 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 2176 128 = 637468656502505767623902848 := by decide +kernel
private theorem rec_9_16_2369_0_part18 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 2304 99 = 143165459242970929167671400 := by decide +kernel
private theorem rec_9_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 0 256 = 41555361317750174366890700032 :=
  phaseBlock_append rec_9_16_2369_0_part0 rec_9_16_2369_0_part1 rfl rfl rfl
private theorem rec_9_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 256 256 = 33763789196188984234218302720 :=
  phaseBlock_append rec_9_16_2369_0_part2 rec_9_16_2369_0_part3 rfl rfl rfl
private theorem rec_9_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 0 512 = 75319150513939158601109002752 :=
  phaseBlock_append rec_9_16_2369_0_join0 rec_9_16_2369_0_join1 rfl rfl rfl
private theorem rec_9_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 512 256 = 26898462867370482840411221248 :=
  phaseBlock_append rec_9_16_2369_0_part4 rec_9_16_2369_0_part5 rfl rfl rfl
private theorem rec_9_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 896 256 = 18206692397768795491460312320 :=
  phaseBlock_append rec_9_16_2369_0_part7 rec_9_16_2369_0_part8 rfl rfl rfl
private theorem rec_9_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 768 384 = 29354552166217383724805002112 :=
  phaseBlock_append rec_9_16_2369_0_part6 rec_9_16_2369_0_join4 rfl rfl rfl
private theorem rec_9_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 512 640 = 56253015033587866565216223360 :=
  phaseBlock_append rec_9_16_2369_0_join3 rec_9_16_2369_0_join5 rfl rfl rfl
private theorem rec_9_16_2369_0_join7 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 0 1152 = 131572165547527025166325226112 :=
  phaseBlock_append rec_9_16_2369_0_join2 rec_9_16_2369_0_join6 rfl rfl rfl
private theorem rec_9_16_2369_0_join8 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1152 256 = 13396491902974404216246070528 :=
  phaseBlock_append rec_9_16_2369_0_part9 rec_9_16_2369_0_part10 rfl rfl rfl
private theorem rec_9_16_2369_0_join9 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1536 256 = 7510974031662131037845105920 :=
  phaseBlock_append rec_9_16_2369_0_part12 rec_9_16_2369_0_part13 rfl rfl rfl
private theorem rec_9_16_2369_0_join10 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1408 384 = 12632325317457715902943605632 :=
  phaseBlock_append rec_9_16_2369_0_part11 rec_9_16_2369_0_join9 rfl rfl rfl
private theorem rec_9_16_2369_0_join11 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1152 640 = 26028817220432120119189676160 :=
  phaseBlock_append rec_9_16_2369_0_join8 rec_9_16_2369_0_join10 rfl rfl rfl
private theorem rec_9_16_2369_0_join12 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1792 256 = 4389564396621076467312766208 :=
  phaseBlock_append rec_9_16_2369_0_part14 rec_9_16_2369_0_part15 rfl rfl rfl
private theorem rec_9_16_2369_0_join13 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 2176 227 = 780634115745476696791574248 :=
  phaseBlock_append rec_9_16_2369_0_part17 rec_9_16_2369_0_part18 rfl rfl rfl
private theorem rec_9_16_2369_0_join14 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 2048 355 = 1986954506023080440472325480 :=
  phaseBlock_append rec_9_16_2369_0_part16 rec_9_16_2369_0_join13 rfl rfl rfl
private theorem rec_9_16_2369_0_join15 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1792 611 = 6376518902644156907785091688 :=
  phaseBlock_append rec_9_16_2369_0_join12 rec_9_16_2369_0_join14 rfl rfl rfl
private theorem rec_9_16_2369_0_join16 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 1152 1251 = 32405336123076277026974767848 :=
  phaseBlock_append rec_9_16_2369_0_join11 rec_9_16_2369_0_join15 rfl rfl rfl
private theorem rec_9_16_2369_0_join17 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 0) 0 2403 = 163977501670603302193299993960 :=
  phaseBlock_append rec_9_16_2369_0_join7 rec_9_16_2369_0_join16 rfl rfl rfl

private theorem rec_9_16_2369_0 : fastPhase (bank 9 16).shape 179798 2369 138 1 1 17 0 = 163977501670603302193299993960 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_9_16_2369_0_join17

private theorem rec_9_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 0 128 = 21795377278390976675910173376 := by decide +kernel
private theorem rec_9_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 128 128 = 19727979772834851278867808960 := by decide +kernel
private theorem rec_9_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 256 128 = 17781939493175734315424531136 := by decide +kernel
private theorem rec_9_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 384 128 = 15953518991040714560437830336 := by decide +kernel
private theorem rec_9_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 512 128 = 14238982353011496038184043200 := by decide +kernel
private theorem rec_9_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 640 128 = 12634597930389085117646652096 := by decide +kernel
private theorem rec_9_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 768 128 = 11136641068958477607804584640 := by decide +kernel
private theorem rec_9_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 896 128 = 9741396838753345852920513216 := by decide +kernel
private theorem rec_9_16_2369_1_part8 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1024 128 = 8445162763820725827829154496 := by decide +kernel
private theorem rec_9_16_2369_1_part9 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1152 128 = 7244251551985704233225568960 := by decide +kernel
private theorem rec_9_16_2369_1_part10 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1280 128 = 6134993824616105590953460416 := by decide +kernel
private theorem rec_9_16_2369_1_part11 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1408 128 = 5113740846387179339293475520 := by decide +kernel
private theorem rec_9_16_2369_1_part12 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1536 128 = 4176867255046286928251503296 := by decide +kernel
private theorem rec_9_16_2369_1_part13 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1664 128 = 3320773791177588914846974656 := by decide +kernel
private theorem rec_9_16_2369_1_part14 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1792 128 = 2541890027966732058401161920 := by decide +kernel
private theorem rec_9_16_2369_1_part15 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1920 128 = 1836677100965536415825478336 := by decide +kernel
private theorem rec_9_16_2369_1_part16 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 2048 128 = 1201630437856682436909777600 := by decide +kernel
private theorem rec_9_16_2369_1_part17 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 2176 128 = 633282488218398059610653376 := by decide +kernel
private theorem rec_9_16_2369_1_part18 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 2304 99 = 140256637988944778529706170 := by decide +kernel
private theorem rec_9_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 0 256 = 41523357051225827954777982336 :=
  phaseBlock_append rec_9_16_2369_1_part0 rec_9_16_2369_1_part1 rfl rfl rfl
private theorem rec_9_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 256 256 = 33735458484216448875862361472 :=
  phaseBlock_append rec_9_16_2369_1_part2 rec_9_16_2369_1_part3 rfl rfl rfl
private theorem rec_9_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 0 512 = 75258815535442276830640343808 :=
  phaseBlock_append rec_9_16_2369_1_join0 rec_9_16_2369_1_join1 rfl rfl rfl
private theorem rec_9_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 512 256 = 26873580283400581155830695296 :=
  phaseBlock_append rec_9_16_2369_1_part4 rec_9_16_2369_1_part5 rfl rfl rfl
private theorem rec_9_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 896 256 = 18186559602574071680749667712 :=
  phaseBlock_append rec_9_16_2369_1_part7 rec_9_16_2369_1_part8 rfl rfl rfl
private theorem rec_9_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 768 384 = 29323200671532549288554252352 :=
  phaseBlock_append rec_9_16_2369_1_part6 rec_9_16_2369_1_join4 rfl rfl rfl
private theorem rec_9_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 512 640 = 56196780954933130444384947648 :=
  phaseBlock_append rec_9_16_2369_1_join3 rec_9_16_2369_1_join5 rfl rfl rfl
private theorem rec_9_16_2369_1_join7 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 0 1152 = 131455596490375407275025291456 :=
  phaseBlock_append rec_9_16_2369_1_join2 rec_9_16_2369_1_join6 rfl rfl rfl
private theorem rec_9_16_2369_1_join8 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1152 256 = 13379245376601809824179029376 :=
  phaseBlock_append rec_9_16_2369_1_part9 rec_9_16_2369_1_part10 rfl rfl rfl
private theorem rec_9_16_2369_1_join9 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1536 256 = 7497641046223875843098477952 :=
  phaseBlock_append rec_9_16_2369_1_part12 rec_9_16_2369_1_part13 rfl rfl rfl
private theorem rec_9_16_2369_1_join10 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1408 384 = 12611381892611055182391953472 :=
  phaseBlock_append rec_9_16_2369_1_part11 rec_9_16_2369_1_join9 rfl rfl rfl
private theorem rec_9_16_2369_1_join11 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1152 640 = 25990627269212865006570982848 :=
  phaseBlock_append rec_9_16_2369_1_join8 rec_9_16_2369_1_join10 rfl rfl rfl
private theorem rec_9_16_2369_1_join12 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1792 256 = 4378567128932268474226640256 :=
  phaseBlock_append rec_9_16_2369_1_part14 rec_9_16_2369_1_part15 rfl rfl rfl
private theorem rec_9_16_2369_1_join13 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 2176 227 = 773539126207342838140359546 :=
  phaseBlock_append rec_9_16_2369_1_part17 rec_9_16_2369_1_part18 rfl rfl rfl
private theorem rec_9_16_2369_1_join14 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 2048 355 = 1975169564064025275050137146 :=
  phaseBlock_append rec_9_16_2369_1_part16 rec_9_16_2369_1_join13 rfl rfl rfl
private theorem rec_9_16_2369_1_join15 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1792 611 = 6353736692996293749276777402 :=
  phaseBlock_append rec_9_16_2369_1_join12 rec_9_16_2369_1_join14 rfl rfl rfl
private theorem rec_9_16_2369_1_join16 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 1152 1251 = 32344363962209158755847760250 :=
  phaseBlock_append rec_9_16_2369_1_join11 rec_9_16_2369_1_join15 rfl rfl rfl
private theorem rec_9_16_2369_1_join17 :
    phaseBlock (fastLayerG (bank 9 16).shape 179798 2369 138 1 1 17 1) 0 2403 = 163799960452584566030873051706 :=
  phaseBlock_append rec_9_16_2369_1_join7 rec_9_16_2369_1_join16 rfl rfl rfl

private theorem rec_9_16_2369_1 : fastPhase (bank 9 16).shape 179798 2369 138 1 1 17 1 = 163799960452584566030873051706 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_9_16_2369_1_join17

theorem receipt_9_16 : Checked (bank 9 16) 138 1 17 := by
  refine checked_from_values (bank 9 16) 138 1 17
    (P3_7_1.checked (bank 9 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_10849_2402)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_16_2368_0 rec_9_16_2368_1 rec_9_16_2369_0 rec_9_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect9_checked (i : Fin 17) :
    Checked (bank 9 i) (reserve i) (excess 9) (seed 9) := by
  fin_cases i
  · exact receipt_9_0
  · exact receipt_9_1
  · exact receipt_9_2
  · exact receipt_9_3
  · exact receipt_9_4
  · exact receipt_9_5
  · exact receipt_9_6
  · exact receipt_9_7
  · exact receipt_9_8
  · exact receipt_9_9
  · exact receipt_9_10
  · exact receipt_9_11
  · exact receipt_9_12
  · exact receipt_9_13
  · exact receipt_9_14
  · exact receipt_9_15
  · exact receipt_9_16

end Lower6961.Lo.RescueSource
