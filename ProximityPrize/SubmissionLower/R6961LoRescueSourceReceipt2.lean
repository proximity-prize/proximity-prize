import ProximityPrize.SubmissionLower.R6961LoRescueSourceSchedule
import ProximityPrize.SubmissionLower.R6963LoFastLayerNat
import ProximityPrize.SubmissionLower.R6961LoRescuePoolMoments0
import ProximityPrize.SubmissionLower.R6961LoRescuePoolMoments1
import ProximityPrize.SubmissionLower.R6961LoRescuePoolMoments2

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


private theorem rec_2_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2368 1 1 0 7 0) 0 128 = 32152462903168223615254688 := by decide +kernel
private theorem rec_2_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2368 1 1 0 7 0) 128 128 = 16736854592698653389500207 := by decide +kernel
private theorem rec_2_1_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2368 1 1 0 7 0) 256 114 = 4335815544594301804364731 := by decide +kernel
private theorem rec_2_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2368 1 1 0 7 0) 128 242 = 21072670137292955193864938 :=
  phaseBlock_append rec_2_1_2368_0_part1 rec_2_1_2368_0_part2 rfl rfl rfl
private theorem rec_2_1_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2368 1 1 0 7 0) 0 370 = 53225133040461178809119626 :=
  phaseBlock_append rec_2_1_2368_0_part0 rec_2_1_2368_0_join0 rfl rfl rfl

private theorem rec_2_1_2368_0 : fastPhase (bank 2 1).shape 179798 2368 1 1 0 7 0 = 53225133040461178809119626 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_2_1_2368_0_join1

private theorem rec_2_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2368 1 1 0 7 1) 0 128 = 32021239311861370999939104 := by decide +kernel
private theorem rec_2_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2368 1 1 0 7 1) 128 128 = 16629407312035811861527130 := by decide +kernel
private theorem rec_2_1_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2368 1 1 0 7 1) 256 114 = 4257954183622628212088374 := by decide +kernel
private theorem rec_2_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2368 1 1 0 7 1) 128 242 = 20887361495658440073615504 :=
  phaseBlock_append rec_2_1_2368_1_part1 rec_2_1_2368_1_part2 rfl rfl rfl
private theorem rec_2_1_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2368 1 1 0 7 1) 0 370 = 52908600807519811073554608 :=
  phaseBlock_append rec_2_1_2368_1_part0 rec_2_1_2368_1_join0 rfl rfl rfl

private theorem rec_2_1_2368_1 : fastPhase (bank 2 1).shape 179798 2368 1 1 0 7 1 = 52908600807519811073554608 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_2_1_2368_1_join1

private theorem rec_2_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2369 1 1 0 7 0) 0 128 = 32152741264485959331194912 := by decide +kernel
private theorem rec_2_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2369 1 1 0 7 0) 128 128 = 16736966840754090072918254 := by decide +kernel
private theorem rec_2_1_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2369 1 1 0 7 0) 256 114 = 4335836197324064197504993 := by decide +kernel
private theorem rec_2_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2369 1 1 0 7 0) 128 242 = 21072803038078154270423247 :=
  phaseBlock_append rec_2_1_2369_0_part1 rec_2_1_2369_0_part2 rfl rfl rfl
private theorem rec_2_1_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2369 1 1 0 7 0) 0 370 = 53225544302564113601618159 :=
  phaseBlock_append rec_2_1_2369_0_part0 rec_2_1_2369_0_join0 rfl rfl rfl

private theorem rec_2_1_2369_0 : fastPhase (bank 2 1).shape 179798 2369 1 1 0 7 0 = 53225544302564113601618159 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_2_1_2369_0_join1

private theorem rec_2_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2369 1 1 0 7 1) 0 128 = 32021516734889254071070560 := by decide +kernel
private theorem rec_2_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2369 1 1 0 7 1) 128 128 = 16629518941315255844865058 := by decide +kernel
private theorem rec_2_1_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2369 1 1 0 7 1) 256 114 = 4257974511698974446622746 := by decide +kernel
private theorem rec_2_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2369 1 1 0 7 1) 128 242 = 20887493453014230291487804 :=
  phaseBlock_append rec_2_1_2369_1_part1 rec_2_1_2369_1_part2 rfl rfl rfl
private theorem rec_2_1_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 1).shape 179798 2369 1 1 0 7 1) 0 370 = 52909010187903484362558364 :=
  phaseBlock_append rec_2_1_2369_1_part0 rec_2_1_2369_1_join0 rfl rfl rfl

private theorem rec_2_1_2369_1 : fastPhase (bank 2 1).shape 179798 2369 1 1 0 7 1 = 52909010187903484362558364 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_2_1_2369_1_join1

theorem receipt_2_1 : Checked (bank 2 1) 1 0 7 := by
  refine checked_from_values (bank 2 1) 1 0 7
    (P3_7_1.checked (bank 2 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_1_2368_0 rec_2_1_2368_1 rec_2_1_2369_0 rec_2_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 0) 0 128 = 66892274671657330257979392 := by decide +kernel
private theorem rec_2_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 0) 128 128 = 42892866073762449679779840 := by decide +kernel
private theorem rec_2_2_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 0) 256 128 = 22528879917810147576557711 := by decide +kernel
private theorem rec_2_2_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 0) 384 109 = 5606587694967484385881809 := by decide +kernel
private theorem rec_2_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 0) 0 256 = 109785140745419779937759232 :=
  phaseBlock_append rec_2_2_2368_0_part0 rec_2_2_2368_0_part1 rfl rfl rfl
private theorem rec_2_2_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 0) 256 237 = 28135467612777631962439520 :=
  phaseBlock_append rec_2_2_2368_0_part2 rec_2_2_2368_0_part3 rfl rfl rfl
private theorem rec_2_2_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 0) 0 493 = 137920608358197411900198752 :=
  phaseBlock_append rec_2_2_2368_0_join0 rec_2_2_2368_0_join1 rfl rfl rfl

private theorem rec_2_2_2368_0 : fastPhase (bank 2 2).shape 179798 2368 2 1 0 7 0 = 137920608358197411900198752 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_2_2368_0_join2

private theorem rec_2_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 1) 0 128 = 66692262426678828830535104 := by decide +kernel
private theorem rec_2_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 1) 128 128 = 42721798425864844839923136 := by decide +kernel
private theorem rec_2_2_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 1) 256 128 = 22384086049362159737060611 := by decide +kernel
private theorem rec_2_2_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 1) 384 109 = 5502086851046969811247146 := by decide +kernel
private theorem rec_2_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 1) 0 256 = 109414060852543673670458240 :=
  phaseBlock_append rec_2_2_2368_1_part0 rec_2_2_2368_1_part1 rfl rfl rfl
private theorem rec_2_2_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 1) 256 237 = 27886172900409129548307757 :=
  phaseBlock_append rec_2_2_2368_1_part2 rec_2_2_2368_1_part3 rfl rfl rfl
private theorem rec_2_2_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2368 2 1 0 7 1) 0 493 = 137300233752952803218765997 :=
  phaseBlock_append rec_2_2_2368_1_join0 rec_2_2_2368_1_join1 rfl rfl rfl

private theorem rec_2_2_2368_1 : fastPhase (bank 2 2).shape 179798 2368 2 1 0 7 1 = 137300233752952803218765997 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_2_2368_1_join2

private theorem rec_2_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 0) 0 128 = 66892866239470277274441312 := by decide +kernel
private theorem rec_2_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 0) 128 128 = 42893183491484806286386784 := by decide +kernel
private theorem rec_2_2_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 0) 256 128 = 22529011467618728227760198 := by decide +kernel
private theorem rec_2_2_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 0) 384 109 = 5606612082939028884594210 := by decide +kernel
private theorem rec_2_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 0) 0 256 = 109786049730955083560828096 :=
  phaseBlock_append rec_2_2_2369_0_part0 rec_2_2_2369_0_part1 rfl rfl rfl
private theorem rec_2_2_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 0) 256 237 = 28135623550557757112354408 :=
  phaseBlock_append rec_2_2_2369_0_part2 rec_2_2_2369_0_part3 rfl rfl rfl
private theorem rec_2_2_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 0) 0 493 = 137921673281512840673182504 :=
  phaseBlock_append rec_2_2_2369_0_join0 rec_2_2_2369_0_join1 rfl rfl rfl

private theorem rec_2_2_2369_0 : fastPhase (bank 2 2).shape 179798 2369 2 1 0 7 0 = 137921673281512840673182504 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_2_2369_0_join2

private theorem rec_2_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 1) 0 128 = 66692852531589760072285728 := by decide +kernel
private theorem rec_2_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 1) 128 128 = 42722114765093662080257568 := by decide +kernel
private theorem rec_2_2_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 1) 256 128 = 22384216853357438422066032 := by decide +kernel
private theorem rec_2_2_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 1) 384 109 = 5502110829238837924761321 := by decide +kernel
private theorem rec_2_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 1) 0 256 = 109414967296683422152543296 :=
  phaseBlock_append rec_2_2_2369_1_part0 rec_2_2_2369_1_part1 rfl rfl rfl
private theorem rec_2_2_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 1) 256 237 = 27886327682596276346827353 :=
  phaseBlock_append rec_2_2_2369_1_part2 rec_2_2_2369_1_part3 rfl rfl rfl
private theorem rec_2_2_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 2).shape 179798 2369 2 1 0 7 1) 0 493 = 137301294979279698499370649 :=
  phaseBlock_append rec_2_2_2369_1_join0 rec_2_2_2369_1_join1 rfl rfl rfl

private theorem rec_2_2_2369_1 : fastPhase (bank 2 2).shape 179798 2369 2 1 0 7 1 = 137301294979279698499370649 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_2_2369_1_join2

theorem receipt_2_2 : Checked (bank 2 2) 2 0 7 := by
  refine checked_from_values (bank 2 2) 2 0 7
    (P3_7_1.checked (bank 2 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_2_2368_0 rec_2_2_2368_1 rec_2_2_2369_0 rec_2_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 0) 0 128 = 85080609036653365073485824 := by decide +kernel
private theorem rec_2_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 0) 128 128 = 54667167136831706805551104 := by decide +kernel
private theorem rec_2_3_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 0) 256 128 = 28771932388704384046819378 := by decide +kernel
private theorem rec_2_3_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 0) 384 109 = 7173237363582513493395711 := by decide +kernel
private theorem rec_2_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 0) 0 256 = 139747776173485071879036928 :=
  phaseBlock_append rec_2_3_2368_0_part0 rec_2_3_2368_0_part1 rfl rfl rfl
private theorem rec_2_3_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 0) 256 237 = 35945169752286897540215089 :=
  phaseBlock_append rec_2_3_2368_0_part2 rec_2_3_2368_0_part3 rfl rfl rfl
private theorem rec_2_3_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 0) 0 493 = 175692945925771969419252017 :=
  phaseBlock_append rec_2_3_2368_0_join0 rec_2_3_2368_0_join1 rfl rfl rfl

private theorem rec_2_3_2368_0 : fastPhase (bank 2 3).shape 179798 2368 3 1 0 7 0 = 175692945925771969419252017 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_3_2368_0_join2

private theorem rec_2_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 1) 0 128 = 84827558864356419567752640 := by decide +kernel
private theorem rec_2_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 1) 128 128 = 54450012824770823677089216 := by decide +kernel
private theorem rec_2_3_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 1) 256 128 = 28587465656838497692768025 := by decide +kernel
private theorem rec_2_3_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 1) 384 109 = 7039615578037514755223193 := by decide +kernel
private theorem rec_2_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 1) 0 256 = 139277571689127243244841856 :=
  phaseBlock_append rec_2_3_2368_1_part0 rec_2_3_2368_1_part1 rfl rfl rfl
private theorem rec_2_3_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 1) 256 237 = 35627081234876012447991218 :=
  phaseBlock_append rec_2_3_2368_1_part2 rec_2_3_2368_1_part3 rfl rfl rfl
private theorem rec_2_3_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2368 3 1 0 7 1) 0 493 = 174904652924003255692833074 :=
  phaseBlock_append rec_2_3_2368_1_join0 rec_2_3_2368_1_join1 rfl rfl rfl

private theorem rec_2_3_2368_1 : fastPhase (bank 2 3).shape 179798 2368 3 1 0 7 1 = 174904652924003255692833074 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_3_2368_1_join2

private theorem rec_2_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 0) 0 128 = 85081360122319661557435680 := by decide +kernel
private theorem rec_2_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 0) 128 128 = 54667570792862146336292128 := by decide +kernel
private theorem rec_2_3_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 0) 256 128 = 28772099894083871289958657 := by decide +kernel
private theorem rec_2_3_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 0) 384 109 = 7173268437971243618546535 := by decide +kernel
private theorem rec_2_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 0) 0 256 = 139748930915181807893727808 :=
  phaseBlock_append rec_2_3_2369_0_part0 rec_2_3_2369_0_part1 rfl rfl rfl
private theorem rec_2_3_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 0) 256 237 = 35945368332055114908505192 :=
  phaseBlock_append rec_2_3_2369_0_part2 rec_2_3_2369_0_part3 rfl rfl rfl
private theorem rec_2_3_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 0) 0 493 = 175694299247236922802233000 :=
  phaseBlock_append rec_2_3_2369_0_join0 rec_2_3_2369_0_join1 rfl rfl rfl

private theorem rec_2_3_2369_0 : fastPhase (bank 2 3).shape 179798 2369 3 1 0 7 0 = 175694299247236922802233000 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_3_2369_0_join2

private theorem rec_2_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 1) 0 128 = 84828308104883118305049056 := by decide +kernel
private theorem rec_2_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 1) 128 128 = 54450415116034468447463904 := by decide +kernel
private theorem rec_2_3_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 1) 256 128 = 28587632215438525818868718 := by decide +kernel
private theorem rec_2_3_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 1) 384 109 = 7039646130877697919589434 := by decide +kernel
private theorem rec_2_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 1) 0 256 = 139278723220917586752512960 :=
  phaseBlock_append rec_2_3_2369_1_part0 rec_2_3_2369_1_part1 rfl rfl rfl
private theorem rec_2_3_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 1) 256 237 = 35627278346316223738458152 :=
  phaseBlock_append rec_2_3_2369_1_part2 rec_2_3_2369_1_part3 rfl rfl rfl
private theorem rec_2_3_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 3).shape 179798 2369 3 1 0 7 1) 0 493 = 174906001567233810490971112 :=
  phaseBlock_append rec_2_3_2369_1_join0 rec_2_3_2369_1_join1 rfl rfl rfl

private theorem rec_2_3_2369_1 : fastPhase (bank 2 3).shape 179798 2369 3 1 0 7 1 = 174906001567233810490971112 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_3_2369_1_join2

theorem receipt_2_3 : Checked (bank 2 3) 3 0 7 := by
  refine checked_from_values (bank 2 3) 3 0 7
    (P3_7_1.checked (bank 2 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_3_2368_0 rec_2_3_2368_1 rec_2_3_2369_0 rec_2_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 0) 0 128 = 111845638967786135625551072 := by decide +kernel
private theorem rec_2_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 0) 128 128 = 72011391487502104255536352 := by decide +kernel
private theorem rec_2_4_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 0) 256 128 = 37977735910067337031702251 := by decide +kernel
private theorem rec_2_4_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 0) 384 109 = 9485464605225420002699943 := by decide +kernel
private theorem rec_2_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 0) 0 256 = 183857030455288239881087424 :=
  phaseBlock_append rec_2_4_2368_0_part0 rec_2_4_2368_0_part1 rfl rfl rfl
private theorem rec_2_4_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 0) 256 237 = 47463200515292757034402194 :=
  phaseBlock_append rec_2_4_2368_0_part2 rec_2_4_2368_0_part3 rfl rfl rfl
private theorem rec_2_4_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 0) 0 493 = 231320230970580996915489618 :=
  phaseBlock_append rec_2_4_2368_0_join0 rec_2_4_2368_0_join1 rfl rfl rfl

private theorem rec_2_4_2368_0 : fastPhase (bank 2 4).shape 179798 2368 4 1 0 7 0 = 231320230970580996915489618 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_4_2368_0_join2

private theorem rec_2_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 1) 0 128 = 111514753497268457741784288 := by decide +kernel
private theorem rec_2_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 1) 128 128 = 71726487630642324803241184 := by decide +kernel
private theorem rec_2_4_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 1) 256 128 = 37734841202902178536884716 := by decide +kernel
private theorem rec_2_4_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 1) 384 109 = 9308875901939954328767848 := by decide +kernel
private theorem rec_2_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 1) 0 256 = 183241241127910782545025472 :=
  phaseBlock_append rec_2_4_2368_1_part0 rec_2_4_2368_1_part1 rfl rfl rfl
private theorem rec_2_4_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 1) 256 237 = 47043717104842132865652564 :=
  phaseBlock_append rec_2_4_2368_1_part2 rec_2_4_2368_1_part3 rfl rfl rfl
private theorem rec_2_4_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2368 4 1 0 7 1) 0 493 = 230284958232752915410678036 :=
  phaseBlock_append rec_2_4_2368_1_join0 rec_2_4_2368_1_join1 rfl rfl rfl

private theorem rec_2_4_2368_1 : fastPhase (bank 2 4).shape 179798 2368 4 1 0 7 1 = 230284958232752915410678036 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_4_2368_1_join2

private theorem rec_2_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 0) 0 128 = 111846624581672663519653344 := by decide +kernel
private theorem rec_2_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 0) 128 128 = 72011922033028428890176992 := by decide +kernel
private theorem rec_2_4_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 0) 256 128 = 37977956350789971832453161 := by decide +kernel
private theorem rec_2_4_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 0) 384 109 = 9485505527495110626806175 := by decide +kernel
private theorem rec_2_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 0) 0 256 = 183858546614701092409830336 :=
  phaseBlock_append rec_2_4_2369_0_part0 rec_2_4_2369_0_part1 rfl rfl rfl
private theorem rec_2_4_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 0) 256 237 = 47463461878285082459259336 :=
  phaseBlock_append rec_2_4_2369_0_part2 rec_2_4_2369_0_part3 rfl rfl rfl
private theorem rec_2_4_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 0) 0 493 = 231322008492986174869089672 :=
  phaseBlock_append rec_2_4_2369_0_join0 rec_2_4_2369_0_join1 rfl rfl rfl

private theorem rec_2_4_2369_0 : fastPhase (bank 2 4).shape 179798 2369 4 1 0 7 0 = 231322008492986174869089672 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_4_2369_0_join2

private theorem rec_2_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 1) 0 128 = 111515736705931171680780000 := by decide +kernel
private theorem rec_2_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 1) 128 128 = 71727016391231475662769888 := by decide +kernel
private theorem rec_2_4_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 1) 256 128 = 37735060401426672235734770 := by decide +kernel
private theorem rec_2_4_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 1) 384 109 = 9308916138146660454214762 := by decide +kernel
private theorem rec_2_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 1) 0 256 = 183242753097162647343549888 :=
  phaseBlock_append rec_2_4_2369_1_part0 rec_2_4_2369_1_part1 rfl rfl rfl
private theorem rec_2_4_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 1) 256 237 = 47043976539573332689949532 :=
  phaseBlock_append rec_2_4_2369_1_part2 rec_2_4_2369_1_part3 rfl rfl rfl
private theorem rec_2_4_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 4).shape 179798 2369 4 1 0 7 1) 0 493 = 230286729636735980033499420 :=
  phaseBlock_append rec_2_4_2369_1_join0 rec_2_4_2369_1_join1 rfl rfl rfl

private theorem rec_2_4_2369_1 : fastPhase (bank 2 4).shape 179798 2369 4 1 0 7 1 = 230286729636735980033499420 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_4_2369_1_join2

theorem receipt_2_4 : Checked (bank 2 4) 4 0 7 := by
  refine checked_from_values (bank 2 4) 4 0 7
    (P3_7_1.checked (bank 2 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_4_2368_0 rec_2_4_2368_1 rec_2_4_2369_0 rec_2_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 0) 0 128 = 153566126674690629668639840 := by decide +kernel
private theorem rec_2_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 0) 128 128 = 99074749738927558735144032 := by decide +kernel
private theorem rec_2_5_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 0) 256 128 = 52356871612007930308011502 := by decide +kernel
private theorem rec_2_5_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 0) 384 109 = 13100346625236303712391115 := by decide +kernel
private theorem rec_2_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 0) 0 256 = 252640876413618188403783872 :=
  phaseBlock_append rec_2_5_2368_0_part0 rec_2_5_2368_0_part1 rfl rfl rfl
private theorem rec_2_5_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 0) 256 237 = 65457218237244234020402617 :=
  phaseBlock_append rec_2_5_2368_0_part2 rec_2_5_2368_0_part3 rfl rfl rfl
private theorem rec_2_5_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 0) 0 493 = 318098094650862422424186489 :=
  phaseBlock_append rec_2_5_2368_0_join0 rec_2_5_2368_0_join1 rfl rfl rfl

private theorem rec_2_5_2368_0 : fastPhase (bank 2 5).shape 179798 2368 5 1 0 7 0 = 318098094650862422424186489 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_5_2368_0_join2

private theorem rec_2_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 1) 0 128 = 153114245922000689738485088 := by decide +kernel
private theorem rec_2_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 1) 128 128 = 98684348131116152193580384 := by decide +kernel
private theorem rec_2_5_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 1) 256 128 = 52022827210857533258792772 := by decide +kernel
private theorem rec_2_5_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 1) 384 109 = 12856604444054687320490943 := by decide +kernel
private theorem rec_2_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 1) 0 256 = 251798594053116841932065472 :=
  phaseBlock_append rec_2_5_2368_1_part0 rec_2_5_2368_1_part1 rfl rfl rfl
private theorem rec_2_5_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 1) 256 237 = 64879431654912220579283715 :=
  phaseBlock_append rec_2_5_2368_1_part2 rec_2_5_2368_1_part3 rfl rfl rfl
private theorem rec_2_5_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2368 5 1 0 7 1) 0 493 = 316678025708029062511349187 :=
  phaseBlock_append rec_2_5_2368_1_join0 rec_2_5_2368_1_join1 rfl rfl rfl

private theorem rec_2_5_2368_1 : fastPhase (bank 2 5).shape 179798 2368 5 1 0 7 1 = 316678025708029062511349187 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_5_2368_1_join2

private theorem rec_2_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 0) 0 128 = 153567477535561904655530784 := by decide +kernel
private theorem rec_2_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 0) 128 128 = 99075478053188499262303008 := by decide +kernel
private theorem rec_2_5_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 0) 256 128 = 52357174606995516792534045 := by decide +kernel
private theorem rec_2_5_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 0) 384 109 = 13100402909855937177778614 := by decide +kernel
private theorem rec_2_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 0) 0 256 = 252642955588750403917833792 :=
  phaseBlock_append rec_2_5_2369_0_part0 rec_2_5_2369_0_part1 rfl rfl rfl
private theorem rec_2_5_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 0) 256 237 = 65457577516851453970312659 :=
  phaseBlock_append rec_2_5_2369_0_part2 rec_2_5_2369_0_part3 rfl rfl rfl
private theorem rec_2_5_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 0) 0 493 = 318100533105601857888146451 :=
  phaseBlock_append rec_2_5_2369_0_join0 rec_2_5_2369_0_join1 rfl rfl rfl

private theorem rec_2_5_2369_0 : fastPhase (bank 2 5).shape 179798 2369 5 1 0 7 0 = 318100533105601857888146451 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_5_2369_0_join2

private theorem rec_2_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 1) 0 128 = 153115593508349272063351968 := by decide +kernel
private theorem rec_2_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 1) 128 128 = 98685074007200951153724576 := by decide +kernel
private theorem rec_2_5_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 1) 256 128 = 52023128503633562079914241 := by decide +kernel
private theorem rec_2_5_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 1) 384 109 = 12856659786120622719428079 := by decide +kernel
private theorem rec_2_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 1) 0 256 = 251800667515550223217076544 :=
  phaseBlock_append rec_2_5_2369_1_part0 rec_2_5_2369_1_part1 rfl rfl rfl
private theorem rec_2_5_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 1) 256 237 = 64879788289754184799342320 :=
  phaseBlock_append rec_2_5_2369_1_part2 rec_2_5_2369_1_part3 rfl rfl rfl
private theorem rec_2_5_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 5).shape 179798 2369 5 1 0 7 1) 0 493 = 316680455805304408016418864 :=
  phaseBlock_append rec_2_5_2369_1_join0 rec_2_5_2369_1_join1 rfl rfl rfl

private theorem rec_2_5_2369_1 : fastPhase (bank 2 5).shape 179798 2369 5 1 0 7 1 = 316680455805304408016418864 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_2_5_2369_1_join2

theorem receipt_2_5 : Checked (bank 2 5) 5 0 7 := by
  refine checked_from_values (bank 2 5) 5 0 7
    (P3_7_1.checked (bank 2 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_5_2368_0 rec_2_5_2368_1 rec_2_5_2369_0 rec_2_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 0 128 = 373131803650384982539281568 := by decide +kernel
private theorem rec_2_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 128 128 = 276724097221489589932356768 := by decide +kernel
private theorem rec_2_6_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 256 128 = 190833867508571678341721430 := by decide +kernel
private theorem rec_2_6_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 384 128 = 114755642094680130396407222 := by decide +kernel
private theorem rec_2_6_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 512 128 = 47806505975567193190982749 := by decide +kernel
private theorem rec_2_6_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 640 38 = 2569327284762532080403425 := by decide +kernel
private theorem rec_2_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 128 256 = 467557964730061268274078198 :=
  phaseBlock_append rec_2_6_2368_0_part1 rec_2_6_2368_0_part2 rfl rfl rfl
private theorem rec_2_6_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 0 384 = 840689768380446250813359766 :=
  phaseBlock_append rec_2_6_2368_0_part0 rec_2_6_2368_0_join0 rfl rfl rfl
private theorem rec_2_6_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 512 166 = 50375833260329725271386174 :=
  phaseBlock_append rec_2_6_2368_0_part4 rec_2_6_2368_0_part5 rfl rfl rfl
private theorem rec_2_6_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 384 294 = 165131475355009855667793396 :=
  phaseBlock_append rec_2_6_2368_0_part3 rec_2_6_2368_0_join2 rfl rfl rfl
private theorem rec_2_6_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 0) 0 678 = 1005821243735456106481153162 :=
  phaseBlock_append rec_2_6_2368_0_join1 rec_2_6_2368_0_join3 rfl rfl rfl

private theorem rec_2_6_2368_0 : fastPhase (bank 2 6).shape 179798 2368 7 1 0 7 0 = 1005821243735456106481153162 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_6_2368_0_join4

private theorem rec_2_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 0 128 = 372346053621891272174154144 := by decide +kernel
private theorem rec_2_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 128 128 = 276020925451642534635815328 := by decide +kernel
private theorem rec_2_6_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 256 128 = 190207825622781547446086774 := by decide +kernel
private theorem rec_2_6_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 384 128 = 114201457616711098336318803 := by decide +kernel
private theorem rec_2_6_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 512 128 = 47319079276333300763939153 := by decide +kernel
private theorem rec_2_6_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 640 38 = 2436743058690939787505265 := by decide +kernel
private theorem rec_2_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 128 256 = 466228751074424082081902102 :=
  phaseBlock_append rec_2_6_2368_1_part1 rec_2_6_2368_1_part2 rfl rfl rfl
private theorem rec_2_6_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 0 384 = 838574804696315354256056246 :=
  phaseBlock_append rec_2_6_2368_1_part0 rec_2_6_2368_1_join0 rfl rfl rfl
private theorem rec_2_6_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 512 166 = 49755822335024240551444418 :=
  phaseBlock_append rec_2_6_2368_1_part4 rec_2_6_2368_1_part5 rfl rfl rfl
private theorem rec_2_6_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 384 294 = 163957279951735338887763221 :=
  phaseBlock_append rec_2_6_2368_1_part3 rec_2_6_2368_1_join2 rfl rfl rfl
private theorem rec_2_6_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2368 7 1 0 7 1) 0 678 = 1002532084648050693143819467 :=
  phaseBlock_append rec_2_6_2368_1_join1 rec_2_6_2368_1_join3 rfl rfl rfl

private theorem rec_2_6_2368_1 : fastPhase (bank 2 6).shape 179798 2368 7 1 0 7 1 = 1002532084648050693143819467 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_6_2368_1_join4

private theorem rec_2_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 0 128 = 373135150649716044200543232 := by decide +kernel
private theorem rec_2_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 128 128 = 276726293117352259768796160 := by decide +kernel
private theorem rec_2_6_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 256 128 = 190835172122452488306986142 := by decide +kernel
private theorem rec_2_6_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 384 128 = 114756291468333564845945382 := by decide +kernel
private theorem rec_2_6_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 512 128 = 47806718963916505520683764 := by decide +kernel
private theorem rec_2_6_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 640 38 = 2569336292120165610597624 := by decide +kernel
private theorem rec_2_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 128 256 = 467561465239804748075782302 :=
  phaseBlock_append rec_2_6_2369_0_part1 rec_2_6_2369_0_part2 rfl rfl rfl
private theorem rec_2_6_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 0 384 = 840696615889520792276325534 :=
  phaseBlock_append rec_2_6_2369_0_part0 rec_2_6_2369_0_join0 rfl rfl rfl
private theorem rec_2_6_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 512 166 = 50376055256036671131281388 :=
  phaseBlock_append rec_2_6_2369_0_part4 rec_2_6_2369_0_part5 rfl rfl rfl
private theorem rec_2_6_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 384 294 = 165132346724370235977226770 :=
  phaseBlock_append rec_2_6_2369_0_part3 rec_2_6_2369_0_join2 rfl rfl rfl
private theorem rec_2_6_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 0) 0 678 = 1005828962613891028253552304 :=
  phaseBlock_append rec_2_6_2369_0_join1 rec_2_6_2369_0_join3 rfl rfl rfl

private theorem rec_2_6_2369_0 : fastPhase (bank 2 6).shape 179798 2369 7 1 0 7 0 = 1005828962613891028253552304 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_6_2369_0_join4

private theorem rec_2_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 0 128 = 372349394810118851786051904 := by decide +kernel
private theorem rec_2_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 128 128 = 276023116648364552590274880 := by decide +kernel
private theorem rec_2_6_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 256 128 = 190209126539855312714609724 := by decide +kernel
private theorem rec_2_6_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 384 128 = 114202104199079929156838070 := by decide +kernel
private theorem rec_2_6_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 512 128 = 47319290277089112446591046 := by decide +kernel
private theorem rec_2_6_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 640 38 = 2436751615712846169644694 := by decide +kernel
private theorem rec_2_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 128 256 = 466232243188219865304884604 :=
  phaseBlock_append rec_2_6_2369_1_part1 rec_2_6_2369_1_part2 rfl rfl rfl
private theorem rec_2_6_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 0 384 = 838581637998338717090936508 :=
  phaseBlock_append rec_2_6_2369_1_part0 rec_2_6_2369_1_join0 rfl rfl rfl
private theorem rec_2_6_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 512 166 = 49756041892801958616235740 :=
  phaseBlock_append rec_2_6_2369_1_part4 rec_2_6_2369_1_part5 rfl rfl rfl
private theorem rec_2_6_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 384 294 = 163958146091881887773073810 :=
  phaseBlock_append rec_2_6_2369_1_part3 rec_2_6_2369_1_join2 rfl rfl rfl
private theorem rec_2_6_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 6).shape 179798 2369 7 1 0 7 1) 0 678 = 1002539784090220604864010318 :=
  phaseBlock_append rec_2_6_2369_1_join1 rec_2_6_2369_1_join3 rfl rfl rfl

private theorem rec_2_6_2369_1 : fastPhase (bank 2 6).shape 179798 2369 7 1 0 7 1 = 1002539784090220604864010318 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_6_2369_1_join4

theorem receipt_2_6 : Checked (bank 2 6) 7 0 7 := by
  refine checked_from_values (bank 2 6) 7 0 7
    (P3_7_1.checked (bank 2 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_6_2368_0 rec_2_6_2368_1 rec_2_6_2369_0 rec_2_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 0 128 = 675345919141939667082939168 := by decide +kernel
private theorem rec_2_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 128 128 = 502481779166044926432516896 := by decide +kernel
private theorem rec_2_7_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 256 128 = 347655442673464466510124308 := by decide +kernel
private theorem rec_2_7_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 384 128 = 209744746788916857261763520 := by decide +kernel
private theorem rec_2_7_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 512 128 = 87656324814555000178831866 := by decide +kernel
private theorem rec_2_7_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 640 38 = 4722391322956050782898772 := by decide +kernel
private theorem rec_2_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 128 256 = 850137221839509392942641204 :=
  phaseBlock_append rec_2_7_2368_0_part1 rec_2_7_2368_0_part2 rfl rfl rfl
private theorem rec_2_7_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 0 384 = 1525483140981449060025580372 :=
  phaseBlock_append rec_2_7_2368_0_part0 rec_2_7_2368_0_join0 rfl rfl rfl
private theorem rec_2_7_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 512 166 = 92378716137511050961730638 :=
  phaseBlock_append rec_2_7_2368_0_part4 rec_2_7_2368_0_part5 rfl rfl rfl
private theorem rec_2_7_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 384 294 = 302123462926427908223494158 :=
  phaseBlock_append rec_2_7_2368_0_part3 rec_2_7_2368_0_join2 rfl rfl rfl
private theorem rec_2_7_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 0) 0 678 = 1827606603907876968249074530 :=
  phaseBlock_append rec_2_7_2368_0_join1 rec_2_7_2368_0_join3 rfl rfl rfl

private theorem rec_2_7_2368_0 : fastPhase (bank 2 7).shape 179798 2368 10 1 0 7 0 = 1827606603907876968249074530 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_7_2368_0_join4

private theorem rec_2_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 0 128 = 673940769991131662110582176 := by decide +kernel
private theorem rec_2_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 128 128 = 501217707244818880822015392 := by decide +kernel
private theorem rec_2_7_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 256 128 = 346523816242140785445524852 := by decide +kernel
private theorem rec_2_7_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 384 128 = 208737160144865830545354634 := by decide +kernel
private theorem rec_2_7_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 512 128 = 86764594797891609915866085 := by decide +kernel
private theorem rec_2_7_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 640 38 = 4478783070709879941586629 := by decide +kernel
private theorem rec_2_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 128 256 = 847741523486959666267540244 :=
  phaseBlock_append rec_2_7_2368_1_part1 rec_2_7_2368_1_part2 rfl rfl rfl
private theorem rec_2_7_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 0 384 = 1521682293478091328378122420 :=
  phaseBlock_append rec_2_7_2368_1_part0 rec_2_7_2368_1_join0 rfl rfl rfl
private theorem rec_2_7_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 512 166 = 91243377868601489857452714 :=
  phaseBlock_append rec_2_7_2368_1_part4 rec_2_7_2368_1_part5 rfl rfl rfl
private theorem rec_2_7_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 384 294 = 299980538013467320402807348 :=
  phaseBlock_append rec_2_7_2368_1_part3 rec_2_7_2368_1_join2 rfl rfl rfl
private theorem rec_2_7_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2368 10 1 0 7 1) 0 678 = 1821662831491558648780929768 :=
  phaseBlock_append rec_2_7_2368_1_join1 rec_2_7_2368_1_join3 rfl rfl rfl

private theorem rec_2_7_2368_1 : fastPhase (bank 2 7).shape 179798 2368 10 1 0 7 1 = 1821662831491558648780929768 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_7_2368_1_join4

private theorem rec_2_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 0 128 = 675351954203091958440737088 := by decide +kernel
private theorem rec_2_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 128 128 = 502485749010644613565307200 := by decide +kernel
private theorem rec_2_7_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 256 128 = 347657806804412318650346553 := by decide +kernel
private theorem rec_2_7_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 384 128 = 209745925778955530584649506 := by decide +kernel
private theorem rec_2_7_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 512 128 = 87656711938940003193246200 := by decide +kernel
private theorem rec_2_7_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 640 38 = 4722407693088599777316224 := by decide +kernel
private theorem rec_2_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 128 256 = 850143555815056932215653753 :=
  phaseBlock_append rec_2_7_2369_0_part1 rec_2_7_2369_0_part2 rfl rfl rfl
private theorem rec_2_7_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 0 384 = 1525495510018148890656390841 :=
  phaseBlock_append rec_2_7_2369_0_part0 rec_2_7_2369_0_join0 rfl rfl rfl
private theorem rec_2_7_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 512 166 = 92379119632028602970562424 :=
  phaseBlock_append rec_2_7_2369_0_part4 rec_2_7_2369_0_part5 rfl rfl rfl
private theorem rec_2_7_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 384 294 = 302125045410984133555211930 :=
  phaseBlock_append rec_2_7_2369_0_part3 rec_2_7_2369_0_join2 rfl rfl rfl
private theorem rec_2_7_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 0) 0 678 = 1827620555429133024211602771 :=
  phaseBlock_append rec_2_7_2369_0_join1 rec_2_7_2369_0_join3 rfl rfl rfl

private theorem rec_2_7_2369_0 : fastPhase (bank 2 7).shape 179798 2369 10 1 0 7 0 = 1827620555429133024211602771 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_7_2369_0_join4

private theorem rec_2_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 0 128 = 673946794730349594362124480 := by decide +kernel
private theorem rec_2_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 128 128 = 501221668698648166144800960 := by decide +kernel
private theorem rec_2_7_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 256 128 = 346526173737600785563414617 := by decide +kernel
private theorem rec_2_7_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 384 128 = 208738334099708678030322519 := by decide +kernel
private theorem rec_2_7_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 512 128 = 86764978320911608398761238 := by decide +kernel
private theorem rec_2_7_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 640 38 = 4478798622936938564266737 := by decide +kernel
private theorem rec_2_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 128 256 = 847747842436248951708215577 :=
  phaseBlock_append rec_2_7_2369_1_part1 rec_2_7_2369_1_part2 rfl rfl rfl
private theorem rec_2_7_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 0 384 = 1521694637166598546070340057 :=
  phaseBlock_append rec_2_7_2369_1_part0 rec_2_7_2369_1_join0 rfl rfl rfl
private theorem rec_2_7_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 512 166 = 91243776943848546963027975 :=
  phaseBlock_append rec_2_7_2369_1_part4 rec_2_7_2369_1_part5 rfl rfl rfl
private theorem rec_2_7_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 384 294 = 299982111043557224993350494 :=
  phaseBlock_append rec_2_7_2369_1_part3 rec_2_7_2369_1_join2 rfl rfl rfl
private theorem rec_2_7_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 7).shape 179798 2369 10 1 0 7 1) 0 678 = 1821676748210155771063690551 :=
  phaseBlock_append rec_2_7_2369_1_join1 rec_2_7_2369_1_join3 rfl rfl rfl

private theorem rec_2_7_2369_1 : fastPhase (bank 2 7).shape 179798 2369 10 1 0 7 1 = 1821676748210155771063690551 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_7_2369_1_join4

theorem receipt_2_7 : Checked (bank 2 7) 10 0 7 := by
  refine checked_from_values (bank 2 7) 10 0 7
    (P3_7_1.checked (bank 2 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_7_2368_0 rec_2_7_2368_1 rec_2_7_2369_0 rec_2_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 0 128 = 2711529216665882267926250336 := by decide +kernel
private theorem rec_2_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 128 128 = 2204535988700400619700147040 := by decide +kernel
private theorem rec_2_8_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 256 128 = 1736749254570519596560802656 := by decide +kernel
private theorem rec_2_8_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 384 128 = 1306355738840765475299366916 := by decide +kernel
private theorem rec_2_8_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 512 128 = 911581033125980938615746642 := by decide +kernel
private theorem rec_2_8_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 640 128 = 550686280034303469117834773 := by decide +kernel
private theorem rec_2_8_2368_0_part6 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 768 128 = 221966418277367960140181356 := by decide +kernel
private theorem rec_2_8_2368_0_part7 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 896 29 = 7793537339018346532264410 := by decide +kernel
private theorem rec_2_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 0 256 = 4916065205366282887626397376 :=
  phaseBlock_append rec_2_8_2368_0_part0 rec_2_8_2368_0_part1 rfl rfl rfl
private theorem rec_2_8_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 256 256 = 3043104993411285071860169572 :=
  phaseBlock_append rec_2_8_2368_0_part2 rec_2_8_2368_0_part3 rfl rfl rfl
private theorem rec_2_8_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 0 512 = 7959170198777567959486566948 :=
  phaseBlock_append rec_2_8_2368_0_join0 rec_2_8_2368_0_join1 rfl rfl rfl
private theorem rec_2_8_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 512 256 = 1462267313160284407733581415 :=
  phaseBlock_append rec_2_8_2368_0_part4 rec_2_8_2368_0_part5 rfl rfl rfl
private theorem rec_2_8_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 768 157 = 229759955616386306672445766 :=
  phaseBlock_append rec_2_8_2368_0_part6 rec_2_8_2368_0_part7 rfl rfl rfl
private theorem rec_2_8_2368_0_join5 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 512 413 = 1692027268776670714406027181 :=
  phaseBlock_append rec_2_8_2368_0_join3 rec_2_8_2368_0_join4 rfl rfl rfl
private theorem rec_2_8_2368_0_join6 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 0) 0 925 = 9651197467554238673892594129 :=
  phaseBlock_append rec_2_8_2368_0_join2 rec_2_8_2368_0_join5 rfl rfl rfl

private theorem rec_2_8_2368_0 : fastPhase (bank 2 8).shape 179798 2368 16 1 0 7 0 = 9651197467554238673892594129 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_2_8_2368_0_join6

private theorem rec_2_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 0 128 = 2707465104252562467667572320 := by decide +kernel
private theorem rec_2_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 128 128 = 2200776221298965307663279712 := by decide +kernel
private theorem rec_2_8_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 256 128 = 1733279925082158987850471008 := by decide +kernel
private theorem rec_2_8_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 384 128 = 1303163227912680071169717471 := by decide +kernel
private theorem rec_2_8_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 512 128 = 908652002694438094557859415 := by decide +kernel
private theorem rec_2_8_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 640 128 = 548007670027631683207878750 := by decide +kernel
private theorem rec_2_8_2368_1_part6 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 768 128 = 219525449510299802521747816 := by decide +kernel
private theorem rec_2_8_2368_1_part7 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 896 29 = 7272230160273671249573427 := by decide +kernel
private theorem rec_2_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 0 256 = 4908241325551527775330852032 :=
  phaseBlock_append rec_2_8_2368_1_part0 rec_2_8_2368_1_part1 rfl rfl rfl
private theorem rec_2_8_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 256 256 = 3036443152994839059020188479 :=
  phaseBlock_append rec_2_8_2368_1_part2 rec_2_8_2368_1_part3 rfl rfl rfl
private theorem rec_2_8_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 0 512 = 7944684478546366834351040511 :=
  phaseBlock_append rec_2_8_2368_1_join0 rec_2_8_2368_1_join1 rfl rfl rfl
private theorem rec_2_8_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 512 256 = 1456659672722069777765738165 :=
  phaseBlock_append rec_2_8_2368_1_part4 rec_2_8_2368_1_part5 rfl rfl rfl
private theorem rec_2_8_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 768 157 = 226797679670573473771321243 :=
  phaseBlock_append rec_2_8_2368_1_part6 rec_2_8_2368_1_part7 rfl rfl rfl
private theorem rec_2_8_2368_1_join5 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 512 413 = 1683457352392643251537059408 :=
  phaseBlock_append rec_2_8_2368_1_join3 rec_2_8_2368_1_join4 rfl rfl rfl
private theorem rec_2_8_2368_1_join6 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2368 16 1 0 7 1) 0 925 = 9628141830939010085888099919 :=
  phaseBlock_append rec_2_8_2368_1_join2 rec_2_8_2368_1_join5 rfl rfl rfl

private theorem rec_2_8_2368_1 : fastPhase (bank 2 8).shape 179798 2368 16 1 0 7 1 = 9628141830939010085888099919 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_2_8_2368_1_join6

private theorem rec_2_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 0 128 = 2711553738145444137660478176 := by decide +kernel
private theorem rec_2_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 128 128 = 2204554272180810806304703200 := by decide +kernel
private theorem rec_2_8_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 256 128 = 1736762296283118911869522656 := by decide +kernel
private theorem rec_2_8_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 384 128 = 1306364475468578516685436959 := by decide +kernel
private theorem rec_2_8_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 512 128 = 911586335579594944596621651 := by decide +kernel
private theorem rec_2_8_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 640 128 = 550688984527806621285261270 := by decide +kernel
private theorem rec_2_8_2369_0_part6 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 768 128 = 221967308826948759933598425 := by decide +kernel
private theorem rec_2_8_2369_0_part7 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 896 29 = 7793563220883518161599621 := by decide +kernel
private theorem rec_2_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 0 256 = 4916108010326254943965181376 :=
  phaseBlock_append rec_2_8_2369_0_part0 rec_2_8_2369_0_part1 rfl rfl rfl
private theorem rec_2_8_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 256 256 = 3043126771751697428554959615 :=
  phaseBlock_append rec_2_8_2369_0_part2 rec_2_8_2369_0_part3 rfl rfl rfl
private theorem rec_2_8_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 0 512 = 7959234782077952372520140991 :=
  phaseBlock_append rec_2_8_2369_0_join0 rec_2_8_2369_0_join1 rfl rfl rfl
private theorem rec_2_8_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 512 256 = 1462275320107401565881882921 :=
  phaseBlock_append rec_2_8_2369_0_part4 rec_2_8_2369_0_part5 rfl rfl rfl
private theorem rec_2_8_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 768 157 = 229760872047832278095198046 :=
  phaseBlock_append rec_2_8_2369_0_part6 rec_2_8_2369_0_part7 rfl rfl rfl
private theorem rec_2_8_2369_0_join5 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 512 413 = 1692036192155233843977080967 :=
  phaseBlock_append rec_2_8_2369_0_join3 rec_2_8_2369_0_join4 rfl rfl rfl
private theorem rec_2_8_2369_0_join6 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 0) 0 925 = 9651270974233186216497221958 :=
  phaseBlock_append rec_2_8_2369_0_join2 rec_2_8_2369_0_join5 rfl rfl rfl

private theorem rec_2_8_2369_0 : fastPhase (bank 2 8).shape 179798 2369 16 1 0 7 0 = 9651270974233186216497221958 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_2_8_2369_0_join6

private theorem rec_2_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 0 128 = 2707489595564008692960068448 := by decide +kernel
private theorem rec_2_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 128 128 = 2200794478786589681934521184 := by decide +kernel
private theorem rec_2_8_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 256 128 = 1733292944692536469452596064 := by decide +kernel
private theorem rec_2_8_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 384 128 = 1303171946055437342080142205 := by decide +kernel
private theorem rec_2_8_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 512 128 = 908657290045169025514675620 := by decide +kernel
private theorem rec_2_8_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 640 128 = 548010362537170655764790715 := by decide +kernel
private theorem rec_2_8_2369_1_part6 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 768 128 = 219526330928235699146807364 := by decide +kernel
private theorem rec_2_8_2369_1_part7 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 896 29 = 7272254342652915001206723 := by decide +kernel
private theorem rec_2_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 0 256 = 4908284074350598374894589632 :=
  phaseBlock_append rec_2_8_2369_1_part0 rec_2_8_2369_1_part1 rfl rfl rfl
private theorem rec_2_8_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 256 256 = 3036464890747973811532738269 :=
  phaseBlock_append rec_2_8_2369_1_part2 rec_2_8_2369_1_part3 rfl rfl rfl
private theorem rec_2_8_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 0 512 = 7944748965098572186427327901 :=
  phaseBlock_append rec_2_8_2369_1_join0 rec_2_8_2369_1_join1 rfl rfl rfl
private theorem rec_2_8_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 512 256 = 1456667652582339681279466335 :=
  phaseBlock_append rec_2_8_2369_1_part4 rec_2_8_2369_1_part5 rfl rfl rfl
private theorem rec_2_8_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 768 157 = 226798585270888614148014087 :=
  phaseBlock_append rec_2_8_2369_1_part6 rec_2_8_2369_1_part7 rfl rfl rfl
private theorem rec_2_8_2369_1_join5 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 512 413 = 1683466237853228295427480422 :=
  phaseBlock_append rec_2_8_2369_1_join3 rec_2_8_2369_1_join4 rfl rfl rfl
private theorem rec_2_8_2369_1_join6 :
    phaseBlock (fastLayerG (bank 2 8).shape 179798 2369 16 1 0 7 1) 0 925 = 9628215202951800481854808323 :=
  phaseBlock_append rec_2_8_2369_1_join2 rec_2_8_2369_1_join5 rfl rfl rfl

private theorem rec_2_8_2369_1 : fastPhase (bank 2 8).shape 179798 2369 16 1 0 7 1 = 9628215202951800481854808323 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_2_8_2369_1_join6

theorem receipt_2_8 : Checked (bank 2 8) 16 0 7 := by
  refine checked_from_values (bank 2 8) 16 0 7
    (P3_7_1.checked (bank 2 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_8_2368_0 rec_2_8_2368_1 rec_2_8_2369_0 rec_2_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 0 128 = 675345919141939667082939168 := by decide +kernel
private theorem rec_2_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 128 128 = 502481779166044926432516896 := by decide +kernel
private theorem rec_2_9_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 256 128 = 347655442673464466510124308 := by decide +kernel
private theorem rec_2_9_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 384 128 = 209744746788916857261763520 := by decide +kernel
private theorem rec_2_9_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 512 128 = 87656324814555000178831866 := by decide +kernel
private theorem rec_2_9_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 640 38 = 4722391322956050782898772 := by decide +kernel
private theorem rec_2_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 128 256 = 850137221839509392942641204 :=
  phaseBlock_append rec_2_9_2368_0_part1 rec_2_9_2368_0_part2 rfl rfl rfl
private theorem rec_2_9_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 0 384 = 1525483140981449060025580372 :=
  phaseBlock_append rec_2_9_2368_0_part0 rec_2_9_2368_0_join0 rfl rfl rfl
private theorem rec_2_9_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 512 166 = 92378716137511050961730638 :=
  phaseBlock_append rec_2_9_2368_0_part4 rec_2_9_2368_0_part5 rfl rfl rfl
private theorem rec_2_9_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 384 294 = 302123462926427908223494158 :=
  phaseBlock_append rec_2_9_2368_0_part3 rec_2_9_2368_0_join2 rfl rfl rfl
private theorem rec_2_9_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 0) 0 678 = 1827606603907876968249074530 :=
  phaseBlock_append rec_2_9_2368_0_join1 rec_2_9_2368_0_join3 rfl rfl rfl

private theorem rec_2_9_2368_0 : fastPhase (bank 2 9).shape 179798 2368 10 1 0 7 0 = 1827606603907876968249074530 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_9_2368_0_join4

private theorem rec_2_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 0 128 = 673940769991131662110582176 := by decide +kernel
private theorem rec_2_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 128 128 = 501217707244818880822015392 := by decide +kernel
private theorem rec_2_9_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 256 128 = 346523816242140785445524852 := by decide +kernel
private theorem rec_2_9_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 384 128 = 208737160144865830545354634 := by decide +kernel
private theorem rec_2_9_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 512 128 = 86764594797891609915866085 := by decide +kernel
private theorem rec_2_9_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 640 38 = 4478783070709879941586629 := by decide +kernel
private theorem rec_2_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 128 256 = 847741523486959666267540244 :=
  phaseBlock_append rec_2_9_2368_1_part1 rec_2_9_2368_1_part2 rfl rfl rfl
private theorem rec_2_9_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 0 384 = 1521682293478091328378122420 :=
  phaseBlock_append rec_2_9_2368_1_part0 rec_2_9_2368_1_join0 rfl rfl rfl
private theorem rec_2_9_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 512 166 = 91243377868601489857452714 :=
  phaseBlock_append rec_2_9_2368_1_part4 rec_2_9_2368_1_part5 rfl rfl rfl
private theorem rec_2_9_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 384 294 = 299980538013467320402807348 :=
  phaseBlock_append rec_2_9_2368_1_part3 rec_2_9_2368_1_join2 rfl rfl rfl
private theorem rec_2_9_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2368 10 1 0 7 1) 0 678 = 1821662831491558648780929768 :=
  phaseBlock_append rec_2_9_2368_1_join1 rec_2_9_2368_1_join3 rfl rfl rfl

private theorem rec_2_9_2368_1 : fastPhase (bank 2 9).shape 179798 2368 10 1 0 7 1 = 1821662831491558648780929768 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_9_2368_1_join4

private theorem rec_2_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 0 128 = 675351954203091958440737088 := by decide +kernel
private theorem rec_2_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 128 128 = 502485749010644613565307200 := by decide +kernel
private theorem rec_2_9_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 256 128 = 347657806804412318650346553 := by decide +kernel
private theorem rec_2_9_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 384 128 = 209745925778955530584649506 := by decide +kernel
private theorem rec_2_9_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 512 128 = 87656711938940003193246200 := by decide +kernel
private theorem rec_2_9_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 640 38 = 4722407693088599777316224 := by decide +kernel
private theorem rec_2_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 128 256 = 850143555815056932215653753 :=
  phaseBlock_append rec_2_9_2369_0_part1 rec_2_9_2369_0_part2 rfl rfl rfl
private theorem rec_2_9_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 0 384 = 1525495510018148890656390841 :=
  phaseBlock_append rec_2_9_2369_0_part0 rec_2_9_2369_0_join0 rfl rfl rfl
private theorem rec_2_9_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 512 166 = 92379119632028602970562424 :=
  phaseBlock_append rec_2_9_2369_0_part4 rec_2_9_2369_0_part5 rfl rfl rfl
private theorem rec_2_9_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 384 294 = 302125045410984133555211930 :=
  phaseBlock_append rec_2_9_2369_0_part3 rec_2_9_2369_0_join2 rfl rfl rfl
private theorem rec_2_9_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 0) 0 678 = 1827620555429133024211602771 :=
  phaseBlock_append rec_2_9_2369_0_join1 rec_2_9_2369_0_join3 rfl rfl rfl

private theorem rec_2_9_2369_0 : fastPhase (bank 2 9).shape 179798 2369 10 1 0 7 0 = 1827620555429133024211602771 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_9_2369_0_join4

private theorem rec_2_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 0 128 = 673946794730349594362124480 := by decide +kernel
private theorem rec_2_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 128 128 = 501221668698648166144800960 := by decide +kernel
private theorem rec_2_9_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 256 128 = 346526173737600785563414617 := by decide +kernel
private theorem rec_2_9_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 384 128 = 208738334099708678030322519 := by decide +kernel
private theorem rec_2_9_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 512 128 = 86764978320911608398761238 := by decide +kernel
private theorem rec_2_9_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 640 38 = 4478798622936938564266737 := by decide +kernel
private theorem rec_2_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 128 256 = 847747842436248951708215577 :=
  phaseBlock_append rec_2_9_2369_1_part1 rec_2_9_2369_1_part2 rfl rfl rfl
private theorem rec_2_9_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 0 384 = 1521694637166598546070340057 :=
  phaseBlock_append rec_2_9_2369_1_part0 rec_2_9_2369_1_join0 rfl rfl rfl
private theorem rec_2_9_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 512 166 = 91243776943848546963027975 :=
  phaseBlock_append rec_2_9_2369_1_part4 rec_2_9_2369_1_part5 rfl rfl rfl
private theorem rec_2_9_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 384 294 = 299982111043557224993350494 :=
  phaseBlock_append rec_2_9_2369_1_part3 rec_2_9_2369_1_join2 rfl rfl rfl
private theorem rec_2_9_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 9).shape 179798 2369 10 1 0 7 1) 0 678 = 1821676748210155771063690551 :=
  phaseBlock_append rec_2_9_2369_1_join1 rec_2_9_2369_1_join3 rfl rfl rfl

private theorem rec_2_9_2369_1 : fastPhase (bank 2 9).shape 179798 2369 10 1 0 7 1 = 1821676748210155771063690551 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_2_9_2369_1_join4

theorem receipt_2_9 : Checked (bank 2 9) 10 0 7 := by
  refine checked_from_values (bank 2 9) 10 0 7
    (P3_7_1.checked (bank 2 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_9_2368_0 rec_2_9_2368_1 rec_2_9_2369_0 rec_2_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 0 128 = 5638154851268897123091422016 := by decide +kernel
private theorem rec_2_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 128 128 = 4594635116948736141299391296 := by decide +kernel
private theorem rec_2_10_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 256 128 = 3628170212964107212637215552 := by decide +kernel
private theorem rec_2_10_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 384 128 = 2735480082948099586450025252 := by decide +kernel
private theorem rec_2_10_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 512 128 = 1913339390885790092156008065 := by decide +kernel
private theorem rec_2_10_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 640 128 = 1158570422107273892918929213 := by decide +kernel
private theorem rec_2_10_2368_0_part6 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 768 128 = 468040278676990285274346399 := by decide +kernel
private theorem rec_2_10_2368_0_part7 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 896 29 = 16461162830839093825700732 := by decide +kernel
private theorem rec_2_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 0 256 = 10232789968217633264390813312 :=
  phaseBlock_append rec_2_10_2368_0_part0 rec_2_10_2368_0_part1 rfl rfl rfl
private theorem rec_2_10_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 256 256 = 6363650295912206799087240804 :=
  phaseBlock_append rec_2_10_2368_0_part2 rec_2_10_2368_0_part3 rfl rfl rfl
private theorem rec_2_10_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 0 512 = 16596440264129840063478054116 :=
  phaseBlock_append rec_2_10_2368_0_join0 rec_2_10_2368_0_join1 rfl rfl rfl
private theorem rec_2_10_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 512 256 = 3071909812993063985074937278 :=
  phaseBlock_append rec_2_10_2368_0_part4 rec_2_10_2368_0_part5 rfl rfl rfl
private theorem rec_2_10_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 768 157 = 484501441507829379100047131 :=
  phaseBlock_append rec_2_10_2368_0_part6 rec_2_10_2368_0_part7 rfl rfl rfl
private theorem rec_2_10_2368_0_join5 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 512 413 = 3556411254500893364174984409 :=
  phaseBlock_append rec_2_10_2368_0_join3 rec_2_10_2368_0_join4 rfl rfl rfl
private theorem rec_2_10_2368_0_join6 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 0) 0 925 = 20152851518630733427653038525 :=
  phaseBlock_append rec_2_10_2368_0_join2 rec_2_10_2368_0_join5 rfl rfl rfl

private theorem rec_2_10_2368_0 : fastPhase (bank 2 10).shape 179798 2368 20 1 0 7 0 = 20152851518630733427653038525 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_2_10_2368_0_join6

private theorem rec_2_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 0 128 = 5629806351010280506625019776 := by decide +kernel
private theorem rec_2_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 128 128 = 4586882785924798945266839424 := by decide +kernel
private theorem rec_2_10_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 256 128 = 3620988984105027518563061632 := by decide +kernel
private theorem rec_2_10_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 384 128 = 2728845286031433043771344718 := by decide +kernel
private theorem rec_2_10_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 512 128 = 1907226741250374654156629668 := by decide +kernel
private theorem rec_2_10_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 640 128 = 1152956016987284532890314128 := by decide +kernel
private theorem rec_2_10_2368_1_part6 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 768 128 = 462900605413264907563802477 := by decide +kernel
private theorem rec_2_10_2368_1_part7 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 896 29 = 15360275558170591868747004 := by decide +kernel
private theorem rec_2_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 0 256 = 10216689136935079451891859200 :=
  phaseBlock_append rec_2_10_2368_1_part0 rec_2_10_2368_1_part1 rfl rfl rfl
private theorem rec_2_10_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 256 256 = 6349834270136460562334406350 :=
  phaseBlock_append rec_2_10_2368_1_part2 rec_2_10_2368_1_part3 rfl rfl rfl
private theorem rec_2_10_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 0 512 = 16566523407071540014226265550 :=
  phaseBlock_append rec_2_10_2368_1_join0 rec_2_10_2368_1_join1 rfl rfl rfl
private theorem rec_2_10_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 512 256 = 3060182758237659187046943796 :=
  phaseBlock_append rec_2_10_2368_1_part4 rec_2_10_2368_1_part5 rfl rfl rfl
private theorem rec_2_10_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 768 157 = 478260880971435499432549481 :=
  phaseBlock_append rec_2_10_2368_1_part6 rec_2_10_2368_1_part7 rfl rfl rfl
private theorem rec_2_10_2368_1_join5 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 512 413 = 3538443639209094686479493277 :=
  phaseBlock_append rec_2_10_2368_1_join3 rec_2_10_2368_1_join4 rfl rfl rfl
private theorem rec_2_10_2368_1_join6 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2368 20 1 0 7 1) 0 925 = 20104967046280634700705758827 :=
  phaseBlock_append rec_2_10_2368_1_join2 rec_2_10_2368_1_join5 rfl rfl rfl

private theorem rec_2_10_2368_1 : fastPhase (bank 2 10).shape 179798 2368 20 1 0 7 1 = 20104967046280634700705758827 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_2_10_2368_1_join6

private theorem rec_2_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 0 128 = 5638205654596836725732082912 := by decide +kernel
private theorem rec_2_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 128 128 = 4594673068760024383337288928 := by decide +kernel
private theorem rec_2_10_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 256 128 = 3628197333275953047197295840 := by decide +kernel
private theorem rec_2_10_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 384 128 = 2735498280444992393063399615 := by decide +kernel
private theorem rec_2_10_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 512 128 = 1913350450338033599260959997 := by decide +kernel
private theorem rec_2_10_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 640 128 = 1158576068819449300696088121 := by decide +kernel
private theorem rec_2_10_2369_0_part6 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 768 128 = 468042138623499094480244787 := by decide +kernel
private theorem rec_2_10_2369_0_part7 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 896 29 = 16461216861565547591654330 := by decide +kernel
private theorem rec_2_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 0 256 = 10232878723356861109069371840 :=
  phaseBlock_append rec_2_10_2369_0_part0 rec_2_10_2369_0_part1 rfl rfl rfl
private theorem rec_2_10_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 256 256 = 6363695613720945440260695455 :=
  phaseBlock_append rec_2_10_2369_0_part2 rec_2_10_2369_0_part3 rfl rfl rfl
private theorem rec_2_10_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 0 512 = 16596574337077806549330067295 :=
  phaseBlock_append rec_2_10_2369_0_join0 rec_2_10_2369_0_join1 rfl rfl rfl
private theorem rec_2_10_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 512 256 = 3071926519157482899957048118 :=
  phaseBlock_append rec_2_10_2369_0_part4 rec_2_10_2369_0_part5 rfl rfl rfl
private theorem rec_2_10_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 768 157 = 484503355485064642071899117 :=
  phaseBlock_append rec_2_10_2369_0_part6 rec_2_10_2369_0_part7 rfl rfl rfl
private theorem rec_2_10_2369_0_join5 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 512 413 = 3556429874642547542028947235 :=
  phaseBlock_append rec_2_10_2369_0_join3 rec_2_10_2369_0_join4 rfl rfl rfl
private theorem rec_2_10_2369_0_join6 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 0) 0 925 = 20153004211720354091359014530 :=
  phaseBlock_append rec_2_10_2369_0_join2 rec_2_10_2369_0_join5 rfl rfl rfl

private theorem rec_2_10_2369_0 : fastPhase (bank 2 10).shape 179798 2369 20 1 0 7 0 = 20153004211720354091359014530 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_2_10_2369_0_join6

private theorem rec_2_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 0 128 = 5629857092780829451847455392 := by decide +kernel
private theorem rec_2_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 128 128 = 4586920684495339464116036256 := by decide +kernel
private theorem rec_2_10_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 256 128 = 3621016058971822277069697696 := by decide +kernel
private theorem rec_2_10_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 384 128 = 2728863445378213383909970445 := by decide +kernel
private theorem rec_2_10_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 512 128 = 1907237769420870901673919288 := by decide +kernel
private theorem rec_2_10_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 640 128 = 1152961638793214595337232980 := by decide +kernel
private theorem rec_2_10_2369_1_part6 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 768 128 = 462902446328504450489142910 := by decide +kernel
private theorem rec_2_10_2369_1_part7 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 896 29 = 15360326042318925375269124 := by decide +kernel
private theorem rec_2_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 0 256 = 10216777777276168915963491648 :=
  phaseBlock_append rec_2_10_2369_1_part0 rec_2_10_2369_1_part1 rfl rfl rfl
private theorem rec_2_10_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 256 256 = 6349879504350035660979668141 :=
  phaseBlock_append rec_2_10_2369_1_part2 rec_2_10_2369_1_part3 rfl rfl rfl
private theorem rec_2_10_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 0 512 = 16566657281626204576943159789 :=
  phaseBlock_append rec_2_10_2369_1_join0 rec_2_10_2369_1_join1 rfl rfl rfl
private theorem rec_2_10_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 512 256 = 3060199408214085497011152268 :=
  phaseBlock_append rec_2_10_2369_1_part4 rec_2_10_2369_1_part5 rfl rfl rfl
private theorem rec_2_10_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 768 157 = 478262772370823375864412034 :=
  phaseBlock_append rec_2_10_2369_1_part6 rec_2_10_2369_1_part7 rfl rfl rfl
private theorem rec_2_10_2369_1_join5 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 512 413 = 3538462180584908872875564302 :=
  phaseBlock_append rec_2_10_2369_1_join3 rec_2_10_2369_1_join4 rfl rfl rfl
private theorem rec_2_10_2369_1_join6 :
    phaseBlock (fastLayerG (bank 2 10).shape 179798 2369 20 1 0 7 1) 0 925 = 20105119462211113449818724091 :=
  phaseBlock_append rec_2_10_2369_1_join2 rec_2_10_2369_1_join5 rfl rfl rfl

private theorem rec_2_10_2369_1 : fastPhase (bank 2 10).shape 179798 2369 20 1 0 7 1 = 20105119462211113449818724091 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_2_10_2369_1_join6

theorem receipt_2_10 : Checked (bank 2 10) 20 0 7 := by
  refine checked_from_values (bank 2 10) 20 0 7
    (P3_7_1.checked (bank 2 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_10_2368_0 rec_2_10_2368_1 rec_2_10_2369_0 rec_2_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 0 128 = 29449086905045208780123091680 := by decide +kernel
private theorem rec_2_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 128 128 = 25572076021610847223363764960 := by decide +kernel
private theorem rec_2_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 256 128 = 21899575880884940507090244320 := by decide +kernel
private theorem rec_2_11_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 384 128 = 18425388936147508639553430240 := by decide +kernel
private theorem rec_2_11_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 512 128 = 15143388869024202860835140320 := by decide +kernel
private theorem rec_2_11_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 640 128 = 12047523389034262270131239474 := by decide +kernel
private theorem rec_2_11_2368_0_part6 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 768 128 = 9131817371943691759974550242 := by decide +kernel
private theorem rec_2_11_2368_0_part7 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 896 128 = 6390346850867340461483943540 := by decide +kernel
private theorem rec_2_11_2368_0_part8 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 1024 128 = 3817252687874580782965312102 := by decide +kernel
private theorem rec_2_11_2368_0_part9 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 1152 128 = 1406745651720103953590757429 := by decide +kernel
private theorem rec_2_11_2368_0_part10 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 1280 14 = 14365432264952341549304341 := by decide +kernel
private theorem rec_2_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 0 256 = 55021162926656056003486856640 :=
  phaseBlock_append rec_2_11_2368_0_part0 rec_2_11_2368_0_part1 rfl rfl rfl
private theorem rec_2_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 384 256 = 33568777805171711500388570560 :=
  phaseBlock_append rec_2_11_2368_0_part3 rec_2_11_2368_0_part4 rfl rfl rfl
private theorem rec_2_11_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 256 384 = 55468353686056652007478814880 :=
  phaseBlock_append rec_2_11_2368_0_part2 rec_2_11_2368_0_join1 rfl rfl rfl
private theorem rec_2_11_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 0 640 = 110489516612712708010965671520 :=
  phaseBlock_append rec_2_11_2368_0_join0 rec_2_11_2368_0_join2 rfl rfl rfl
private theorem rec_2_11_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 768 256 = 15522164222811032221458493782 :=
  phaseBlock_append rec_2_11_2368_0_part6 rec_2_11_2368_0_part7 rfl rfl rfl
private theorem rec_2_11_2368_0_join5 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 640 384 = 27569687611845294491589733256 :=
  phaseBlock_append rec_2_11_2368_0_part5 rec_2_11_2368_0_join4 rfl rfl rfl
private theorem rec_2_11_2368_0_join6 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 1152 142 = 1421111083985056295140061770 :=
  phaseBlock_append rec_2_11_2368_0_part9 rec_2_11_2368_0_part10 rfl rfl rfl
private theorem rec_2_11_2368_0_join7 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 1024 270 = 5238363771859637078105373872 :=
  phaseBlock_append rec_2_11_2368_0_part8 rec_2_11_2368_0_join6 rfl rfl rfl
private theorem rec_2_11_2368_0_join8 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 640 654 = 32808051383704931569695107128 :=
  phaseBlock_append rec_2_11_2368_0_join5 rec_2_11_2368_0_join7 rfl rfl rfl
private theorem rec_2_11_2368_0_join9 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 0) 0 1294 = 143297567996417639580660778648 :=
  phaseBlock_append rec_2_11_2368_0_join3 rec_2_11_2368_0_join8 rfl rfl rfl

private theorem rec_2_11_2368_0 : fastPhase (bank 2 11).shape 179798 2368 32 1 0 7 0 = 143297567996417639580660778648 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_2_11_2368_0_join9

private theorem rec_2_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 0 128 = 29418402836003166088104606304 := by decide +kernel
private theorem rec_2_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 128 128 = 25542964816160962983303203424 := by decide +kernel
private theorem rec_2_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 256 128 = 21871990273677234430726838880 := by decide +kernel
private theorem rec_2_11_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 384 128 = 18399282206110330492299504224 := by decide +kernel
private theorem rec_2_11_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 512 128 = 15118714837006019645011966560 := by decide +kernel
private theorem rec_2_11_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 640 128 = 12024236409761826660474105508 := by decide +kernel
private theorem rec_2_11_2368_1_part6 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 768 128 = 9109872311464941288352262061 := by decide +kernel
private theorem rec_2_11_2368_1_part7 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 896 128 = 6369699103621664385051855320 := by decide +kernel
private theorem rec_2_11_2368_1_part8 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 1024 128 = 3797858181667964408159405710 := by decide +kernel
private theorem rec_2_11_2368_1_part9 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 1152 128 = 1388560845383323656153929218 := by decide +kernel
private theorem rec_2_11_2368_1_part10 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 1280 14 = 12448020464218552954748933 := by decide +kernel
private theorem rec_2_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 0 256 = 54961367652164129071407809728 :=
  phaseBlock_append rec_2_11_2368_1_part0 rec_2_11_2368_1_part1 rfl rfl rfl
private theorem rec_2_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 384 256 = 33517997043116350137311470784 :=
  phaseBlock_append rec_2_11_2368_1_part3 rec_2_11_2368_1_part4 rfl rfl rfl
private theorem rec_2_11_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 256 384 = 55389987316793584568038309664 :=
  phaseBlock_append rec_2_11_2368_1_part2 rec_2_11_2368_1_join1 rfl rfl rfl
private theorem rec_2_11_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 0 640 = 110351354968957713639446119392 :=
  phaseBlock_append rec_2_11_2368_1_join0 rec_2_11_2368_1_join2 rfl rfl rfl
private theorem rec_2_11_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 768 256 = 15479571415086605673404117381 :=
  phaseBlock_append rec_2_11_2368_1_part6 rec_2_11_2368_1_part7 rfl rfl rfl
private theorem rec_2_11_2368_1_join5 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 640 384 = 27503807824848432333878222889 :=
  phaseBlock_append rec_2_11_2368_1_part5 rec_2_11_2368_1_join4 rfl rfl rfl
private theorem rec_2_11_2368_1_join6 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 1152 142 = 1401008865847542209108678151 :=
  phaseBlock_append rec_2_11_2368_1_part9 rec_2_11_2368_1_part10 rfl rfl rfl
private theorem rec_2_11_2368_1_join7 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 1024 270 = 5198867047515506617268083861 :=
  phaseBlock_append rec_2_11_2368_1_part8 rec_2_11_2368_1_join6 rfl rfl rfl
private theorem rec_2_11_2368_1_join8 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 640 654 = 32702674872363938951146306750 :=
  phaseBlock_append rec_2_11_2368_1_join5 rec_2_11_2368_1_join7 rfl rfl rfl
private theorem rec_2_11_2368_1_join9 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2368 32 1 0 7 1) 0 1294 = 143054029841321652590592426142 :=
  phaseBlock_append rec_2_11_2368_1_join3 rec_2_11_2368_1_join8 rfl rfl rfl

private theorem rec_2_11_2368_1 : fastPhase (bank 2 11).shape 179798 2368 32 1 0 7 1 = 143054029841321652590592426142 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_2_11_2368_1_join9

private theorem rec_2_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 0 128 = 29449354439293445233996729536 := by decide +kernel
private theorem rec_2_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 128 128 = 25572294771931648827344596160 := by decide +kernel
private theorem rec_2_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 256 128 = 21899751218565608635203144896 := by decide +kernel
private theorem rec_2_11_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 384 128 = 18425526030655907152882166976 := by decide +kernel
private theorem rec_2_11_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 512 128 = 15143492690449859498132016320 := by decide +kernel
private theorem rec_2_11_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 640 128 = 12047598640319902423510912193 := by decide +kernel
private theorem rec_2_11_2369_0_part6 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 768 128 = 9131868599434976794037344722 := by decide +kernel
private theorem rec_2_11_2369_0_part7 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 896 128 = 6390378519185197783779714981 := by decide +kernel
private theorem rec_2_11_2369_0_part8 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 1024 128 = 3817269056195110013985325113 := by decide +kernel
private theorem rec_2_11_2369_0_part9 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 1152 128 = 1406750778818527399040793435 := by decide +kernel
private theorem rec_2_11_2369_0_part10 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 1280 14 = 14365477639119764627005713 := by decide +kernel
private theorem rec_2_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 0 256 = 55021649211225094061341325696 :=
  phaseBlock_append rec_2_11_2369_0_part0 rec_2_11_2369_0_part1 rfl rfl rfl
private theorem rec_2_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 384 256 = 33569018721105766651014183296 :=
  phaseBlock_append rec_2_11_2369_0_part3 rec_2_11_2369_0_part4 rfl rfl rfl
private theorem rec_2_11_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 256 384 = 55468769939671375286217328192 :=
  phaseBlock_append rec_2_11_2369_0_part2 rec_2_11_2369_0_join1 rfl rfl rfl
private theorem rec_2_11_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 0 640 = 110490419150896469347558653888 :=
  phaseBlock_append rec_2_11_2369_0_join0 rec_2_11_2369_0_join2 rfl rfl rfl
private theorem rec_2_11_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 768 256 = 15522247118620174577817059703 :=
  phaseBlock_append rec_2_11_2369_0_part6 rec_2_11_2369_0_part7 rfl rfl rfl
private theorem rec_2_11_2369_0_join5 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 640 384 = 27569845758940077001327971896 :=
  phaseBlock_append rec_2_11_2369_0_part5 rec_2_11_2369_0_join4 rfl rfl rfl
private theorem rec_2_11_2369_0_join6 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 1152 142 = 1421116256457647163667799148 :=
  phaseBlock_append rec_2_11_2369_0_part9 rec_2_11_2369_0_part10 rfl rfl rfl
private theorem rec_2_11_2369_0_join7 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 1024 270 = 5238385312652757177653124261 :=
  phaseBlock_append rec_2_11_2369_0_part8 rec_2_11_2369_0_join6 rfl rfl rfl
private theorem rec_2_11_2369_0_join8 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 640 654 = 32808231071592834178981096157 :=
  phaseBlock_append rec_2_11_2369_0_join5 rec_2_11_2369_0_join7 rfl rfl rfl
private theorem rec_2_11_2369_0_join9 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 0) 0 1294 = 143298650222489303526539750045 :=
  phaseBlock_append rec_2_11_2369_0_join3 rec_2_11_2369_0_join8 rfl rfl rfl

private theorem rec_2_11_2369_0 : fastPhase (bank 2 11).shape 179798 2369 32 1 0 7 0 = 143298650222489303526539750045 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_2_11_2369_0_join9

private theorem rec_2_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 0 128 = 29418670142530004992151317888 := by decide +kernel
private theorem rec_2_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 128 128 = 25543183360785474101211393408 := by decide +kernel
private theorem rec_2_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 256 128 = 21872165426704332893918719360 := by decide +kernel
private theorem rec_2_11_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 384 128 = 18399419136038953597826919808 := by decide +kernel
private theorem rec_2_11_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 512 128 = 15118818512970164268333198720 := by decide +kernel
private theorem rec_2_11_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 640 128 = 12024311533887948432915379621 := by decide +kernel
private theorem rec_2_11_2369_1_part6 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 768 128 = 9109923429301909908951445666 := by decide +kernel
private theorem rec_2_11_2369_1_part7 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 896 128 = 6369730678834174385521647492 := by decide +kernel
private theorem rec_2_11_2369_1_part8 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 1024 128 = 3797874472493635000372594650 := by decide +kernel
private theorem rec_2_11_2369_1_part9 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 1152 128 = 1388565909674155952018113469 := by decide +kernel
private theorem rec_2_11_2369_1_part10 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 1280 14 = 12448059821271916441011919 := by decide +kernel
private theorem rec_2_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 0 256 = 54961853503315479093362711296 :=
  phaseBlock_append rec_2_11_2369_1_part0 rec_2_11_2369_1_part1 rfl rfl rfl
private theorem rec_2_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 384 256 = 33518237649009117866160118528 :=
  phaseBlock_append rec_2_11_2369_1_part3 rec_2_11_2369_1_part4 rfl rfl rfl
private theorem rec_2_11_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 256 384 = 55390403075713450760078837888 :=
  phaseBlock_append rec_2_11_2369_1_part2 rec_2_11_2369_1_join1 rfl rfl rfl
private theorem rec_2_11_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 0 640 = 110352256579028929853441549184 :=
  phaseBlock_append rec_2_11_2369_1_join0 rec_2_11_2369_1_join2 rfl rfl rfl
private theorem rec_2_11_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 768 256 = 15479654108136084294473093158 :=
  phaseBlock_append rec_2_11_2369_1_part6 rec_2_11_2369_1_part7 rfl rfl rfl
private theorem rec_2_11_2369_1_join5 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 640 384 = 27503965642024032727388472779 :=
  phaseBlock_append rec_2_11_2369_1_part5 rec_2_11_2369_1_join4 rfl rfl rfl
private theorem rec_2_11_2369_1_join6 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 1152 142 = 1401013969495427868459125388 :=
  phaseBlock_append rec_2_11_2369_1_part9 rec_2_11_2369_1_part10 rfl rfl rfl
private theorem rec_2_11_2369_1_join7 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 1024 270 = 5198888441989062868831720038 :=
  phaseBlock_append rec_2_11_2369_1_part8 rec_2_11_2369_1_join6 rfl rfl rfl
private theorem rec_2_11_2369_1_join8 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 640 654 = 32702854084013095596220192817 :=
  phaseBlock_append rec_2_11_2369_1_join5 rec_2_11_2369_1_join7 rfl rfl rfl
private theorem rec_2_11_2369_1_join9 :
    phaseBlock (fastLayerG (bank 2 11).shape 179798 2369 32 1 0 7 1) 0 1294 = 143055110663042025449661742001 :=
  phaseBlock_append rec_2_11_2369_1_join3 rec_2_11_2369_1_join8 rfl rfl rfl

private theorem rec_2_11_2369_1 : fastPhase (bank 2 11).shape 179798 2369 32 1 0 7 1 = 143055110663042025449661742001 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_2_11_2369_1_join9

theorem receipt_2_11 : Checked (bank 2 11) 32 0 7 := by
  refine checked_from_values (bank 2 11) 32 0 7
    (P3_7_1.checked (bank 2 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_11_2368_0 rec_2_11_2368_1 rec_2_11_2369_0 rec_2_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 0 128 = 25400543028057466759770789088 := by decide +kernel
private theorem rec_2_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 128 128 = 22049984539943790022358410464 := by decide +kernel
private theorem rec_2_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 256 128 = 18877681692376093081684833504 := by decide +kernel
private theorem rec_2_12_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 384 128 = 15878146389565742137330222304 := by decide +kernel
private theorem rec_2_12_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 512 128 = 13045957219698822048970511584 := by decide +kernel
private theorem rec_2_12_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 640 128 = 10375761756857568085723239228 := by decide +kernel
private theorem rec_2_12_2368_0_part6 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 768 128 = 7862279375975099023601763539 := by decide +kernel
private theorem rec_2_12_2368_0_part7 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 896 128 = 5500278803016806032326945318 := by decide +kernel
private theorem rec_2_12_2368_0_part8 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 1024 128 = 3284589668576729755955418037 := by decide +kernel
private theorem rec_2_12_2368_0_part9 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 1152 128 = 1210106952704575693298523108 := by decide +kernel
private theorem rec_2_12_2368_0_part10 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 1280 14 = 12354824626347158706395320 := by decide +kernel
private theorem rec_2_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 0 256 = 47450527568001256782129199552 :=
  phaseBlock_append rec_2_12_2368_0_part0 rec_2_12_2368_0_part1 rfl rfl rfl
private theorem rec_2_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 384 256 = 28924103609264564186300733888 :=
  phaseBlock_append rec_2_12_2368_0_part3 rec_2_12_2368_0_part4 rfl rfl rfl
private theorem rec_2_12_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 256 384 = 47801785301640657267985567392 :=
  phaseBlock_append rec_2_12_2368_0_part2 rec_2_12_2368_0_join1 rfl rfl rfl
private theorem rec_2_12_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 0 640 = 95252312869641914050114766944 :=
  phaseBlock_append rec_2_12_2368_0_join0 rec_2_12_2368_0_join2 rfl rfl rfl
private theorem rec_2_12_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 768 256 = 13362558178991905055928708857 :=
  phaseBlock_append rec_2_12_2368_0_part6 rec_2_12_2368_0_part7 rfl rfl rfl
private theorem rec_2_12_2368_0_join5 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 640 384 = 23738319935849473141651948085 :=
  phaseBlock_append rec_2_12_2368_0_part5 rec_2_12_2368_0_join4 rfl rfl rfl
private theorem rec_2_12_2368_0_join6 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 1152 142 = 1222461777330922852004918428 :=
  phaseBlock_append rec_2_12_2368_0_part9 rec_2_12_2368_0_part10 rfl rfl rfl
private theorem rec_2_12_2368_0_join7 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 1024 270 = 4507051445907652607960336465 :=
  phaseBlock_append rec_2_12_2368_0_part8 rec_2_12_2368_0_join6 rfl rfl rfl
private theorem rec_2_12_2368_0_join8 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 640 654 = 28245371381757125749612284550 :=
  phaseBlock_append rec_2_12_2368_0_join5 rec_2_12_2368_0_join7 rfl rfl rfl
private theorem rec_2_12_2368_0_join9 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 0) 0 1294 = 123497684251399039799727051494 :=
  phaseBlock_append rec_2_12_2368_0_join3 rec_2_12_2368_0_join8 rfl rfl rfl

private theorem rec_2_12_2368_0 : fastPhase (bank 2 12).shape 179798 2368 31 1 0 7 0 = 123497684251399039799727051494 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_2_12_2368_0_join9

private theorem rec_2_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 0 128 = 25374018567800196623447542752 := by decide +kernel
private theorem rec_2_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 128 128 = 22024831718663863649312627680 := by decide +kernel
private theorem rec_2_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 256 128 = 18853858632456761823667088352 := by decide +kernel
private theorem rec_2_12_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 384 128 = 15855611723048122665177119712 := by decide +kernel
private theorem rec_2_12_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 512 128 = 13024670085923683535840545760 := by decide +kernel
private theorem rec_2_12_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 640 128 = 10355681795325244732757763532 := by decide +kernel
private theorem rec_2_12_2368_1_part6 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 768 128 = 7843366706495869264972763589 := by decide +kernel
private theorem rec_2_12_2368_1_part7 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 896 128 = 5482494039962227808406229797 := by decide +kernel
private theorem rec_2_12_2368_1_part8 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 1024 128 = 3267893925005477700168762164 := by decide +kernel
private theorem rec_2_12_2368_1_part9 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 1152 128 = 1194461838016076748166624842 := by decide +kernel
private theorem rec_2_12_2368_1_part10 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 1280 14 = 10705759492220227652642092 := by decide +kernel
private theorem rec_2_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 0 256 = 47398850286464060272760170432 :=
  phaseBlock_append rec_2_12_2368_1_part0 rec_2_12_2368_1_part1 rfl rfl rfl
private theorem rec_2_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 384 256 = 28880281808971806201017665472 :=
  phaseBlock_append rec_2_12_2368_1_part3 rec_2_12_2368_1_part4 rfl rfl rfl
private theorem rec_2_12_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 256 384 = 47734140441428568024684753824 :=
  phaseBlock_append rec_2_12_2368_1_part2 rec_2_12_2368_1_join1 rfl rfl rfl
private theorem rec_2_12_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 0 640 = 95132990727892628297444924256 :=
  phaseBlock_append rec_2_12_2368_1_join0 rec_2_12_2368_1_join2 rfl rfl rfl
private theorem rec_2_12_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 768 256 = 13325860746458097073378993386 :=
  phaseBlock_append rec_2_12_2368_1_part6 rec_2_12_2368_1_part7 rfl rfl rfl
private theorem rec_2_12_2368_1_join5 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 640 384 = 23681542541783341806136756918 :=
  phaseBlock_append rec_2_12_2368_1_part5 rec_2_12_2368_1_join4 rfl rfl rfl
private theorem rec_2_12_2368_1_join6 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 1152 142 = 1205167597508296975819266934 :=
  phaseBlock_append rec_2_12_2368_1_part9 rec_2_12_2368_1_part10 rfl rfl rfl
private theorem rec_2_12_2368_1_join7 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 1024 270 = 4473061522513774675988029098 :=
  phaseBlock_append rec_2_12_2368_1_part8 rec_2_12_2368_1_join6 rfl rfl rfl
private theorem rec_2_12_2368_1_join8 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 640 654 = 28154604064297116482124786016 :=
  phaseBlock_append rec_2_12_2368_1_join5 rec_2_12_2368_1_join7 rfl rfl rfl
private theorem rec_2_12_2368_1_join9 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2368 31 1 0 7 1) 0 1294 = 123287594792189744779569710272 :=
  phaseBlock_append rec_2_12_2368_1_join3 rec_2_12_2368_1_join8 rfl rfl rfl

private theorem rec_2_12_2368_1 : fastPhase (bank 2 12).shape 179798 2368 31 1 0 7 1 = 123287594792189744779569710272 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_2_12_2368_1_join9

private theorem rec_2_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 0 128 = 25400773930699840546782048512 := by decide +kernel
private theorem rec_2_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 128 128 = 22050173291902579309412430080 := by decide +kernel
private theorem rec_2_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 256 128 = 18877832949059014473726980352 := by decide +kernel
private theorem rec_2_12_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 384 128 = 15878264628437578125502296320 := by decide +kernel
private theorem rec_2_12_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 512 128 = 13046046742563545664227700992 := by decide +kernel
private theorem rec_2_12_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 640 128 = 10375826632593644858877759252 := by decide +kernel
private theorem rec_2_12_2369_0_part6 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 768 128 = 7862323533094223665997538005 := by decide +kernel
private theorem rec_2_12_2369_0_part7 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 896 128 = 5500306097017296996321472824 := by decide +kernel
private theorem rec_2_12_2369_0_part8 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 1024 128 = 3284603774996894515345447746 := by decide +kernel
private theorem rec_2_12_2369_0_part9 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 1152 128 = 1210111371378750532087404108 := by decide +kernel
private theorem rec_2_12_2369_0_part10 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 1280 14 = 12354863736767682503501358 := by decide +kernel
private theorem rec_2_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 0 256 = 47450947222602419856194478592 :=
  phaseBlock_append rec_2_12_2369_0_part0 rec_2_12_2369_0_part1 rfl rfl rfl
private theorem rec_2_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 384 256 = 28924311371001123789729997312 :=
  phaseBlock_append rec_2_12_2369_0_part3 rec_2_12_2369_0_part4 rfl rfl rfl
private theorem rec_2_12_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 256 384 = 47802144320060138263456977664 :=
  phaseBlock_append rec_2_12_2369_0_part2 rec_2_12_2369_0_join1 rfl rfl rfl
private theorem rec_2_12_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 0 640 = 95253091542662558119651456256 :=
  phaseBlock_append rec_2_12_2369_0_join0 rec_2_12_2369_0_join2 rfl rfl rfl
private theorem rec_2_12_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 768 256 = 13362629630111520662319010829 :=
  phaseBlock_append rec_2_12_2369_0_part6 rec_2_12_2369_0_part7 rfl rfl rfl
private theorem rec_2_12_2369_0_join5 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 640 384 = 23738456262705165521196770081 :=
  phaseBlock_append rec_2_12_2369_0_part5 rec_2_12_2369_0_join4 rfl rfl rfl
private theorem rec_2_12_2369_0_join6 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 1152 142 = 1222466235115518214590905466 :=
  phaseBlock_append rec_2_12_2369_0_part9 rec_2_12_2369_0_part10 rfl rfl rfl
private theorem rec_2_12_2369_0_join7 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 1024 270 = 4507070010112412729936353212 :=
  phaseBlock_append rec_2_12_2369_0_part8 rec_2_12_2369_0_join6 rfl rfl rfl
private theorem rec_2_12_2369_0_join8 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 640 654 = 28245526272817578251133123293 :=
  phaseBlock_append rec_2_12_2369_0_join5 rec_2_12_2369_0_join7 rfl rfl rfl
private theorem rec_2_12_2369_0_join9 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 0) 0 1294 = 123498617815480136370784579549 :=
  phaseBlock_append rec_2_12_2369_0_join3 rec_2_12_2369_0_join8 rfl rfl rfl

private theorem rec_2_12_2369_0 : fastPhase (bank 2 12).shape 179798 2369 31 1 0 7 0 = 123498617815480136370784579549 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_2_12_2369_0_join9

private theorem rec_2_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 0 128 = 25374249273353950960889444736 := by decide +kernel
private theorem rec_2_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 128 128 = 22025020292683648726678288768 := by decide +kernel
private theorem rec_2_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 256 128 = 18854009729482227861391686016 := by decide +kernel
private theorem rec_2_12_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 384 128 = 15855729819688576091784591744 := by decide +kernel
private theorem rec_2_12_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 512 128 = 13024759483140147663727704448 := by decide +kernel
private theorem rec_2_12_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 640 128 = 10355746561272715830002015617 := by decide +kernel
private theorem rec_2_12_2369_1_part6 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 768 128 = 7843410768983134905003931179 := by decide +kernel
private theorem rec_2_12_2369_1_part7 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 896 128 = 5482521253647109323348552789 := by decide +kernel
private theorem rec_2_12_2369_1_part8 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 1024 128 = 3267907964601668625628820133 := by decide +kernel
private theorem rec_2_12_2369_1_part9 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 1152 128 = 1194466202547721850845593807 := by decide +kernel
private theorem rec_2_12_2369_1_part10 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 1280 14 = 10705793416129828714767342 := by decide +kernel
private theorem rec_2_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 0 256 = 47399269566037599687567733504 :=
  phaseBlock_append rec_2_12_2369_1_part0 rec_2_12_2369_1_part1 rfl rfl rfl
private theorem rec_2_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 384 256 = 28880489302828723755512296192 :=
  phaseBlock_append rec_2_12_2369_1_part3 rec_2_12_2369_1_part4 rfl rfl rfl
private theorem rec_2_12_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 256 384 = 47734499032310951616903982208 :=
  phaseBlock_append rec_2_12_2369_1_part2 rec_2_12_2369_1_join1 rfl rfl rfl
private theorem rec_2_12_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 0 640 = 95133768598348551304471715712 :=
  phaseBlock_append rec_2_12_2369_1_join0 rec_2_12_2369_1_join2 rfl rfl rfl
private theorem rec_2_12_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 768 256 = 13325932022630244228352483968 :=
  phaseBlock_append rec_2_12_2369_1_part6 rec_2_12_2369_1_part7 rfl rfl rfl
private theorem rec_2_12_2369_1_join5 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 640 384 = 23681678583902960058354499585 :=
  phaseBlock_append rec_2_12_2369_1_part5 rec_2_12_2369_1_join4 rfl rfl rfl
private theorem rec_2_12_2369_1_join6 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 1152 142 = 1205171995963851679560361149 :=
  phaseBlock_append rec_2_12_2369_1_part9 rec_2_12_2369_1_part10 rfl rfl rfl
private theorem rec_2_12_2369_1_join7 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 1024 270 = 4473079960565520305189181282 :=
  phaseBlock_append rec_2_12_2369_1_part8 rec_2_12_2369_1_join6 rfl rfl rfl
private theorem rec_2_12_2369_1_join8 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 640 654 = 28154758544468480363543680867 :=
  phaseBlock_append rec_2_12_2369_1_join5 rec_2_12_2369_1_join7 rfl rfl rfl
private theorem rec_2_12_2369_1_join9 :
    phaseBlock (fastLayerG (bank 2 12).shape 179798 2369 31 1 0 7 1) 0 1294 = 123288527142817031668015396579 :=
  phaseBlock_append rec_2_12_2369_1_join3 rec_2_12_2369_1_join8 rfl rfl rfl

private theorem rec_2_12_2369_1 : fastPhase (bank 2 12).shape 179798 2369 31 1 0 7 1 = 123288527142817031668015396579 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_2_12_2369_1_join9

theorem receipt_2_12 : Checked (bank 2 12) 31 0 7 := by
  refine checked_from_values (bank 2 12) 31 0 7
    (P3_7_1.checked (bank 2 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_12_2368_0 rec_2_12_2368_1 rec_2_12_2369_0 rec_2_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 0 128 = 100378988493075676432459937952 := by decide +kernel
private theorem rec_2_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 128 128 = 90787278146336151730463803552 := by decide +kernel
private theorem rec_2_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 256 128 = 81570444364148632800669096096 := by decide +kernel
private theorem rec_2_13_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 384 128 = 72719929357533303480323090592 := by decide +kernel
private theorem rec_2_13_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 512 128 = 64227257823401018384837245088 := by decide +kernel
private theorem rec_2_13_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 640 128 = 56084036636578292768660048032 := by decide +kernel
private theorem rec_2_13_2368_0_part6 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 768 128 = 48281954541832292386149865632 := by decide +kernel
private theorem rec_2_13_2368_0_part7 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 896 128 = 40812786259839901851820794015 := by decide +kernel
private theorem rec_2_13_2368_0_part8 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 1024 128 = 33668403394715566341272674139 := by decide +kernel
private theorem rec_2_13_2368_0_part9 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 1152 128 = 26840730492429241084799808942 := by decide +kernel
private theorem rec_2_13_2368_0_part10 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 1280 128 = 20321761986686343620966325454 := by decide +kernel
private theorem rec_2_13_2368_0_part11 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 1408 128 = 14103572903190185682040021617 := by decide +kernel
private theorem rec_2_13_2368_0_part12 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 1536 128 = 8178318565251671757513346143 := by decide +kernel
private theorem rec_2_13_2368_0_part13 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 1664 123 = 2541510850374927915578176893 := by decide +kernel
private theorem rec_2_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 128 256 = 172357722510484784531132899648 :=
  phaseBlock_append rec_2_13_2368_0_part1 rec_2_13_2368_0_part2 rfl rfl rfl
private theorem rec_2_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 0 384 = 272736711003560460963592837600 :=
  phaseBlock_append rec_2_13_2368_0_part0 rec_2_13_2368_0_join0 rfl rfl rfl
private theorem rec_2_13_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 384 256 = 136947187180934321865160335680 :=
  phaseBlock_append rec_2_13_2368_0_part3 rec_2_13_2368_0_part4 rfl rfl rfl
private theorem rec_2_13_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 640 256 = 104365991178410585154809913664 :=
  phaseBlock_append rec_2_13_2368_0_part5 rec_2_13_2368_0_part6 rfl rfl rfl
private theorem rec_2_13_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 384 512 = 241313178359344907019970249344 :=
  phaseBlock_append rec_2_13_2368_0_join2 rec_2_13_2368_0_join3 rfl rfl rfl
private theorem rec_2_13_2368_0_join5 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 0 896 = 514049889362905367983563086944 :=
  phaseBlock_append rec_2_13_2368_0_join1 rec_2_13_2368_0_join4 rfl rfl rfl
private theorem rec_2_13_2368_0_join6 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 1024 256 = 60509133887144807426072483081 :=
  phaseBlock_append rec_2_13_2368_0_part8 rec_2_13_2368_0_part9 rfl rfl rfl
private theorem rec_2_13_2368_0_join7 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 896 384 = 101321920146984709277893277096 :=
  phaseBlock_append rec_2_13_2368_0_part7 rec_2_13_2368_0_join6 rfl rfl rfl
private theorem rec_2_13_2368_0_join8 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 1280 256 = 34425334889876529303006347071 :=
  phaseBlock_append rec_2_13_2368_0_part10 rec_2_13_2368_0_part11 rfl rfl rfl
private theorem rec_2_13_2368_0_join9 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 1536 251 = 10719829415626599673091523036 :=
  phaseBlock_append rec_2_13_2368_0_part12 rec_2_13_2368_0_part13 rfl rfl rfl
private theorem rec_2_13_2368_0_join10 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 1280 507 = 45145164305503128976097870107 :=
  phaseBlock_append rec_2_13_2368_0_join8 rec_2_13_2368_0_join9 rfl rfl rfl
private theorem rec_2_13_2368_0_join11 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 896 891 = 146467084452487838253991147203 :=
  phaseBlock_append rec_2_13_2368_0_join7 rec_2_13_2368_0_join10 rfl rfl rfl
private theorem rec_2_13_2368_0_join12 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 0) 0 1787 = 660516973815393206237554234147 :=
  phaseBlock_append rec_2_13_2368_0_join5 rec_2_13_2368_0_join11 rfl rfl rfl

private theorem rec_2_13_2368_0 : fastPhase (bank 2 13).shape 179798 2368 44 1 0 7 0 = 660516973815393206237554234147 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_2_13_2368_0_join12

private theorem rec_2_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 0 128 = 100303597719283493193549690400 := by decide +kernel
private theorem rec_2_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 128 128 = 90714762058196054887949542944 := by decide +kernel
private theorem rec_2_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 256 128 = 81500737713543901323448227360 := by decide +kernel
private theorem rec_2_13_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 384 128 = 72652967526578836897803535904 := by decide +kernel
private theorem rec_2_13_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 512 128 = 64162976822085123970173302304 := by decide +kernel
private theorem rec_2_13_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 640 128 = 56022373100404472721988249120 := by decide +kernel
private theorem rec_2_13_2368_1_part6 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 768 128 = 48222845729461031017824835104 := by decide +kernel
private theorem rec_2_13_2368_1_part7 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 896 128 = 40756170045021294023147489232 := by decide +kernel
private theorem rec_2_13_2368_1_part8 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 1024 128 = 33614218237217967374391381089 := by decide +kernel
private theorem rec_2_13_2368_1_part9 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 1152 128 = 26788915457663508118546484047 := by decide +kernel
private theorem rec_2_13_2368_1_part10 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 1280 128 = 20272256754807838943407496097 := by decide +kernel
private theorem rec_2_13_2368_1_part11 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 1408 128 = 14056317766745947269756573816 := by decide +kernel
private theorem rec_2_13_2368_1_part12 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 1536 128 = 8133254426770789229201575736 := by decide +kernel
private theorem rec_2_13_2368_1_part13 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 1664 123 = 2500216925306227201462342582 := by decide +kernel
private theorem rec_2_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 128 256 = 172215499771739956211397770304 :=
  phaseBlock_append rec_2_13_2368_1_part1 rec_2_13_2368_1_part2 rfl rfl rfl
private theorem rec_2_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 0 384 = 272519097491023449404947460704 :=
  phaseBlock_append rec_2_13_2368_1_part0 rec_2_13_2368_1_join0 rfl rfl rfl
private theorem rec_2_13_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 384 256 = 136815944348663960867976838208 :=
  phaseBlock_append rec_2_13_2368_1_part3 rec_2_13_2368_1_part4 rfl rfl rfl
private theorem rec_2_13_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 640 256 = 104245218829865503739813084224 :=
  phaseBlock_append rec_2_13_2368_1_part5 rec_2_13_2368_1_part6 rfl rfl rfl
private theorem rec_2_13_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 384 512 = 241061163178529464607789922432 :=
  phaseBlock_append rec_2_13_2368_1_join2 rec_2_13_2368_1_join3 rfl rfl rfl
private theorem rec_2_13_2368_1_join5 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 0 896 = 513580260669552914012737383136 :=
  phaseBlock_append rec_2_13_2368_1_join1 rec_2_13_2368_1_join4 rfl rfl rfl
private theorem rec_2_13_2368_1_join6 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 1024 256 = 60403133694881475492937865136 :=
  phaseBlock_append rec_2_13_2368_1_part8 rec_2_13_2368_1_part9 rfl rfl rfl
private theorem rec_2_13_2368_1_join7 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 896 384 = 101159303739902769516085354368 :=
  phaseBlock_append rec_2_13_2368_1_part7 rec_2_13_2368_1_join6 rfl rfl rfl
private theorem rec_2_13_2368_1_join8 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 1280 256 = 34328574521553786213164069913 :=
  phaseBlock_append rec_2_13_2368_1_part10 rec_2_13_2368_1_part11 rfl rfl rfl
private theorem rec_2_13_2368_1_join9 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 1536 251 = 10633471352077016430663918318 :=
  phaseBlock_append rec_2_13_2368_1_part12 rec_2_13_2368_1_part13 rfl rfl rfl
private theorem rec_2_13_2368_1_join10 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 1280 507 = 44962045873630802643827988231 :=
  phaseBlock_append rec_2_13_2368_1_join8 rec_2_13_2368_1_join9 rfl rfl rfl
private theorem rec_2_13_2368_1_join11 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 896 891 = 146121349613533572159913342599 :=
  phaseBlock_append rec_2_13_2368_1_join7 rec_2_13_2368_1_join10 rfl rfl rfl
private theorem rec_2_13_2368_1_join12 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2368 44 1 0 7 1) 0 1787 = 659701610283086486172650725735 :=
  phaseBlock_append rec_2_13_2368_1_join5 rec_2_13_2368_1_join11 rfl rfl rfl

private theorem rec_2_13_2368_1 : fastPhase (bank 2 13).shape 179798 2368 44 1 0 7 1 = 659701610283086486172650725735 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_2_13_2368_1_join12

private theorem rec_2_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 0 128 = 100379907317643330544029603936 := by decide +kernel
private theorem rec_2_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 128 128 = 90788074594015078955948034144 := by decide +kernel
private theorem rec_2_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 256 128 = 81571128148984555154238634080 := by decide +kernel
private theorem rec_2_13_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 384 128 = 72720509918230976427985152096 := by decide +kernel
private theorem rec_2_13_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 512 128 = 64227744326139764185375561824 := by decide +kernel
private theorem rec_2_13_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 640 128 = 56084437977816758600622704736 := by decide +kernel
private theorem rec_2_13_2369_0_part6 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 768 128 = 48282279351102433260884932704 := by decide +kernel
private theorem rec_2_13_2369_0_part7 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 896 128 = 40813042752535483025915100741 := by decide +kernel
private theorem rec_2_13_2369_0_part8 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 1024 128 = 33668599531393860419321565183 := by decide +kernel
private theorem rec_2_13_2369_0_part9 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 1152 128 = 26840874258779121161561035197 := by decide +kernel
private theorem rec_2_13_2369_0_part10 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 1280 128 = 20321861095074042892258404189 := by decide +kernel
private theorem rec_2_13_2369_0_part11 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 1408 128 = 14103634799755334589336143757 := by decide +kernel
private theorem rec_2_13_2369_0_part12 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 1536 128 = 8178350427239137466109769956 := by decide +kernel
private theorem rec_2_13_2369_0_part13 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 1664 123 = 2541519600320675727874733496 := by decide +kernel
private theorem rec_2_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 128 256 = 172359202742999634110186668224 :=
  phaseBlock_append rec_2_13_2369_0_part1 rec_2_13_2369_0_part2 rfl rfl rfl
private theorem rec_2_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 0 384 = 272739110060642964654216272160 :=
  phaseBlock_append rec_2_13_2369_0_part0 rec_2_13_2369_0_join0 rfl rfl rfl
private theorem rec_2_13_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 384 256 = 136948254244370740613360713920 :=
  phaseBlock_append rec_2_13_2369_0_part3 rec_2_13_2369_0_part4 rfl rfl rfl
private theorem rec_2_13_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 640 256 = 104366717328919191861507637440 :=
  phaseBlock_append rec_2_13_2369_0_part5 rec_2_13_2369_0_part6 rfl rfl rfl
private theorem rec_2_13_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 384 512 = 241314971573289932474868351360 :=
  phaseBlock_append rec_2_13_2369_0_join2 rec_2_13_2369_0_join3 rfl rfl rfl
private theorem rec_2_13_2369_0_join5 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 0 896 = 514054081633932897129084623520 :=
  phaseBlock_append rec_2_13_2369_0_join1 rec_2_13_2369_0_join4 rfl rfl rfl
private theorem rec_2_13_2369_0_join6 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 1024 256 = 60509473790172981580882600380 :=
  phaseBlock_append rec_2_13_2369_0_part8 rec_2_13_2369_0_part9 rfl rfl rfl
private theorem rec_2_13_2369_0_join7 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 896 384 = 101322516542708464606797701121 :=
  phaseBlock_append rec_2_13_2369_0_part7 rec_2_13_2369_0_join6 rfl rfl rfl
private theorem rec_2_13_2369_0_join8 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 1280 256 = 34425495894829377481594547946 :=
  phaseBlock_append rec_2_13_2369_0_part10 rec_2_13_2369_0_part11 rfl rfl rfl
private theorem rec_2_13_2369_0_join9 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 1536 251 = 10719870027559813193984503452 :=
  phaseBlock_append rec_2_13_2369_0_part12 rec_2_13_2369_0_part13 rfl rfl rfl
private theorem rec_2_13_2369_0_join10 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 1280 507 = 45145365922389190675579051398 :=
  phaseBlock_append rec_2_13_2369_0_join8 rec_2_13_2369_0_join9 rfl rfl rfl
private theorem rec_2_13_2369_0_join11 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 896 891 = 146467882465097655282376752519 :=
  phaseBlock_append rec_2_13_2369_0_join7 rec_2_13_2369_0_join10 rfl rfl rfl
private theorem rec_2_13_2369_0_join12 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 0) 0 1787 = 660521964099030552411461376039 :=
  phaseBlock_append rec_2_13_2369_0_join5 rec_2_13_2369_0_join11 rfl rfl rfl

private theorem rec_2_13_2369_0 : fastPhase (bank 2 13).shape 179798 2369 44 1 0 7 0 = 660521964099030552411461376039 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_2_13_2369_0_join12

private theorem rec_2_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 0 128 = 100304515979979912442676347872 := by decide +kernel
private theorem rec_2_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 128 128 = 90715557982052718045818368992 := by decide +kernel
private theorem rec_2_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 256 128 = 81501421013259563258922263520 := by decide +kernel
private theorem rec_2_13_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 384 128 = 72653547639526827836067943392 := by decide +kernel
private theorem rec_2_13_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 512 128 = 64163462913128818855842563040 := by decide +kernel
private theorem rec_2_13_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 640 128 = 56022774064701985368261161952 := by decide +kernel
private theorem rec_2_13_2369_1_part6 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 768 128 = 48223170195259133041687307232 := by decide +kernel
private theorem rec_2_13_2369_1_part7 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 896 128 = 40756426226635514369068529415 := by decide +kernel
private theorem rec_2_13_2369_1_part8 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 1024 128 = 33614414094220591219111928238 := by decide +kernel
private theorem rec_2_13_2369_1_part9 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 1152 128 = 26789058974457157754659069350 := by decide +kernel
private theorem rec_2_13_2369_1_part10 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 1280 128 = 20272355642491133155453221606 := by decide +kernel
private theorem rec_2_13_2369_1_part11 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 1408 128 = 14056379470199818790050044384 := by decide +kernel
private theorem rec_2_13_2369_1_part12 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 1536 128 = 8133286121998811896713896910 := by decide +kernel
private theorem rec_2_13_2369_1_part13 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 1664 123 = 2500225538698199148376525287 := by decide +kernel
private theorem rec_2_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 128 256 = 172216978995312281304740632512 :=
  phaseBlock_append rec_2_13_2369_1_part1 rec_2_13_2369_1_part2 rfl rfl rfl
private theorem rec_2_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 0 384 = 272521494975292193747416980384 :=
  phaseBlock_append rec_2_13_2369_1_part0 rec_2_13_2369_1_join0 rfl rfl rfl
private theorem rec_2_13_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 384 256 = 136817010552655646691910506432 :=
  phaseBlock_append rec_2_13_2369_1_part3 rec_2_13_2369_1_part4 rfl rfl rfl
private theorem rec_2_13_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 640 256 = 104245944259961118409948469184 :=
  phaseBlock_append rec_2_13_2369_1_part5 rec_2_13_2369_1_part6 rfl rfl rfl
private theorem rec_2_13_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 384 512 = 241062954812616765101858975616 :=
  phaseBlock_append rec_2_13_2369_1_join2 rec_2_13_2369_1_join3 rfl rfl rfl
private theorem rec_2_13_2369_1_join5 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 0 896 = 513584449787908958849275956000 :=
  phaseBlock_append rec_2_13_2369_1_join1 rec_2_13_2369_1_join4 rfl rfl rfl
private theorem rec_2_13_2369_1_join6 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 1024 256 = 60403473068677748973770997588 :=
  phaseBlock_append rec_2_13_2369_1_part8 rec_2_13_2369_1_part9 rfl rfl rfl
private theorem rec_2_13_2369_1_join7 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 896 384 = 101159899295313263342839527003 :=
  phaseBlock_append rec_2_13_2369_1_part7 rec_2_13_2369_1_join6 rfl rfl rfl
private theorem rec_2_13_2369_1_join8 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 1280 256 = 34328735112690951945503265990 :=
  phaseBlock_append rec_2_13_2369_1_part10 rec_2_13_2369_1_part11 rfl rfl rfl
private theorem rec_2_13_2369_1_join9 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 1536 251 = 10633511660697011045090422197 :=
  phaseBlock_append rec_2_13_2369_1_part12 rec_2_13_2369_1_part13 rfl rfl rfl
private theorem rec_2_13_2369_1_join10 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 1280 507 = 44962246773387962990593688187 :=
  phaseBlock_append rec_2_13_2369_1_join8 rec_2_13_2369_1_join9 rfl rfl rfl
private theorem rec_2_13_2369_1_join11 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 896 891 = 146122146068701226333433215190 :=
  phaseBlock_append rec_2_13_2369_1_join7 rec_2_13_2369_1_join10 rfl rfl rfl
private theorem rec_2_13_2369_1_join12 :
    phaseBlock (fastLayerG (bank 2 13).shape 179798 2369 44 1 0 7 1) 0 1787 = 659706595856610185182709171190 :=
  phaseBlock_append rec_2_13_2369_1_join5 rec_2_13_2369_1_join11 rfl rfl rfl

private theorem rec_2_13_2369_1 : fastPhase (bank 2 13).shape 179798 2369 44 1 0 7 1 = 659706595856610185182709171190 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_2_13_2369_1_join12

theorem receipt_2_13 : Checked (bank 2 13) 44 0 7 := by
  refine checked_from_values (bank 2 13) 44 0 7
    (P3_7_1.checked (bank 2 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_13_2368_0 rec_2_13_2368_1 rec_2_13_2369_0 rec_2_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 0 128 = 1181394885136101720433934282784 := by decide +kernel
private theorem rec_2_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 128 128 = 1118643428565272172276768989216 := by decide +kernel
private theorem rec_2_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 256 128 = 1057297975828982952223135731744 := by decide +kernel
private theorem rec_2_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 384 128 = 997339680273962341106781569056 := by decide +kernel
private theorem rec_2_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 512 128 = 938749815221240993665250357280 := by decide +kernel
private theorem rec_2_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 640 128 = 881509773658176928400755597344 := by decide +kernel
private theorem rec_2_14_2368_0_part6 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 768 128 = 825601067930480517441053282336 := by decide +kernel
private theorem rec_2_14_2368_0_part7 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 896 128 = 771005329434239476400314744864 := by decide +kernel
private theorem rec_2_14_2368_0_part8 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1024 128 = 717704308307943854239999504416 := by decide +kernel
private theorem rec_2_14_2368_0_part9 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1152 128 = 665679873124511023129728114720 := by decide +kernel
private theorem rec_2_14_2368_0_part10 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1280 128 = 614914010583310668308155011104 := by decide +kernel
private theorem rec_2_14_2368_0_part11 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1408 128 = 565388825202189777943841357856 := by decide +kernel
private theorem rec_2_14_2368_0_part12 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1536 128 = 517086539185659431352113276952 := by decide +kernel
private theorem rec_2_14_2368_0_part13 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1664 128 = 469989532042182174183441802840 := by decide +kernel
private theorem rec_2_14_2368_0_part14 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1792 128 = 424080330951660765939194285323 := by decide +kernel
private theorem rec_2_14_2368_0_part15 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1920 128 = 379341484346237012941263618211 := by decide +kernel
private theorem rec_2_14_2368_0_part16 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2048 128 = 335755644786548357962388118104 := by decide +kernel
private theorem rec_2_14_2368_0_part17 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2176 128 = 293305581128523276768118531713 := by decide +kernel
private theorem rec_2_14_2368_0_part18 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2304 128 = 251974178201506368871872905059 := by decide +kernel
private theorem rec_2_14_2368_0_part19 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2432 128 = 211744436568926871852888654143 := by decide +kernel
private theorem rec_2_14_2368_0_part20 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2560 128 = 172599472248799572157876066723 := by decide +kernel
private theorem rec_2_14_2368_0_part21 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2688 128 = 134522516302461378491641121354 := by decide +kernel
private theorem rec_2_14_2368_0_part22 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2816 128 = 97496914567744798987425311882 := by decide +kernel
private theorem rec_2_14_2368_0_part23 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2944 128 = 61506127405655969295882089972 := by decide +kernel
private theorem rec_2_14_2368_0_part24 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 3072 128 = 26533729316993596416234496452 := by decide +kernel
private theorem rec_2_14_2368_0_part25 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 3200 35 = 1299125251202009856151237338 := by decide +kernel
private theorem rec_2_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 128 256 = 2175941404394255124499904720960 :=
  phaseBlock_append rec_2_14_2368_0_part1 rec_2_14_2368_0_part2 rfl rfl rfl
private theorem rec_2_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 0 384 = 3357336289530356844933839003744 :=
  phaseBlock_append rec_2_14_2368_0_part0 rec_2_14_2368_0_join0 rfl rfl rfl
private theorem rec_2_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 512 256 = 1820259588879417922066005954624 :=
  phaseBlock_append rec_2_14_2368_0_part4 rec_2_14_2368_0_part5 rfl rfl rfl
private theorem rec_2_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 384 384 = 2817599269153380263172787523680 :=
  phaseBlock_append rec_2_14_2368_0_part3 rec_2_14_2368_0_join2 rfl rfl rfl
private theorem rec_2_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 0 768 = 6174935558683737108106626527424 :=
  phaseBlock_append rec_2_14_2368_0_join1 rec_2_14_2368_0_join3 rfl rfl rfl
private theorem rec_2_14_2368_0_join5 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 896 256 = 1488709637742183330640314249280 :=
  phaseBlock_append rec_2_14_2368_0_part7 rec_2_14_2368_0_part8 rfl rfl rfl
private theorem rec_2_14_2368_0_join6 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 768 384 = 2314310705672663848081367531616 :=
  phaseBlock_append rec_2_14_2368_0_part6 rec_2_14_2368_0_join5 rfl rfl rfl
private theorem rec_2_14_2368_0_join7 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1152 256 = 1280593883707821691437883125824 :=
  phaseBlock_append rec_2_14_2368_0_part9 rec_2_14_2368_0_part10 rfl rfl rfl
private theorem rec_2_14_2368_0_join8 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1408 256 = 1082475364387849209295954634808 :=
  phaseBlock_append rec_2_14_2368_0_part11 rec_2_14_2368_0_part12 rfl rfl rfl
private theorem rec_2_14_2368_0_join9 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1152 512 = 2363069248095670900733837760632 :=
  phaseBlock_append rec_2_14_2368_0_join7 rec_2_14_2368_0_join8 rfl rfl rfl
private theorem rec_2_14_2368_0_join10 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 768 896 = 4677379953768334748815205292248 :=
  phaseBlock_append rec_2_14_2368_0_join6 rec_2_14_2368_0_join9 rfl rfl rfl
private theorem rec_2_14_2368_0_join11 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 0 1664 = 10852315512452071856921831819672 :=
  phaseBlock_append rec_2_14_2368_0_join4 rec_2_14_2368_0_join10 rfl rfl rfl
private theorem rec_2_14_2368_0_join12 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1792 256 = 803421815297897778880457903534 :=
  phaseBlock_append rec_2_14_2368_0_part14 rec_2_14_2368_0_part15 rfl rfl rfl
private theorem rec_2_14_2368_0_join13 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1664 384 = 1273411347340079953063899706374 :=
  phaseBlock_append rec_2_14_2368_0_part13 rec_2_14_2368_0_join12 rfl rfl rfl
private theorem rec_2_14_2368_0_join14 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2176 256 = 545279759330029645639991436772 :=
  phaseBlock_append rec_2_14_2368_0_part17 rec_2_14_2368_0_part18 rfl rfl rfl
private theorem rec_2_14_2368_0_join15 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2048 384 = 881035404116578003602379554876 :=
  phaseBlock_append rec_2_14_2368_0_part16 rec_2_14_2368_0_join14 rfl rfl rfl
private theorem rec_2_14_2368_0_join16 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1664 768 = 2154446751456657956666279261250 :=
  phaseBlock_append rec_2_14_2368_0_join13 rec_2_14_2368_0_join15 rfl rfl rfl
private theorem rec_2_14_2368_0_join17 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2560 256 = 307121988551260950649517188077 :=
  phaseBlock_append rec_2_14_2368_0_part20 rec_2_14_2368_0_part21 rfl rfl rfl
private theorem rec_2_14_2368_0_join18 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2432 384 = 518866425120187822502405842220 :=
  phaseBlock_append rec_2_14_2368_0_part19 rec_2_14_2368_0_join17 rfl rfl rfl
private theorem rec_2_14_2368_0_join19 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2816 256 = 159003041973400768283307401854 :=
  phaseBlock_append rec_2_14_2368_0_part22 rec_2_14_2368_0_part23 rfl rfl rfl
private theorem rec_2_14_2368_0_join20 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 3072 163 = 27832854568195606272385733790 :=
  phaseBlock_append rec_2_14_2368_0_part24 rec_2_14_2368_0_part25 rfl rfl rfl
private theorem rec_2_14_2368_0_join21 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2816 419 = 186835896541596374555693135644 :=
  phaseBlock_append rec_2_14_2368_0_join19 rec_2_14_2368_0_join20 rfl rfl rfl
private theorem rec_2_14_2368_0_join22 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 2432 803 = 705702321661784197058098977864 :=
  phaseBlock_append rec_2_14_2368_0_join18 rec_2_14_2368_0_join21 rfl rfl rfl
private theorem rec_2_14_2368_0_join23 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 1664 1571 = 2860149073118442153724378239114 :=
  phaseBlock_append rec_2_14_2368_0_join16 rec_2_14_2368_0_join22 rfl rfl rfl
private theorem rec_2_14_2368_0_join24 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 0) 0 3235 = 13712464585570514010646210058786 :=
  phaseBlock_append rec_2_14_2368_0_join11 rec_2_14_2368_0_join23 rfl rfl rfl

private theorem rec_2_14_2368_0 : fastPhase (bank 2 14).shape 179798 2368 76 1 0 7 0 = 13712464585570514010646210058786 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_2_14_2368_0_join24

private theorem rec_2_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 0 128 = 1180905756759124302800935316256 := by decide +kernel
private theorem rec_2_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 128 128 = 1118165043997456402221853309728 := by decide +kernel
private theorem rec_2_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 256 128 = 1056830191475188094356318194464 := by decide +kernel
private theorem rec_2_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 384 128 = 996882353455434955531124218656 := by decide +kernel
private theorem rec_2_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 512 128 = 938302804173256723160098286368 := by decide +kernel
private theorem rec_2_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 640 128 = 881072937527682285604972804896 := by decide +kernel
private theorem rec_2_14_2368_1_part6 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 768 128 = 825174266773734672036258532128 := by decide +kernel
private theorem rec_2_14_2368_1_part7 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 896 128 = 770588424214456042294117423904 := by decide +kernel
private theorem rec_2_14_2368_1_part8 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1024 128 = 717297160892932676749235481376 := by decide +kernel
private theorem rec_2_14_2368_1_part9 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1152 128 = 665282346284319966163695598368 := by decide +kernel
private theorem rec_2_14_2368_1_part10 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1280 128 = 614525967987867401551850408736 := by decide +kernel
private theorem rec_2_14_2368_1_part11 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1408 128 = 565010131418943564041195133728 := by decide +kernel
private theorem rec_2_14_2368_1_part12 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1536 128 = 516717059677104886039055619732 := by decide +kernel
private theorem rec_2_14_2368_1_part13 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1664 128 = 469629133135553614517527846171 := by decide +kernel
private theorem rec_2_14_2368_1_part14 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1792 128 = 423728879804490755375462903709 := by decide +kernel
private theorem rec_2_14_2368_1_part15 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1920 128 = 378998848997863161089840037570 := by decide +kernel
private theorem rec_2_14_2368_1_part16 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2048 128 = 335421694163414680261663877411 := by decide +kernel
private theorem rec_2_14_2368_1_part17 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2176 128 = 292980185041829654777593069837 := by decide +kernel
private theorem rec_2_14_2368_1_part18 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2304 128 = 251657207344892058880312486380 := by decide +kernel
private theorem rec_2_14_2368_1_part19 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2432 128 = 211435762516103612868835923114 := by decide +kernel
private theorem rec_2_14_2368_1_part20 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2560 128 = 172298967451116785519046664625 := by decide +kernel
private theorem rec_2_14_2368_1_part21 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2688 128 = 134230054086596034325272811614 := by decide +kernel
private theorem rec_2_14_2368_1_part22 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2816 128 = 97212369133382626417060353862 := by decide +kernel
private theorem rec_2_14_2368_1_part23 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2944 128 = 61229373823036451714683667712 := by decide +kernel
private theorem rec_2_14_2368_1_part24 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 3072 128 = 26264643524574556307592033888 := by decide +kernel
private theorem rec_2_14_2368_1_part25 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 3200 35 = 1226865813650287877579522646 := by decide +kernel
private theorem rec_2_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 128 256 = 2174995235472644496578171504192 :=
  phaseBlock_append rec_2_14_2368_1_part1 rec_2_14_2368_1_part2 rfl rfl rfl
private theorem rec_2_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 0 384 = 3355900992231768799379106820448 :=
  phaseBlock_append rec_2_14_2368_1_part0 rec_2_14_2368_1_join0 rfl rfl rfl
private theorem rec_2_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 512 256 = 1819375741700939008765071091264 :=
  phaseBlock_append rec_2_14_2368_1_part4 rec_2_14_2368_1_part5 rfl rfl rfl
private theorem rec_2_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 384 384 = 2816258095156373964296195309920 :=
  phaseBlock_append rec_2_14_2368_1_part3 rec_2_14_2368_1_join2 rfl rfl rfl
private theorem rec_2_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 0 768 = 6172159087388142763675302130368 :=
  phaseBlock_append rec_2_14_2368_1_join1 rec_2_14_2368_1_join3 rfl rfl rfl
private theorem rec_2_14_2368_1_join5 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 896 256 = 1487885585107388719043352905280 :=
  phaseBlock_append rec_2_14_2368_1_part7 rec_2_14_2368_1_part8 rfl rfl rfl
private theorem rec_2_14_2368_1_join6 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 768 384 = 2313059851881123391079611437408 :=
  phaseBlock_append rec_2_14_2368_1_part6 rec_2_14_2368_1_join5 rfl rfl rfl
private theorem rec_2_14_2368_1_join7 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1152 256 = 1279808314272187367715546007104 :=
  phaseBlock_append rec_2_14_2368_1_part9 rec_2_14_2368_1_part10 rfl rfl rfl
private theorem rec_2_14_2368_1_join8 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1408 256 = 1081727191096048450080250753460 :=
  phaseBlock_append rec_2_14_2368_1_part11 rec_2_14_2368_1_part12 rfl rfl rfl
private theorem rec_2_14_2368_1_join9 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1152 512 = 2361535505368235817795796760564 :=
  phaseBlock_append rec_2_14_2368_1_join7 rec_2_14_2368_1_join8 rfl rfl rfl
private theorem rec_2_14_2368_1_join10 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 768 896 = 4674595357249359208875408197972 :=
  phaseBlock_append rec_2_14_2368_1_join6 rec_2_14_2368_1_join9 rfl rfl rfl
private theorem rec_2_14_2368_1_join11 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 0 1664 = 10846754444637501972550710328340 :=
  phaseBlock_append rec_2_14_2368_1_join4 rec_2_14_2368_1_join10 rfl rfl rfl
private theorem rec_2_14_2368_1_join12 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1792 256 = 802727728802353916465302941279 :=
  phaseBlock_append rec_2_14_2368_1_part14 rec_2_14_2368_1_part15 rfl rfl rfl
private theorem rec_2_14_2368_1_join13 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1664 384 = 1272356861937907530982830787450 :=
  phaseBlock_append rec_2_14_2368_1_part13 rec_2_14_2368_1_join12 rfl rfl rfl
private theorem rec_2_14_2368_1_join14 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2176 256 = 544637392386721713657905556217 :=
  phaseBlock_append rec_2_14_2368_1_part17 rec_2_14_2368_1_part18 rfl rfl rfl
private theorem rec_2_14_2368_1_join15 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2048 384 = 880059086550136393919569433628 :=
  phaseBlock_append rec_2_14_2368_1_part16 rec_2_14_2368_1_join14 rfl rfl rfl
private theorem rec_2_14_2368_1_join16 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1664 768 = 2152415948488043924902400221078 :=
  phaseBlock_append rec_2_14_2368_1_join13 rec_2_14_2368_1_join15 rfl rfl rfl
private theorem rec_2_14_2368_1_join17 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2560 256 = 306529021537712819844319476239 :=
  phaseBlock_append rec_2_14_2368_1_part20 rec_2_14_2368_1_part21 rfl rfl rfl
private theorem rec_2_14_2368_1_join18 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2432 384 = 517964784053816432713155399353 :=
  phaseBlock_append rec_2_14_2368_1_part19 rec_2_14_2368_1_join17 rfl rfl rfl
private theorem rec_2_14_2368_1_join19 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2816 256 = 158441742956419078131744021574 :=
  phaseBlock_append rec_2_14_2368_1_part22 rec_2_14_2368_1_part23 rfl rfl rfl
private theorem rec_2_14_2368_1_join20 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 3072 163 = 27491509338224844185171556534 :=
  phaseBlock_append rec_2_14_2368_1_part24 rec_2_14_2368_1_part25 rfl rfl rfl
private theorem rec_2_14_2368_1_join21 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2816 419 = 185933252294643922316915578108 :=
  phaseBlock_append rec_2_14_2368_1_join19 rec_2_14_2368_1_join20 rfl rfl rfl
private theorem rec_2_14_2368_1_join22 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 2432 803 = 703898036348460355030070977461 :=
  phaseBlock_append rec_2_14_2368_1_join18 rec_2_14_2368_1_join21 rfl rfl rfl
private theorem rec_2_14_2368_1_join23 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 1664 1571 = 2856313984836504279932471198539 :=
  phaseBlock_append rec_2_14_2368_1_join16 rec_2_14_2368_1_join22 rfl rfl rfl
private theorem rec_2_14_2368_1_join24 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2368 76 1 0 7 1) 0 3235 = 13703068429474006252483181526879 :=
  phaseBlock_append rec_2_14_2368_1_join11 rec_2_14_2368_1_join23 rfl rfl rfl

private theorem rec_2_14_2368_1 : fastPhase (bank 2 14).shape 179798 2368 76 1 0 7 1 = 13703068429474006252483181526879 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_2_14_2368_1_join24

private theorem rec_2_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 0 128 = 1181405807442443761871433825632 := by decide +kernel
private theorem rec_2_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 128 128 = 1118653537761980014220596047200 := by decide +kernel
private theorem rec_2_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 256 128 = 1057307307591622748600148024672 := by decide +kernel
private theorem rec_2_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 384 128 = 997348269682249173035505569120 := by decide +kernel
private theorem rec_2_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 512 128 = 938757696763109055240398617952 := by decide +kernel
private theorem rec_2_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 640 128 = 881516981233838937263791877472 := by decide +kernel
private theorem rec_2_14_2369_0_part6 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 768 128 = 825607634856476350136805465440 := by decide +kernel
private theorem rec_2_14_2369_0_part7 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 896 128 = 771011288447474028519635553632 := by decide +kernel
private theorem rec_2_14_2369_0_part8 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1024 128 = 717709691569714125348475010400 := by decide +kernel
private theorem rec_2_14_2369_0_part9 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1152 128 = 665684712224522426482434043232 := by decide +kernel
private theorem rec_2_14_2369_0_part10 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1280 128 = 614918336543682565350460841312 := by decide +kernel
private theorem rec_2_14_2369_0_part11 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1408 128 = 565392668481450237598262218080 := by decide +kernel
private theorem rec_2_14_2369_0_part12 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1536 128 = 517089929626872952327313321132 := by decide +kernel
private theorem rec_2_14_2369_0_part13 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1664 128 = 469992497323309559458799737872 := by decide +kernel
private theorem rec_2_14_2369_0_part14 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1792 128 = 424082899483400246865289271754 := by decide +kernel
private theorem rec_2_14_2369_0_part15 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1920 128 = 379343684897600456192510261663 := by decide +kernel
private theorem rec_2_14_2369_0_part16 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2048 128 = 335757505565628935509900132262 := by decide +kernel
private theorem rec_2_14_2369_0_part17 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2176 128 = 293307129751221300342604754374 := by decide +kernel
private theorem rec_2_14_2369_0_part18 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2304 128 = 251975441700809931373321076201 := by decide +kernel
private theorem rec_2_14_2369_0_part19 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2432 128 = 211745441445375027840134295773 := by decide +kernel
private theorem rec_2_14_2369_0_part20 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2560 128 = 172600244423164095485216981778 := by decide +kernel
private theorem rec_2_14_2369_0_part21 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2688 128 = 134523081134130179741954607075 := by decide +kernel
private theorem rec_2_14_2369_0_part22 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2816 128 = 97497296871147788795150597612 := by decide +kernel
private theorem rec_2_14_2369_0_part23 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2944 128 = 61506351447049766211592766024 := by decide +kernel
private theorem rec_2_14_2369_0_part24 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 3072 128 = 26533818813502446779751799761 := by decide +kernel
private theorem rec_2_14_2369_0_part25 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 3200 35 = 1299129369127919733431183184 := by decide +kernel
private theorem rec_2_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 128 256 = 2175960845353602762820744071872 :=
  phaseBlock_append rec_2_14_2369_0_part1 rec_2_14_2369_0_part2 rfl rfl rfl
private theorem rec_2_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 0 384 = 3357366652796046524692177897504 :=
  phaseBlock_append rec_2_14_2369_0_part0 rec_2_14_2369_0_join0 rfl rfl rfl
private theorem rec_2_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 512 256 = 1820274677996947992504190495424 :=
  phaseBlock_append rec_2_14_2369_0_part4 rec_2_14_2369_0_part5 rfl rfl rfl
private theorem rec_2_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 384 384 = 2817622947679197165539696064544 :=
  phaseBlock_append rec_2_14_2369_0_part3 rec_2_14_2369_0_join2 rfl rfl rfl
private theorem rec_2_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 0 768 = 6174989600475243690231873962048 :=
  phaseBlock_append rec_2_14_2369_0_join1 rec_2_14_2369_0_join3 rfl rfl rfl
private theorem rec_2_14_2369_0_join5 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 896 256 = 1488720980017188153868110564032 :=
  phaseBlock_append rec_2_14_2369_0_part7 rec_2_14_2369_0_part8 rfl rfl rfl
private theorem rec_2_14_2369_0_join6 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 768 384 = 2314328614873664504004916029472 :=
  phaseBlock_append rec_2_14_2369_0_part6 rec_2_14_2369_0_join5 rfl rfl rfl
private theorem rec_2_14_2369_0_join7 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1152 256 = 1280603048768204991832894884544 :=
  phaseBlock_append rec_2_14_2369_0_part9 rec_2_14_2369_0_part10 rfl rfl rfl
private theorem rec_2_14_2369_0_join8 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1408 256 = 1082482598108323189925575539212 :=
  phaseBlock_append rec_2_14_2369_0_part11 rec_2_14_2369_0_part12 rfl rfl rfl
private theorem rec_2_14_2369_0_join9 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1152 512 = 2363085646876528181758470423756 :=
  phaseBlock_append rec_2_14_2369_0_join7 rec_2_14_2369_0_join8 rfl rfl rfl
private theorem rec_2_14_2369_0_join10 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 768 896 = 4677414261750192685763386453228 :=
  phaseBlock_append rec_2_14_2369_0_join6 rec_2_14_2369_0_join9 rfl rfl rfl
private theorem rec_2_14_2369_0_join11 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 0 1664 = 10852403862225436375995260415276 :=
  phaseBlock_append rec_2_14_2369_0_join4 rec_2_14_2369_0_join10 rfl rfl rfl
private theorem rec_2_14_2369_0_join12 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1792 256 = 803426584381000703057799533417 :=
  phaseBlock_append rec_2_14_2369_0_part14 rec_2_14_2369_0_part15 rfl rfl rfl
private theorem rec_2_14_2369_0_join13 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1664 384 = 1273419081704310262516599271289 :=
  phaseBlock_append rec_2_14_2369_0_part13 rec_2_14_2369_0_join12 rfl rfl rfl
private theorem rec_2_14_2369_0_join14 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2176 256 = 545282571452031231715925830575 :=
  phaseBlock_append rec_2_14_2369_0_part17 rec_2_14_2369_0_part18 rfl rfl rfl
private theorem rec_2_14_2369_0_join15 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2048 384 = 881040077017660167225825962837 :=
  phaseBlock_append rec_2_14_2369_0_part16 rec_2_14_2369_0_join14 rfl rfl rfl
private theorem rec_2_14_2369_0_join16 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1664 768 = 2154459158721970429742425234126 :=
  phaseBlock_append rec_2_14_2369_0_join13 rec_2_14_2369_0_join15 rfl rfl rfl
private theorem rec_2_14_2369_0_join17 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2560 256 = 307123325557294275227171588853 :=
  phaseBlock_append rec_2_14_2369_0_part20 rec_2_14_2369_0_part21 rfl rfl rfl
private theorem rec_2_14_2369_0_join18 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2432 384 = 518868767002669303067305884626 :=
  phaseBlock_append rec_2_14_2369_0_part19 rec_2_14_2369_0_join17 rfl rfl rfl
private theorem rec_2_14_2369_0_join19 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2816 256 = 159003648318197555006743363636 :=
  phaseBlock_append rec_2_14_2369_0_part22 rec_2_14_2369_0_part23 rfl rfl rfl
private theorem rec_2_14_2369_0_join20 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 3072 163 = 27832948182630366513182982945 :=
  phaseBlock_append rec_2_14_2369_0_part24 rec_2_14_2369_0_part25 rfl rfl rfl
private theorem rec_2_14_2369_0_join21 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2816 419 = 186836596500827921519926346581 :=
  phaseBlock_append rec_2_14_2369_0_join19 rec_2_14_2369_0_join20 rfl rfl rfl
private theorem rec_2_14_2369_0_join22 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 2432 803 = 705705363503497224587232231207 :=
  phaseBlock_append rec_2_14_2369_0_join18 rec_2_14_2369_0_join21 rfl rfl rfl
private theorem rec_2_14_2369_0_join23 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 1664 1571 = 2860164522225467654329657465333 :=
  phaseBlock_append rec_2_14_2369_0_join16 rec_2_14_2369_0_join22 rfl rfl rfl
private theorem rec_2_14_2369_0_join24 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 0) 0 3235 = 13712568384450904030324917880609 :=
  phaseBlock_append rec_2_14_2369_0_join11 rec_2_14_2369_0_join23 rfl rfl rfl

private theorem rec_2_14_2369_0 : fastPhase (bank 2 14).shape 179798 2369 76 1 0 7 0 = 13712568384450904030324917880609 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_2_14_2369_0_join24

private theorem rec_2_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 0 128 = 1180916675366906627046710955168 := by decide +kernel
private theorem rec_2_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 128 128 = 1118175149644059610126262516896 := by decide +kernel
private theorem rec_2_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 256 128 = 1056839519833243142754180639904 := by decide +kernel
private theorem rec_2_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 384 128 = 996890939601744233414523788448 := by decide +kernel
private theorem rec_2_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 512 128 = 938310682592864173485067570336 := by decide +kernel
private theorem rec_2_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 640 128 = 881080142117932751884225379488 := by decide +kernel
private theorem rec_2_14_2369_1_part6 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 768 128 = 825180830848322469717969038496 := by decide +kernel
private theorem rec_2_14_2369_1_part7 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 896 128 = 770594380507462754926749441184 := by decide +kernel
private theorem rec_2_14_2369_1_part8 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1024 128 = 717302541562854176932417195168 := by decide +kernel
private theorem rec_2_14_2369_1_part9 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1152 128 = 665287182918082661285143264416 := by decide +kernel
private theorem rec_2_14_2369_1_part10 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1280 128 = 614530291604833704310339611808 := by decide +kernel
private theorem rec_2_14_2369_1_part11 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1408 128 = 565013972474906587755579841696 := by decide +kernel
private theorem rec_2_14_2369_1_part12 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1536 128 = 516720448012453179527248941387 := by decide +kernel
private theorem rec_2_14_2369_1_part13 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1664 128 = 469632096426710253669938437048 := by decide +kernel
private theorem rec_2_14_2369_1_part14 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1792 128 = 423731446459967892259409154773 := by decide +kernel
private theorem rec_2_14_2369_1_part15 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1920 128 = 379001047783930853617172273294 := by decide +kernel
private theorem rec_2_14_2369_1_part16 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2048 128 = 335423553285430365352148747194 := by decide +kernel
private theorem rec_2_14_2369_1_part17 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2176 128 = 292981732112994494748596560527 := by decide +kernel
private theorem rec_2_14_2369_1_part18 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2304 128 = 251658469395535336384295757969 := by decide +kernel
private theorem rec_2_14_2369_1_part19 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2432 128 = 211436766044092194473426124993 := by decide +kernel
private theorem rec_2_14_2369_1_part20 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2560 128 = 172299738374590181513072191795 := by decide +kernel
private theorem rec_2_14_2369_1_part21 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2688 128 = 134230617762342385398141427562 := by decide +kernel
private theorem rec_2_14_2369_1_part22 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2816 128 = 97212750373244385022170452300 := by decide +kernel
private theorem rec_2_14_2369_1_part23 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2944 128 = 61229596890697571947435152268 := by decide +kernel
private theorem rec_2_14_2369_1_part24 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 3072 128 = 26264732134618918581698102384 := by decide +kernel
private theorem rec_2_14_2369_1_part25 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 3200 35 = 1226869704051201283506794995 := by decide +kernel
private theorem rec_2_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 128 256 = 2175014669477302752880443156800 :=
  phaseBlock_append rec_2_14_2369_1_part1 rec_2_14_2369_1_part2 rfl rfl rfl
private theorem rec_2_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 0 384 = 3355931344844209379927154111968 :=
  phaseBlock_append rec_2_14_2369_1_part0 rec_2_14_2369_1_join0 rfl rfl rfl
private theorem rec_2_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 512 256 = 1819390824710796925369292949824 :=
  phaseBlock_append rec_2_14_2369_1_part4 rec_2_14_2369_1_part5 rfl rfl rfl
private theorem rec_2_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 384 384 = 2816281764312541158783816738272 :=
  phaseBlock_append rec_2_14_2369_1_part3 rec_2_14_2369_1_join2 rfl rfl rfl
private theorem rec_2_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 0 768 = 6172213109156750538710970850240 :=
  phaseBlock_append rec_2_14_2369_1_join1 rec_2_14_2369_1_join3 rfl rfl rfl
private theorem rec_2_14_2369_1_join5 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 896 256 = 1487896922070316931859166636352 :=
  phaseBlock_append rec_2_14_2369_1_part7 rec_2_14_2369_1_part8 rfl rfl rfl
private theorem rec_2_14_2369_1_join6 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 768 384 = 2313077752918639401577135674848 :=
  phaseBlock_append rec_2_14_2369_1_part6 rec_2_14_2369_1_join5 rfl rfl rfl
private theorem rec_2_14_2369_1_join7 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1152 256 = 1279817474522916365595482876224 :=
  phaseBlock_append rec_2_14_2369_1_part9 rec_2_14_2369_1_part10 rfl rfl rfl
private theorem rec_2_14_2369_1_join8 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1408 256 = 1081734420487359767282828783083 :=
  phaseBlock_append rec_2_14_2369_1_part11 rec_2_14_2369_1_part12 rfl rfl rfl
private theorem rec_2_14_2369_1_join9 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1152 512 = 2361551895010276132878311659307 :=
  phaseBlock_append rec_2_14_2369_1_join7 rec_2_14_2369_1_join8 rfl rfl rfl
private theorem rec_2_14_2369_1_join10 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 768 896 = 4674629647928915534455447334155 :=
  phaseBlock_append rec_2_14_2369_1_join6 rec_2_14_2369_1_join9 rfl rfl rfl
private theorem rec_2_14_2369_1_join11 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 0 1664 = 10846842757085666073166418184395 :=
  phaseBlock_append rec_2_14_2369_1_join4 rec_2_14_2369_1_join10 rfl rfl rfl
private theorem rec_2_14_2369_1_join12 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1792 256 = 802732494243898745876581428067 :=
  phaseBlock_append rec_2_14_2369_1_part14 rec_2_14_2369_1_part15 rfl rfl rfl
private theorem rec_2_14_2369_1_join13 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1664 384 = 1272364590670608999546519865115 :=
  phaseBlock_append rec_2_14_2369_1_part13 rec_2_14_2369_1_join12 rfl rfl rfl
private theorem rec_2_14_2369_1_join14 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2176 256 = 544640201508529831132892318496 :=
  phaseBlock_append rec_2_14_2369_1_part17 rec_2_14_2369_1_part18 rfl rfl rfl
private theorem rec_2_14_2369_1_join15 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2048 384 = 880063754793960196485041065690 :=
  phaseBlock_append rec_2_14_2369_1_part16 rec_2_14_2369_1_join14 rfl rfl rfl
private theorem rec_2_14_2369_1_join16 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1664 768 = 2152428345464569196031560930805 :=
  phaseBlock_append rec_2_14_2369_1_join13 rec_2_14_2369_1_join15 rfl rfl rfl
private theorem rec_2_14_2369_1_join17 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2560 256 = 306530356136932566911213619357 :=
  phaseBlock_append rec_2_14_2369_1_part20 rec_2_14_2369_1_part21 rfl rfl rfl
private theorem rec_2_14_2369_1_join18 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2432 384 = 517967122181024761384639744350 :=
  phaseBlock_append rec_2_14_2369_1_part19 rec_2_14_2369_1_join17 rfl rfl rfl
private theorem rec_2_14_2369_1_join19 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2816 256 = 158442347263941956969605604568 :=
  phaseBlock_append rec_2_14_2369_1_part22 rec_2_14_2369_1_part23 rfl rfl rfl
private theorem rec_2_14_2369_1_join20 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 3072 163 = 27491601838670119865204897379 :=
  phaseBlock_append rec_2_14_2369_1_part24 rec_2_14_2369_1_part25 rfl rfl rfl
private theorem rec_2_14_2369_1_join21 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2816 419 = 185933949102612076834810501947 :=
  phaseBlock_append rec_2_14_2369_1_join19 rec_2_14_2369_1_join20 rfl rfl rfl
private theorem rec_2_14_2369_1_join22 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 2432 803 = 703901071283636838219450246297 :=
  phaseBlock_append rec_2_14_2369_1_join18 rec_2_14_2369_1_join21 rfl rfl rfl
private theorem rec_2_14_2369_1_join23 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 1664 1571 = 2856329416748206034251011177102 :=
  phaseBlock_append rec_2_14_2369_1_join16 rec_2_14_2369_1_join22 rfl rfl rfl
private theorem rec_2_14_2369_1_join24 :
    phaseBlock (fastLayerG (bank 2 14).shape 179798 2369 76 1 0 7 1) 0 3235 = 13703172173833872107417429361497 :=
  phaseBlock_append rec_2_14_2369_1_join11 rec_2_14_2369_1_join23 rfl rfl rfl

private theorem rec_2_14_2369_1 : fastPhase (bank 2 14).shape 179798 2369 76 1 0 7 1 = 13703172173833872107417429361497 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_2_14_2369_1_join24

theorem receipt_2_14 : Checked (bank 2 14) 76 0 7 := by
  refine checked_from_values (bank 2 14) 76 0 7
    (P3_7_1.checked (bank 2 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_14605_3234)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_14_2368_0 rec_2_14_2368_1 rec_2_14_2369_0 rec_2_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 0 128 = 4767441865460221570815001127136 := by decide +kernel
private theorem rec_2_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 128 128 = 4571216131146329107028885010656 := by decide +kernel
private theorem rec_2_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 256 128 = 4378371626796562340129212500192 := by decide +kernel
private theorem rec_2_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 384 128 = 4188873789449914674181088909536 := by decide +kernel
private theorem rec_2_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 512 128 = 4002688219462054131840036677856 := by decide +kernel
private theorem rec_2_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 640 128 = 3819780680197348344212868217056 := by decide +kernel
private theorem rec_2_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 768 128 = 3640117097720889540718558759136 := by decide +kernel
private theorem rec_2_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 896 128 = 3463663560490519538949119203552 := by decide +kernel
private theorem rec_2_15_2368_0_part8 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1024 128 = 3290386319048854734530468964576 := by decide +kernel
private theorem rec_2_15_2368_0_part9 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1152 128 = 3120251785715311090983308818656 := by decide +kernel
private theorem rec_2_15_2368_0_part10 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1280 128 = 2953226534278129129583993751776 := by decide +kernel
private theorem rec_2_15_2368_0_part11 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1408 128 = 2789277299686398919225405806816 := by decide +kernel
private theorem rec_2_15_2368_0_part12 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1536 128 = 2628370977742085066277826930912 := by decide +kernel
private theorem rec_2_15_2368_0_part13 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1664 128 = 2470474624792051704449811822816 := by decide +kernel
private theorem rec_2_15_2368_0_part14 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1792 128 = 2315555457420087484649060780256 := by decide +kernel
private theorem rec_2_15_2368_0_part15 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1920 128 = 2163580852138930564843292547296 := by decide +kernel
private theorem rec_2_15_2368_0_part16 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2048 128 = 2014518358561398971185290292354 := by decide +kernel
private theorem rec_2_15_2368_0_part17 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2176 128 = 1868335855691297385341225421249 := by decide +kernel
private theorem rec_2_15_2368_0_part18 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2304 128 = 1725001286879136272561412562866 := by decide +kernel
private theorem rec_2_15_2368_0_part19 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2432 128 = 1584482598777539963816459034932 := by decide +kernel
private theorem rec_2_15_2368_0_part20 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2560 128 = 1446747894002276618617715267718 := by decide +kernel
private theorem rec_2_15_2368_0_part21 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2688 128 = 1311765433569513815226900294421 := by decide +kernel
private theorem rec_2_15_2368_0_part22 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2816 128 = 1179503636639638949068707252612 := by decide +kernel
private theorem rec_2_15_2368_0_part23 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2944 128 = 1049931080534767073920736002509 := by decide +kernel
private theorem rec_2_15_2368_0_part24 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3072 128 = 923016500204880158171160880940 := by decide +kernel
private theorem rec_2_15_2368_0_part25 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3200 128 = 798728787838525461652876416646 := by decide +kernel
private theorem rec_2_15_2368_0_part26 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3328 128 = 677036992664083459089929382282 := by decide +kernel
private theorem rec_2_15_2368_0_part27 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3456 128 = 557910320761543245925521214080 := by decide +kernel
private theorem rec_2_15_2368_0_part28 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3584 128 = 441318134522517105513839971043 := by decide +kernel
private theorem rec_2_15_2368_0_part29 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3712 128 = 327229952414755305364793921535 := by decide +kernel
private theorem rec_2_15_2368_0_part30 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3840 128 = 215615448791715568652944521403 := by decide +kernel
private theorem rec_2_15_2368_0_part31 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3968 128 = 106444453451070787811573104395 := by decide +kernel
private theorem rec_2_15_2368_0_part32 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 4096 63 = 13038488335181161734554939679 := by decide +kernel
private theorem rec_2_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 0 256 = 9338657996606550677843886137792 :=
  phaseBlock_append rec_2_15_2368_0_part0 rec_2_15_2368_0_part1 rfl rfl rfl
private theorem rec_2_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 256 256 = 8567245416246477014310301409728 :=
  phaseBlock_append rec_2_15_2368_0_part2 rec_2_15_2368_0_part3 rfl rfl rfl
private theorem rec_2_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 0 512 = 17905903412853027692154187547520 :=
  phaseBlock_append rec_2_15_2368_0_join0 rec_2_15_2368_0_join1 rfl rfl rfl
private theorem rec_2_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 512 256 = 7822468899659402476052904894912 :=
  phaseBlock_append rec_2_15_2368_0_part4 rec_2_15_2368_0_part5 rfl rfl rfl
private theorem rec_2_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 768 256 = 7103780658211409079667677962688 :=
  phaseBlock_append rec_2_15_2368_0_part6 rec_2_15_2368_0_part7 rfl rfl rfl
private theorem rec_2_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 512 512 = 14926249557870811555720582857600 :=
  phaseBlock_append rec_2_15_2368_0_join3 rec_2_15_2368_0_join4 rfl rfl rfl
private theorem rec_2_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 0 1024 = 32832152970723839247874770405120 :=
  phaseBlock_append rec_2_15_2368_0_join2 rec_2_15_2368_0_join5 rfl rfl rfl
private theorem rec_2_15_2368_0_join7 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1024 256 = 6410638104764165825513777783232 :=
  phaseBlock_append rec_2_15_2368_0_part8 rec_2_15_2368_0_part9 rfl rfl rfl
private theorem rec_2_15_2368_0_join8 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1280 256 = 5742503833964528048809399558592 :=
  phaseBlock_append rec_2_15_2368_0_part10 rec_2_15_2368_0_part11 rfl rfl rfl
private theorem rec_2_15_2368_0_join9 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1024 512 = 12153141938728693874323177341824 :=
  phaseBlock_append rec_2_15_2368_0_join7 rec_2_15_2368_0_join8 rfl rfl rfl
private theorem rec_2_15_2368_0_join10 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1536 256 = 5098845602534136770727638753728 :=
  phaseBlock_append rec_2_15_2368_0_part12 rec_2_15_2368_0_part13 rfl rfl rfl
private theorem rec_2_15_2368_0_join11 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1792 256 = 4479136309559018049492353327552 :=
  phaseBlock_append rec_2_15_2368_0_part14 rec_2_15_2368_0_part15 rfl rfl rfl
private theorem rec_2_15_2368_0_join12 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1536 512 = 9577981912093154820219992081280 :=
  phaseBlock_append rec_2_15_2368_0_join10 rec_2_15_2368_0_join11 rfl rfl rfl
private theorem rec_2_15_2368_0_join13 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 1024 1024 = 21731123850821848694543169423104 :=
  phaseBlock_append rec_2_15_2368_0_join9 rec_2_15_2368_0_join12 rfl rfl rfl
private theorem rec_2_15_2368_0_join14 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 0 2048 = 54563276821545687942417939828224 :=
  phaseBlock_append rec_2_15_2368_0_join6 rec_2_15_2368_0_join13 rfl rfl rfl
private theorem rec_2_15_2368_0_join15 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2048 256 = 3882854214252696356526515713603 :=
  phaseBlock_append rec_2_15_2368_0_part16 rec_2_15_2368_0_part17 rfl rfl rfl
private theorem rec_2_15_2368_0_join16 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2304 256 = 3309483885656676236377871597798 :=
  phaseBlock_append rec_2_15_2368_0_part18 rec_2_15_2368_0_part19 rfl rfl rfl
private theorem rec_2_15_2368_0_join17 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2048 512 = 7192338099909372592904387311401 :=
  phaseBlock_append rec_2_15_2368_0_join15 rec_2_15_2368_0_join16 rfl rfl rfl
private theorem rec_2_15_2368_0_join18 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2560 256 = 2758513327571790433844615562139 :=
  phaseBlock_append rec_2_15_2368_0_part20 rec_2_15_2368_0_part21 rfl rfl rfl
private theorem rec_2_15_2368_0_join19 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2816 256 = 2229434717174406022989443255121 :=
  phaseBlock_append rec_2_15_2368_0_part22 rec_2_15_2368_0_part23 rfl rfl rfl
private theorem rec_2_15_2368_0_join20 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2560 512 = 4987948044746196456834058817260 :=
  phaseBlock_append rec_2_15_2368_0_join18 rec_2_15_2368_0_join19 rfl rfl rfl
private theorem rec_2_15_2368_0_join21 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2048 1024 = 12180286144655569049738446128661 :=
  phaseBlock_append rec_2_15_2368_0_join17 rec_2_15_2368_0_join20 rfl rfl rfl
private theorem rec_2_15_2368_0_join22 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3072 256 = 1721745288043405619824037297586 :=
  phaseBlock_append rec_2_15_2368_0_part24 rec_2_15_2368_0_part25 rfl rfl rfl
private theorem rec_2_15_2368_0_join23 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3328 256 = 1234947313425626705015450596362 :=
  phaseBlock_append rec_2_15_2368_0_part26 rec_2_15_2368_0_part27 rfl rfl rfl
private theorem rec_2_15_2368_0_join24 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3072 512 = 2956692601469032324839487893948 :=
  phaseBlock_append rec_2_15_2368_0_join22 rec_2_15_2368_0_join23 rfl rfl rfl
private theorem rec_2_15_2368_0_join25 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3584 256 = 768548086937272410878633892578 :=
  phaseBlock_append rec_2_15_2368_0_part28 rec_2_15_2368_0_part29 rfl rfl rfl
private theorem rec_2_15_2368_0_join26 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3968 191 = 119482941786251949546128044074 :=
  phaseBlock_append rec_2_15_2368_0_part31 rec_2_15_2368_0_part32 rfl rfl rfl
private theorem rec_2_15_2368_0_join27 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3840 319 = 335098390577967518199072565477 :=
  phaseBlock_append rec_2_15_2368_0_part30 rec_2_15_2368_0_join26 rfl rfl rfl
private theorem rec_2_15_2368_0_join28 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3584 575 = 1103646477515239929077706458055 :=
  phaseBlock_append rec_2_15_2368_0_join25 rec_2_15_2368_0_join27 rfl rfl rfl
private theorem rec_2_15_2368_0_join29 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 3072 1087 = 4060339078984272253917194352003 :=
  phaseBlock_append rec_2_15_2368_0_join24 rec_2_15_2368_0_join28 rfl rfl rfl
private theorem rec_2_15_2368_0_join30 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 2048 2111 = 16240625223639841303655640480664 :=
  phaseBlock_append rec_2_15_2368_0_join21 rec_2_15_2368_0_join29 rfl rfl rfl
private theorem rec_2_15_2368_0_join31 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 0) 0 4159 = 70803902045185529246073580308888 :=
  phaseBlock_append rec_2_15_2368_0_join14 rec_2_15_2368_0_join30 rfl rfl rfl

private theorem rec_2_15_2368_0 : fastPhase (bank 2 15).shape 179798 2368 105 1 0 7 0 = 70803902045185529246073580308888 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_2_15_2368_0_join31

private theorem rec_2_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 0 128 = 4765916410667664825322901667936 := by decide +kernel
private theorem rec_2_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 128 128 = 4569716464830729977436087472224 := by decide +kernel
private theorem rec_2_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 256 128 = 4376897485892628483680262004832 := by decide +kernel
private theorem rec_2_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 384 128 = 4187424912139292572251873865824 := by decide +kernel
private theorem rec_2_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 512 128 = 4001264345170970877121024639072 := by decide +kernel
private theorem rec_2_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 640 128 = 3818381549594253427892341739616 := by decide +kernel
private theorem rec_2_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 768 128 = 3638742452714096639665851261024 := by decide +kernel
private theorem rec_2_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 896 128 = 3462313144225848302897850822752 := by decide +kernel
private theorem rec_2_15_2368_1_part8 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1024 128 = 3289059875907272573261782417504 := by decide +kernel
private theorem rec_2_15_2368_1_part9 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1152 128 = 3118949061310574961509105258592 := by decide +kernel
private theorem rec_2_15_2368_1_part10 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1280 128 = 2951947275454427323330168627296 := by decide +kernel
private theorem rec_2_15_2368_1_part11 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1408 128 = 2788021254515992849215084720224 := by decide +kernel
private theorem rec_2_15_2368_1_part12 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1536 128 = 2627137895522951054314601496672 := by decide +kernel
private theorem rec_2_15_2368_1_part13 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1664 128 = 2469264256045522768300975525984 := by decide +kernel
private theorem rec_2_15_2368_1_part14 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1792 128 = 2314367553888495125228844834912 := by decide +kernel
private theorem rec_2_15_2368_1_part15 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1920 128 = 2162415166783246553396101754976 := by decide +kernel
private theorem rec_2_15_2368_1_part16 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2048 128 = 2013374645551899601728090569774 := by decide +kernel
private theorem rec_2_15_2368_1_part17 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2176 128 = 1867213870311830895808807553217 := by decide +kernel
private theorem rec_2_15_2368_1_part18 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2304 128 = 1723900785552876906959694927832 := by decide +kernel
private theorem rec_2_15_2368_1_part19 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2432 128 = 1583403339137336959822841056390 := by decide +kernel
private theorem rec_2_15_2368_1_part20 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2560 128 = 1445689634889671100900469215220 := by decide +kernel
private theorem rec_2_15_2368_1_part21 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2688 128 = 1310727935032462264263095784165 := by decide +kernel
private theorem rec_2_15_2368_1_part22 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2816 128 = 1178486659930250018086122213018 := by decide +kernel
private theorem rec_2_15_2368_1_part23 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2944 128 = 1048934388106808178079102485711 := by decide +kernel
private theorem rec_2_15_2368_1_part24 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3072 128 = 922039855711401858180430972137 := by decide +kernel
private theorem rec_2_15_2368_1_part25 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3200 128 = 797771956129586879096906546555 := by decide +kernel
private theorem rec_2_15_2368_1_part26 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3328 128 = 676099739784416415053711083385 := by decide +kernel
private theorem rec_2_15_2368_1_part27 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3456 128 = 556992413948028614501996687455 := by decide +kernel
private theorem rec_2_15_2368_1_part28 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3584 128 = 440419342201916839518505307713 := by decide +kernel
private theorem rec_2_15_2368_1_part29 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3712 128 = 326350044201443104746141468370 := by decide +kernel
private theorem rec_2_15_2368_1_part30 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3840 128 = 214754195485156573626009320544 := by decide +kernel
private theorem rec_2_15_2368_1_part31 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3968 128 = 105601627033484056952880099613 := by decide +kernel
private theorem rec_2_15_2368_1_part32 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 4096 63 = 12630357149075417494232611506 := by decide +kernel
private theorem rec_2_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 0 256 = 9335632875498394802758989140160 :=
  phaseBlock_append rec_2_15_2368_1_part0 rec_2_15_2368_1_part1 rfl rfl rfl
private theorem rec_2_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 256 256 = 8564322398031921055932135870656 :=
  phaseBlock_append rec_2_15_2368_1_part2 rec_2_15_2368_1_part3 rfl rfl rfl
private theorem rec_2_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 0 512 = 17899955273530315858691125010816 :=
  phaseBlock_append rec_2_15_2368_1_join0 rec_2_15_2368_1_join1 rfl rfl rfl
private theorem rec_2_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 512 256 = 7819645894765224305013366378688 :=
  phaseBlock_append rec_2_15_2368_1_part4 rec_2_15_2368_1_part5 rfl rfl rfl
private theorem rec_2_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 768 256 = 7101055596939944942563702083776 :=
  phaseBlock_append rec_2_15_2368_1_part6 rec_2_15_2368_1_part7 rfl rfl rfl
private theorem rec_2_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 512 512 = 14920701491705169247577068462464 :=
  phaseBlock_append rec_2_15_2368_1_join3 rec_2_15_2368_1_join4 rfl rfl rfl
private theorem rec_2_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 0 1024 = 32820656765235485106268193473280 :=
  phaseBlock_append rec_2_15_2368_1_join2 rec_2_15_2368_1_join5 rfl rfl rfl
private theorem rec_2_15_2368_1_join7 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1024 256 = 6408008937217847534770887676096 :=
  phaseBlock_append rec_2_15_2368_1_part8 rec_2_15_2368_1_part9 rfl rfl rfl
private theorem rec_2_15_2368_1_join8 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1280 256 = 5739968529970420172545253347520 :=
  phaseBlock_append rec_2_15_2368_1_part10 rec_2_15_2368_1_part11 rfl rfl rfl
private theorem rec_2_15_2368_1_join9 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1024 512 = 12147977467188267707316141023616 :=
  phaseBlock_append rec_2_15_2368_1_join7 rec_2_15_2368_1_join8 rfl rfl rfl
private theorem rec_2_15_2368_1_join10 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1536 256 = 5096402151568473822615577022656 :=
  phaseBlock_append rec_2_15_2368_1_part12 rec_2_15_2368_1_part13 rfl rfl rfl
private theorem rec_2_15_2368_1_join11 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1792 256 = 4476782720671741678624946589888 :=
  phaseBlock_append rec_2_15_2368_1_part14 rec_2_15_2368_1_part15 rfl rfl rfl
private theorem rec_2_15_2368_1_join12 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1536 512 = 9573184872240215501240523612544 :=
  phaseBlock_append rec_2_15_2368_1_join10 rec_2_15_2368_1_join11 rfl rfl rfl
private theorem rec_2_15_2368_1_join13 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 1024 1024 = 21721162339428483208556664636160 :=
  phaseBlock_append rec_2_15_2368_1_join9 rec_2_15_2368_1_join12 rfl rfl rfl
private theorem rec_2_15_2368_1_join14 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 0 2048 = 54541819104663968314824858109440 :=
  phaseBlock_append rec_2_15_2368_1_join6 rec_2_15_2368_1_join13 rfl rfl rfl
private theorem rec_2_15_2368_1_join15 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2048 256 = 3880588515863730497536898122991 :=
  phaseBlock_append rec_2_15_2368_1_part16 rec_2_15_2368_1_part17 rfl rfl rfl
private theorem rec_2_15_2368_1_join16 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2304 256 = 3307304124690213866782535984222 :=
  phaseBlock_append rec_2_15_2368_1_part18 rec_2_15_2368_1_part19 rfl rfl rfl
private theorem rec_2_15_2368_1_join17 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2048 512 = 7187892640553944364319434107213 :=
  phaseBlock_append rec_2_15_2368_1_join15 rec_2_15_2368_1_join16 rfl rfl rfl
private theorem rec_2_15_2368_1_join18 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2560 256 = 2756417569922133365163564999385 :=
  phaseBlock_append rec_2_15_2368_1_part20 rec_2_15_2368_1_part21 rfl rfl rfl
private theorem rec_2_15_2368_1_join19 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2816 256 = 2227421048037058196165224698729 :=
  phaseBlock_append rec_2_15_2368_1_part22 rec_2_15_2368_1_part23 rfl rfl rfl
private theorem rec_2_15_2368_1_join20 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2560 512 = 4983838617959191561328789698114 :=
  phaseBlock_append rec_2_15_2368_1_join18 rec_2_15_2368_1_join19 rfl rfl rfl
private theorem rec_2_15_2368_1_join21 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2048 1024 = 12171731258513135925648223805327 :=
  phaseBlock_append rec_2_15_2368_1_join17 rec_2_15_2368_1_join20 rfl rfl rfl
private theorem rec_2_15_2368_1_join22 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3072 256 = 1719811811840988737277337518692 :=
  phaseBlock_append rec_2_15_2368_1_part24 rec_2_15_2368_1_part25 rfl rfl rfl
private theorem rec_2_15_2368_1_join23 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3328 256 = 1233092153732445029555707770840 :=
  phaseBlock_append rec_2_15_2368_1_part26 rec_2_15_2368_1_part27 rfl rfl rfl
private theorem rec_2_15_2368_1_join24 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3072 512 = 2952903965573433766833045289532 :=
  phaseBlock_append rec_2_15_2368_1_join22 rec_2_15_2368_1_join23 rfl rfl rfl
private theorem rec_2_15_2368_1_join25 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3584 256 = 766769386403359944264646776083 :=
  phaseBlock_append rec_2_15_2368_1_part28 rec_2_15_2368_1_part29 rfl rfl rfl
private theorem rec_2_15_2368_1_join26 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3968 191 = 118231984182559474447112711119 :=
  phaseBlock_append rec_2_15_2368_1_part31 rec_2_15_2368_1_part32 rfl rfl rfl
private theorem rec_2_15_2368_1_join27 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3840 319 = 332986179667716048073122031663 :=
  phaseBlock_append rec_2_15_2368_1_part30 rec_2_15_2368_1_join26 rfl rfl rfl
private theorem rec_2_15_2368_1_join28 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3584 575 = 1099755566071075992337768807746 :=
  phaseBlock_append rec_2_15_2368_1_join25 rec_2_15_2368_1_join27 rfl rfl rfl
private theorem rec_2_15_2368_1_join29 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 3072 1087 = 4052659531644509759170814097278 :=
  phaseBlock_append rec_2_15_2368_1_join24 rec_2_15_2368_1_join28 rfl rfl rfl
private theorem rec_2_15_2368_1_join30 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 2048 2111 = 16224390790157645684819037902605 :=
  phaseBlock_append rec_2_15_2368_1_join21 rec_2_15_2368_1_join29 rfl rfl rfl
private theorem rec_2_15_2368_1_join31 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2368 105 1 0 7 1) 0 4159 = 70766209894821613999643896012045 :=
  phaseBlock_append rec_2_15_2368_1_join14 rec_2_15_2368_1_join30 rfl rfl rfl

private theorem rec_2_15_2368_1 : fastPhase (bank 2 15).shape 179798 2368 105 1 0 7 1 = 70766209894821613999643896012045 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_2_15_2368_1_join31

private theorem rec_2_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 0 128 = 4767485987118175368429096350272 := by decide +kernel
private theorem rec_2_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 128 128 = 4571257698129188723809851216448 := by decide +kernel
private theorem rec_2_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 256 128 = 4378410725552804260526798598720 := by decide +kernel
private theorem rec_2_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 384 128 = 4188910505329845308163310146112 := by decide +kernel
private theorem rec_2_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 512 128 = 4002722636723359906082722067008 := by decide +kernel
private theorem rec_2_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 640 128 = 3819812882010635018075255771712 := by decide +kernel
private theorem rec_2_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 768 128 = 3640147166175210747004938515008 := by decide +kernel
private theorem rec_2_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 896 128 = 3463691576598894549456524038720 := by decide +kernel
private theorem rec_2_15_2369_0_part8 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1024 128 = 3290412362753775450382413214272 := by decide +kernel
private theorem rec_2_15_2369_0_part9 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1152 128 = 3120275935894238257749574685248 := by decide +kernel
private theorem rec_2_15_2369_0_part10 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1280 128 = 2953248868748977777186465509952 := by decide +kernel
private theorem rec_2_15_2369_0_part11 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1408 128 = 2789297895213013026629951803968 := by decide +kernel
private theorem rec_2_15_2369_0_part12 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1536 128 = 2628389910039701450972229382720 := by decide +kernel
private theorem rec_2_15_2369_0_part13 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1664 128 = 2470491968532753136707744404032 := by decide +kernel
private theorem rec_2_15_2369_0_part14 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1792 128 = 2315571286238245026580114010688 := by decide +kernel
private theorem rec_2_15_2369_0_part15 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1920 128 = 2163595238636635134229046972992 := by decide +kernel
private theorem rec_2_15_2369_0_part16 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2048 128 = 2014531372780899320235672339016 := by decide +kernel
private theorem rec_2_15_2369_0_part17 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2176 128 = 1868347562579005243139169074064 := by decide +kernel
private theorem rec_2_15_2369_0_part18 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2304 128 = 1725011756554199221393218561649 := by decide +kernel
private theorem rec_2_15_2369_0_part19 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2432 128 = 1584491901117555832549224393036 := by decide +kernel
private theorem rec_2_15_2369_0_part20 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2560 128 = 1446756097764528306894285891408 := by decide +kernel
private theorem rec_2_15_2369_0_part21 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2688 128 = 1311772606405002015264270015036 := by decide +kernel
private theorem rec_2_15_2369_0_part22 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2816 128 = 1179509845154728797335738213773 := by decide +kernel
private theorem rec_2_15_2369_0_part23 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2944 128 = 1049936390340476882445659833712 := by decide +kernel
private theorem rec_2_15_2369_0_part24 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3072 128 = 923020975817431216602990685369 := by decide +kernel
private theorem rec_2_15_2369_0_part25 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3200 128 = 798732492700416455628827888053 := by decide +kernel
private theorem rec_2_15_2369_0_part26 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3328 128 = 677039989256990231698292495574 := by decide +kernel
private theorem rec_2_15_2369_0_part27 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3456 128 = 557912670501068890751430688638 := by decide +kernel
private theorem rec_2_15_2369_0_part28 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3584 128 = 441319897787736614797529559621 := by decide +kernel
private theorem rec_2_15_2369_0_part29 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3712 128 = 327231188580325123957044468216 := by decide +kernel
private theorem rec_2_15_2369_0_part30 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3840 128 = 215616216227690938717262848370 := by decide +kernel
private theorem rec_2_15_2369_0_part31 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3968 128 = 106444809507074392697726192698 := by decide +kernel
private theorem rec_2_15_2369_0_part32 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 4096 63 = 13038529743860683603101299991 := by decide +kernel
private theorem rec_2_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 0 256 = 9338743685247364092238947566720 :=
  phaseBlock_append rec_2_15_2369_0_part0 rec_2_15_2369_0_part1 rfl rfl rfl
private theorem rec_2_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 256 256 = 8567321230882649568690108744832 :=
  phaseBlock_append rec_2_15_2369_0_part2 rec_2_15_2369_0_part3 rfl rfl rfl
private theorem rec_2_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 0 512 = 17906064916130013660929056311552 :=
  phaseBlock_append rec_2_15_2369_0_join0 rec_2_15_2369_0_join1 rfl rfl rfl
private theorem rec_2_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 512 256 = 7822535518733994924157977838720 :=
  phaseBlock_append rec_2_15_2369_0_part4 rec_2_15_2369_0_part5 rfl rfl rfl
private theorem rec_2_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 768 256 = 7103838742774105296461462553728 :=
  phaseBlock_append rec_2_15_2369_0_part6 rec_2_15_2369_0_part7 rfl rfl rfl
private theorem rec_2_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 512 512 = 14926374261508100220619440392448 :=
  phaseBlock_append rec_2_15_2369_0_join3 rec_2_15_2369_0_join4 rfl rfl rfl
private theorem rec_2_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 0 1024 = 32832439177638113881548496704000 :=
  phaseBlock_append rec_2_15_2369_0_join2 rec_2_15_2369_0_join5 rfl rfl rfl
private theorem rec_2_15_2369_0_join7 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1024 256 = 6410688298648013708131987899520 :=
  phaseBlock_append rec_2_15_2369_0_part8 rec_2_15_2369_0_part9 rfl rfl rfl
private theorem rec_2_15_2369_0_join8 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1280 256 = 5742546763961990803816417313920 :=
  phaseBlock_append rec_2_15_2369_0_part10 rec_2_15_2369_0_part11 rfl rfl rfl
private theorem rec_2_15_2369_0_join9 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1024 512 = 12153235062610004511948405213440 :=
  phaseBlock_append rec_2_15_2369_0_join7 rec_2_15_2369_0_join8 rfl rfl rfl
private theorem rec_2_15_2369_0_join10 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1536 256 = 5098881878572454587679973786752 :=
  phaseBlock_append rec_2_15_2369_0_part12 rec_2_15_2369_0_part13 rfl rfl rfl
private theorem rec_2_15_2369_0_join11 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1792 256 = 4479166524874880160809160983680 :=
  phaseBlock_append rec_2_15_2369_0_part14 rec_2_15_2369_0_part15 rfl rfl rfl
private theorem rec_2_15_2369_0_join12 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1536 512 = 9578048403447334748489134770432 :=
  phaseBlock_append rec_2_15_2369_0_join10 rec_2_15_2369_0_join11 rfl rfl rfl
private theorem rec_2_15_2369_0_join13 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 1024 1024 = 21731283466057339260437539983872 :=
  phaseBlock_append rec_2_15_2369_0_join9 rec_2_15_2369_0_join12 rfl rfl rfl
private theorem rec_2_15_2369_0_join14 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 0 2048 = 54563722643695453141986036687872 :=
  phaseBlock_append rec_2_15_2369_0_join6 rec_2_15_2369_0_join13 rfl rfl rfl
private theorem rec_2_15_2369_0_join15 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2048 256 = 3882878935359904563374841413080 :=
  phaseBlock_append rec_2_15_2369_0_part16 rec_2_15_2369_0_part17 rfl rfl rfl
private theorem rec_2_15_2369_0_join16 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2304 256 = 3309503657671755053942442954685 :=
  phaseBlock_append rec_2_15_2369_0_part18 rec_2_15_2369_0_part19 rfl rfl rfl
private theorem rec_2_15_2369_0_join17 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2048 512 = 7192382593031659617317284367765 :=
  phaseBlock_append rec_2_15_2369_0_join15 rec_2_15_2369_0_join16 rfl rfl rfl
private theorem rec_2_15_2369_0_join18 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2560 256 = 2758528704169530322158555906444 :=
  phaseBlock_append rec_2_15_2369_0_part20 rec_2_15_2369_0_part21 rfl rfl rfl
private theorem rec_2_15_2369_0_join19 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2816 256 = 2229446235495205679781398047485 :=
  phaseBlock_append rec_2_15_2369_0_part22 rec_2_15_2369_0_part23 rfl rfl rfl
private theorem rec_2_15_2369_0_join20 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2560 512 = 4987974939664736001939953953929 :=
  phaseBlock_append rec_2_15_2369_0_join18 rec_2_15_2369_0_join19 rfl rfl rfl
private theorem rec_2_15_2369_0_join21 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2048 1024 = 12180357532696395619257238321694 :=
  phaseBlock_append rec_2_15_2369_0_join17 rec_2_15_2369_0_join20 rfl rfl rfl
private theorem rec_2_15_2369_0_join22 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3072 256 = 1721753468517847672231818573422 :=
  phaseBlock_append rec_2_15_2369_0_part24 rec_2_15_2369_0_part25 rfl rfl rfl
private theorem rec_2_15_2369_0_join23 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3328 256 = 1234952659758059122449723184212 :=
  phaseBlock_append rec_2_15_2369_0_part26 rec_2_15_2369_0_part27 rfl rfl rfl
private theorem rec_2_15_2369_0_join24 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3072 512 = 2956706128275906794681541757634 :=
  phaseBlock_append rec_2_15_2369_0_join22 rec_2_15_2369_0_join23 rfl rfl rfl
private theorem rec_2_15_2369_0_join25 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3584 256 = 768551086368061738754574027837 :=
  phaseBlock_append rec_2_15_2369_0_part28 rec_2_15_2369_0_part29 rfl rfl rfl
private theorem rec_2_15_2369_0_join26 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3968 191 = 119483339250935076300827492689 :=
  phaseBlock_append rec_2_15_2369_0_part31 rec_2_15_2369_0_part32 rfl rfl rfl
private theorem rec_2_15_2369_0_join27 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3840 319 = 335099555478626015018090341059 :=
  phaseBlock_append rec_2_15_2369_0_part30 rec_2_15_2369_0_join26 rfl rfl rfl
private theorem rec_2_15_2369_0_join28 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3584 575 = 1103650641846687753772664368896 :=
  phaseBlock_append rec_2_15_2369_0_join25 rec_2_15_2369_0_join27 rfl rfl rfl
private theorem rec_2_15_2369_0_join29 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 3072 1087 = 4060356770122594548454206126530 :=
  phaseBlock_append rec_2_15_2369_0_join24 rec_2_15_2369_0_join28 rfl rfl rfl
private theorem rec_2_15_2369_0_join30 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 2048 2111 = 16240714302818990167711444448224 :=
  phaseBlock_append rec_2_15_2369_0_join21 rec_2_15_2369_0_join29 rfl rfl rfl
private theorem rec_2_15_2369_0_join31 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 0) 0 4159 = 70804436946514443309697481136096 :=
  phaseBlock_append rec_2_15_2369_0_join14 rec_2_15_2369_0_join30 rfl rfl rfl

private theorem rec_2_15_2369_0 : fastPhase (bank 2 15).shape 179798 2369 105 1 0 7 0 = 70804436946514443309697481136096 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_2_15_2369_0_join31

private theorem rec_2_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 0 128 = 4765960520793169854279867076032 := by decide +kernel
private theorem rec_2_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 128 128 = 4569758020639100940190325747136 := by decide +kernel
private theorem rec_2_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 256 128 = 4376936573826946786803607129536 := by decide +kernel
private theorem rec_2_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 384 128 = 4187461617544500210526149045696 := by decide +kernel
private theorem rec_2_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 512 128 = 4001298752299420460749756894656 := by decide +kernel
private theorem rec_2_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 640 128 = 3818413741611247434498524294592 := by decide +kernel
private theorem rec_2_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 768 128 = 3638772511703415891075753725376 := by decide +kernel
private theorem rec_2_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 896 128 = 3462341151195269666710877171136 := by decide +kernel
private theorem rec_2_15_2369_1_part8 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1024 128 = 3289085910794075889206376762816 := by decide +kernel
private theorem rec_2_15_2369_1_part9 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1152 128 = 3118973202987039192584705420736 := by decide +kernel
private theorem rec_2_15_2369_1_part10 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1280 128 = 2951969601733315931735207497152 := by decide +kernel
private theorem rec_2_15_2369_1_part11 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1408 128 = 2788041842156028397061039418816 := by decide +kernel
private theorem rec_2_15_2369_1_part12 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1536 128 = 2627156820234279029126090329536 := by decide +kernel
private theorem rec_2_15_2369_1_part13 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1664 128 = 2469281592495164633301902732736 := by decide +kernel
private theorem rec_2_15_2369_1_part14 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1792 128 = 2314383375705790594414593134016 := by decide +kernel
private theorem rec_2_15_2369_1_part15 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1920 128 = 2162429546565285091391772683712 := by decide +kernel
private theorem rec_2_15_2369_1_part16 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2048 128 = 2013387653336747743014764399427 := by decide +kernel
private theorem rec_2_15_2369_1_part17 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2176 128 = 1867225571044050483732756621940 := by decide +kernel
private theorem rec_2_15_2369_1_part18 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2304 128 = 1723911249346897672217455631955 := by decide +kernel
private theorem rec_2_15_2369_1_part19 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2432 128 = 1583412635865660335068637571939 := by decide +kernel
private theorem rec_2_15_2369_1_part20 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2560 128 = 1445697833304533888887725293789 := by decide +kernel
private theorem rec_2_15_2369_1_part21 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2688 128 = 1310735102779878895938386288798 := by decide +kernel
private theorem rec_2_15_2369_1_part22 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2816 128 = 1178492863611629956380304410131 := by decide +kernel
private theorem rec_2_15_2369_1_part23 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2944 128 = 1048939693328194955640392784430 := by decide +kernel
private theorem rec_2_15_2369_1_part24 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3072 128 = 922044326984107590435565455300 := by decide +kernel
private theorem rec_2_15_2369_1_part25 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3200 128 = 797775656891271869771466687048 := by decide +kernel
private theorem rec_2_15_2369_1_part26 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3328 128 = 676102732511872697805800216988 := by decide +kernel
private theorem rec_2_15_2369_1_part27 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3456 128 = 556994760052036694740577503936 := by decide +kernel
private theorem rec_2_15_2369_1_part28 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3584 128 = 440421102056783301488807679242 := by decide +kernel
private theorem rec_2_15_2369_1_part29 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3712 128 = 326351277177074284067596965098 := by decide +kernel
private theorem rec_2_15_2369_1_part30 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3840 128 = 214754959946858300478192387403 := by decide +kernel
private theorem rec_2_15_2369_1_part31 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3968 128 = 105601980326185751648966305020 := by decide +kernel
private theorem rec_2_15_2369_1_part32 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 4096 63 = 12630397273763841107583963888 := by decide +kernel
private theorem rec_2_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 0 256 = 9335718541432270794470192823168 :=
  phaseBlock_append rec_2_15_2369_1_part0 rec_2_15_2369_1_part1 rfl rfl rfl
private theorem rec_2_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 256 256 = 8564398191371446997329756175232 :=
  phaseBlock_append rec_2_15_2369_1_part2 rec_2_15_2369_1_part3 rfl rfl rfl
private theorem rec_2_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 0 512 = 17900116732803717791799948998400 :=
  phaseBlock_append rec_2_15_2369_1_join0 rec_2_15_2369_1_join1 rfl rfl rfl
private theorem rec_2_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 512 256 = 7819712493910667895248281189248 :=
  phaseBlock_append rec_2_15_2369_1_part4 rec_2_15_2369_1_part5 rfl rfl rfl
private theorem rec_2_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 768 256 = 7101113662898685557786630896512 :=
  phaseBlock_append rec_2_15_2369_1_part6 rec_2_15_2369_1_part7 rfl rfl rfl
private theorem rec_2_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 512 512 = 14920826156809353453034912085760 :=
  phaseBlock_append rec_2_15_2369_1_join3 rec_2_15_2369_1_join4 rfl rfl rfl
private theorem rec_2_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 0 1024 = 32820942889613071244834861084160 :=
  phaseBlock_append rec_2_15_2369_1_join2 rec_2_15_2369_1_join5 rfl rfl rfl
private theorem rec_2_15_2369_1_join7 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1024 256 = 6408059113781115081791082183552 :=
  phaseBlock_append rec_2_15_2369_1_part8 rec_2_15_2369_1_part9 rfl rfl rfl
private theorem rec_2_15_2369_1_join8 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1280 256 = 5740011443889344328796246915968 :=
  phaseBlock_append rec_2_15_2369_1_part10 rec_2_15_2369_1_part11 rfl rfl rfl
private theorem rec_2_15_2369_1_join9 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1024 512 = 12148070557670459410587329099520 :=
  phaseBlock_append rec_2_15_2369_1_join7 rec_2_15_2369_1_join8 rfl rfl rfl
private theorem rec_2_15_2369_1_join10 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1536 256 = 5096438412729443662427993062272 :=
  phaseBlock_append rec_2_15_2369_1_part12 rec_2_15_2369_1_part13 rfl rfl rfl
private theorem rec_2_15_2369_1_join11 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1792 256 = 4476812922271075685806365817728 :=
  phaseBlock_append rec_2_15_2369_1_part14 rec_2_15_2369_1_part15 rfl rfl rfl
private theorem rec_2_15_2369_1_join12 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1536 512 = 9573251335000519348234358880000 :=
  phaseBlock_append rec_2_15_2369_1_join10 rec_2_15_2369_1_join11 rfl rfl rfl
private theorem rec_2_15_2369_1_join13 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 1024 1024 = 21721321892670978758821687979520 :=
  phaseBlock_append rec_2_15_2369_1_join9 rec_2_15_2369_1_join12 rfl rfl rfl
private theorem rec_2_15_2369_1_join14 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 0 2048 = 54542264782284050003656549063680 :=
  phaseBlock_append rec_2_15_2369_1_join6 rec_2_15_2369_1_join13 rfl rfl rfl
private theorem rec_2_15_2369_1_join15 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2048 256 = 3880613224380798226747521021367 :=
  phaseBlock_append rec_2_15_2369_1_part16 rec_2_15_2369_1_part17 rfl rfl rfl
private theorem rec_2_15_2369_1_join16 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2304 256 = 3307323885212558007286093203894 :=
  phaseBlock_append rec_2_15_2369_1_part18 rec_2_15_2369_1_part19 rfl rfl rfl
private theorem rec_2_15_2369_1_join17 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2048 512 = 7187937109593356234033614225261 :=
  phaseBlock_append rec_2_15_2369_1_join15 rec_2_15_2369_1_join16 rfl rfl rfl
private theorem rec_2_15_2369_1_join18 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2560 256 = 2756432936084412784826111582587 :=
  phaseBlock_append rec_2_15_2369_1_part20 rec_2_15_2369_1_part21 rfl rfl rfl
private theorem rec_2_15_2369_1_join19 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2816 256 = 2227432556939824912020697194561 :=
  phaseBlock_append rec_2_15_2369_1_part22 rec_2_15_2369_1_part23 rfl rfl rfl
private theorem rec_2_15_2369_1_join20 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2560 512 = 4983865493024237696846808777148 :=
  phaseBlock_append rec_2_15_2369_1_join18 rec_2_15_2369_1_join19 rfl rfl rfl
private theorem rec_2_15_2369_1_join21 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2048 1024 = 12171802602617593930880423002409 :=
  phaseBlock_append rec_2_15_2369_1_join17 rec_2_15_2369_1_join20 rfl rfl rfl
private theorem rec_2_15_2369_1_join22 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3072 256 = 1719819983875379460207032142348 :=
  phaseBlock_append rec_2_15_2369_1_part24 rec_2_15_2369_1_part25 rfl rfl rfl
private theorem rec_2_15_2369_1_join23 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3328 256 = 1233097492563909392546377720924 :=
  phaseBlock_append rec_2_15_2369_1_part26 rec_2_15_2369_1_part27 rfl rfl rfl
private theorem rec_2_15_2369_1_join24 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3072 512 = 2952917476439288852753409863272 :=
  phaseBlock_append rec_2_15_2369_1_join22 rec_2_15_2369_1_join23 rfl rfl rfl
private theorem rec_2_15_2369_1_join25 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3584 256 = 766772379233857585556404644340 :=
  phaseBlock_append rec_2_15_2369_1_part28 rec_2_15_2369_1_part29 rfl rfl rfl
private theorem rec_2_15_2369_1_join26 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3968 191 = 118232377599949592756550268908 :=
  phaseBlock_append rec_2_15_2369_1_part31 rec_2_15_2369_1_part32 rfl rfl rfl
private theorem rec_2_15_2369_1_join27 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3840 319 = 332987337546807893234742656311 :=
  phaseBlock_append rec_2_15_2369_1_part30 rec_2_15_2369_1_join26 rfl rfl rfl
private theorem rec_2_15_2369_1_join28 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3584 575 = 1099759716780665478791147300651 :=
  phaseBlock_append rec_2_15_2369_1_join25 rec_2_15_2369_1_join27 rfl rfl rfl
private theorem rec_2_15_2369_1_join29 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 3072 1087 = 4052677193219954331544557163923 :=
  phaseBlock_append rec_2_15_2369_1_join24 rec_2_15_2369_1_join28 rfl rfl rfl
private theorem rec_2_15_2369_1_join30 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 2048 2111 = 16224479795837548262424980166332 :=
  phaseBlock_append rec_2_15_2369_1_join21 rec_2_15_2369_1_join29 rfl rfl rfl
private theorem rec_2_15_2369_1_join31 :
    phaseBlock (fastLayerG (bank 2 15).shape 179798 2369 105 1 0 7 1) 0 4159 = 70766744578121598266081529230012 :=
  phaseBlock_append rec_2_15_2369_1_join14 rec_2_15_2369_1_join30 rfl rfl rfl

private theorem rec_2_15_2369_1 : fastPhase (bank 2 15).shape 179798 2369 105 1 0 7 1 = 70766744578121598266081529230012 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_2_15_2369_1_join31

theorem receipt_2_15 : Checked (bank 2 15) 105 0 7 := by
  refine checked_from_values (bank 2 15) 105 0 7
    (P3_7_1.checked (bank 2 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_18778_4158)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_15_2368_0 rec_2_15_2368_1 rec_2_15_2369_0 rec_2_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_2_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 0 128 = 15971547483912542889881319687840 := by decide +kernel
private theorem rec_2_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 128 128 = 15436164363202170489281326306976 := by decide +kernel
private theorem rec_2_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 256 128 = 14908211490771117550394346038944 := by decide +kernel
private theorem rec_2_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 384 128 = 14387628409962512145108423964320 := by decide +kernel
private theorem rec_2_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 512 128 = 13874354881788581942106459276960 := by decide +kernel
private theorem rec_2_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 640 128 = 13368330884622679196727078131360 := by decide +kernel
private theorem rec_2_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 768 128 = 12869496613891305740825506490016 := by decide +kernel
private theorem rec_2_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 896 128 = 12377792481766137972634442970784 := by decide +kernel
private theorem rec_2_16_2368_0_part8 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1024 128 = 11893159116856051846624931694240 := by decide +kernel
private theorem rec_2_16_2368_0_part9 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1152 128 = 11415537363899147863367235131040 := by decide +kernel
private theorem rec_2_16_2368_0_part10 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1280 128 = 10944868283454776059391706949280 := by decide +kernel
private theorem rec_2_16_2368_0_part11 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1408 128 = 10481093151595560997049664861856 := by decide +kernel
private theorem rec_2_16_2368_0_part12 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1536 128 = 10024153459599426754374263473824 := by decide +kernel
private theorem rec_2_16_2368_0_part13 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1664 128 = 9573990913641621914941367129760 := by decide +kernel
private theorem rec_2_16_2368_0_part14 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1792 128 = 9130547434486744557730422761120 := by decide +kernel
private theorem rec_2_16_2368_0_part15 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1920 128 = 8693765157180767246985332733600 := by decide +kernel
private theorem rec_2_16_2368_0_part16 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2048 128 = 8263586430743062022075327694496 := by decide +kernel
private theorem rec_2_16_2368_0_part17 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2176 128 = 7839953817858425387355839420064 := by decide +kernel
private theorem rec_2_16_2368_0_part18 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2304 128 = 7422810094569103302029373662880 := by decide +kernel
private theorem rec_2_16_2368_0_part19 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2432 128 = 7012098249966816170006382999200 := by decide +kernel
private theorem rec_2_16_2368_0_part20 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2560 128 = 6607761638004483616025028138847 := by decide +kernel
private theorem rec_2_16_2368_0_part21 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2688 128 = 6209744156251983406777297528452 := by decide +kernel
private theorem rec_2_16_2368_0_part22 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2816 128 = 5817989423220827434488365874408 := by decide +kernel
private theorem rec_2_16_2368_0_part23 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2944 128 = 5432441149402813325804891471528 := by decide +kernel
private theorem rec_2_16_2368_0_part24 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3072 128 = 5053043258199339727830962558382 := by decide +kernel
private theorem rec_2_16_2368_0_part25 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3200 128 = 4679739884585413697036098409011 := by decide +kernel
private theorem rec_2_16_2368_0_part26 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3328 128 = 4312475374798446192320374160910 := by decide +kernel
private theorem rec_2_16_2368_0_part27 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3456 128 = 3951194286603848530811264486871 := by decide +kernel
private theorem rec_2_16_2368_0_part28 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3584 128 = 3595841388901869605414141020082 := by decide +kernel
private theorem rec_2_16_2368_0_part29 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3712 128 = 3246361660932101917988444407270 := by decide +kernel
private theorem rec_2_16_2368_0_part30 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3840 128 = 2902700292159163430996371015650 := by decide +kernel
private theorem rec_2_16_2368_0_part31 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3968 128 = 2564802682488443990294772340641 := by decide +kernel
private theorem rec_2_16_2368_0_part32 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4096 128 = 2232614441302505855107087419698 := by decide +kernel
private theorem rec_2_16_2368_0_part33 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4224 128 = 1906081387240755018668098896465 := by decide +kernel
private theorem rec_2_16_2368_0_part34 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4352 128 = 1585149548256299637406765864873 := by decide +kernel
private theorem rec_2_16_2368_0_part35 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4480 128 = 1269765161077520418629630051061 := by decide +kernel
private theorem rec_2_16_2368_0_part36 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4608 128 = 959874670785166086358562360304 := by decide +kernel
private theorem rec_2_16_2368_0_part37 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4736 128 = 655424730646441563031190944796 := by decide +kernel
private theorem rec_2_16_2368_0_part38 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4864 128 = 356362201895275389241756881532 := by decide +kernel
private theorem rec_2_16_2368_0_part39 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4992 91 = 74399803611106972662706488306 := by decide +kernel
private theorem rec_2_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 0 256 = 31407711847114713379162645994816 :=
  phaseBlock_append rec_2_16_2368_0_part0 rec_2_16_2368_0_part1 rfl rfl rfl
private theorem rec_2_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 384 256 = 28261983291751094087214883241280 :=
  phaseBlock_append rec_2_16_2368_0_part3 rec_2_16_2368_0_part4 rfl rfl rfl
private theorem rec_2_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 256 384 = 43170194782522211637609229280224 :=
  phaseBlock_append rec_2_16_2368_0_part2 rec_2_16_2368_0_join1 rfl rfl rfl
private theorem rec_2_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 0 640 = 74577906629636925016771875275040 :=
  phaseBlock_append rec_2_16_2368_0_join0 rec_2_16_2368_0_join2 rfl rfl rfl
private theorem rec_2_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 640 256 = 26237827498513984937552584621376 :=
  phaseBlock_append rec_2_16_2368_0_part5 rec_2_16_2368_0_part6 rfl rfl rfl
private theorem rec_2_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1024 256 = 23308696480755199709992166825280 :=
  phaseBlock_append rec_2_16_2368_0_part8 rec_2_16_2368_0_part9 rfl rfl rfl
private theorem rec_2_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 896 384 = 35686488962521337682626609796064 :=
  phaseBlock_append rec_2_16_2368_0_part7 rec_2_16_2368_0_join5 rfl rfl rfl
private theorem rec_2_16_2368_0_join7 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 640 640 = 61924316461035322620179194417440 :=
  phaseBlock_append rec_2_16_2368_0_join4 rec_2_16_2368_0_join6 rfl rfl rfl
private theorem rec_2_16_2368_0_join8 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 0 1280 = 136502223090672247636951069692480 :=
  phaseBlock_append rec_2_16_2368_0_join3 rec_2_16_2368_0_join7 rfl rfl rfl
private theorem rec_2_16_2368_0_join9 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1280 256 = 21425961435050337056441371811136 :=
  phaseBlock_append rec_2_16_2368_0_part10 rec_2_16_2368_0_part11 rfl rfl rfl
private theorem rec_2_16_2368_0_join10 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1664 256 = 18704538348128366472671789890880 :=
  phaseBlock_append rec_2_16_2368_0_part13 rec_2_16_2368_0_part14 rfl rfl rfl
private theorem rec_2_16_2368_0_join11 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1536 384 = 28728691807727793227046053364704 :=
  phaseBlock_append rec_2_16_2368_0_part12 rec_2_16_2368_0_join10 rfl rfl rfl
private theorem rec_2_16_2368_0_join12 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1280 640 = 50154653242778130283487425175840 :=
  phaseBlock_append rec_2_16_2368_0_join9 rec_2_16_2368_0_join11 rfl rfl rfl
private theorem rec_2_16_2368_0_join13 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1920 256 = 16957351587923829269060660428096 :=
  phaseBlock_append rec_2_16_2368_0_part15 rec_2_16_2368_0_part16 rfl rfl rfl
private theorem rec_2_16_2368_0_join14 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2304 256 = 14434908344535919472035756662080 :=
  phaseBlock_append rec_2_16_2368_0_part18 rec_2_16_2368_0_part19 rfl rfl rfl
private theorem rec_2_16_2368_0_join15 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2176 384 = 22274862162394344859391596082144 :=
  phaseBlock_append rec_2_16_2368_0_part17 rec_2_16_2368_0_join14 rfl rfl rfl
private theorem rec_2_16_2368_0_join16 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1920 640 = 39232213750318174128452256510240 :=
  phaseBlock_append rec_2_16_2368_0_join13 rec_2_16_2368_0_join15 rfl rfl rfl
private theorem rec_2_16_2368_0_join17 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 1280 1280 = 89386866993096304411939681686080 :=
  phaseBlock_append rec_2_16_2368_0_join12 rec_2_16_2368_0_join16 rfl rfl rfl
private theorem rec_2_16_2368_0_join18 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 0 2560 = 225889090083768552048890751378560 :=
  phaseBlock_append rec_2_16_2368_0_join8 rec_2_16_2368_0_join17 rfl rfl rfl
private theorem rec_2_16_2368_0_join19 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2560 256 = 12817505794256467022802325667299 :=
  phaseBlock_append rec_2_16_2368_0_part20 rec_2_16_2368_0_part21 rfl rfl rfl
private theorem rec_2_16_2368_0_join20 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2944 256 = 10485484407602153053635854029910 :=
  phaseBlock_append rec_2_16_2368_0_part23 rec_2_16_2368_0_part24 rfl rfl rfl
private theorem rec_2_16_2368_0_join21 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2816 384 = 16303473830822980488124219904318 :=
  phaseBlock_append rec_2_16_2368_0_part22 rec_2_16_2368_0_join20 rfl rfl rfl
private theorem rec_2_16_2368_0_join22 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2560 640 = 29120979625079447510926545571617 :=
  phaseBlock_append rec_2_16_2368_0_join19 rec_2_16_2368_0_join21 rfl rfl rfl
private theorem rec_2_16_2368_0_join23 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3200 256 = 8992215259383859889356472569921 :=
  phaseBlock_append rec_2_16_2368_0_part25 rec_2_16_2368_0_part26 rfl rfl rfl
private theorem rec_2_16_2368_0_join24 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3584 256 = 6842203049833971523402585427352 :=
  phaseBlock_append rec_2_16_2368_0_part28 rec_2_16_2368_0_part29 rfl rfl rfl
private theorem rec_2_16_2368_0_join25 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3456 384 = 10793397336437820054213849914223 :=
  phaseBlock_append rec_2_16_2368_0_part27 rec_2_16_2368_0_join24 rfl rfl rfl
private theorem rec_2_16_2368_0_join26 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3200 640 = 19785612595821679943570322484144 :=
  phaseBlock_append rec_2_16_2368_0_join23 rec_2_16_2368_0_join25 rfl rfl rfl
private theorem rec_2_16_2368_0_join27 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2560 1280 = 48906592220901127454496868055761 :=
  phaseBlock_append rec_2_16_2368_0_join22 rec_2_16_2368_0_join26 rfl rfl rfl
private theorem rec_2_16_2368_0_join28 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3840 256 = 5467502974647607421291143356291 :=
  phaseBlock_append rec_2_16_2368_0_part30 rec_2_16_2368_0_part31 rfl rfl rfl
private theorem rec_2_16_2368_0_join29 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4224 256 = 3491230935497054656074864761338 :=
  phaseBlock_append rec_2_16_2368_0_part33 rec_2_16_2368_0_part34 rfl rfl rfl
private theorem rec_2_16_2368_0_join30 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4096 384 = 5723845376799560511181952181036 :=
  phaseBlock_append rec_2_16_2368_0_part32 rec_2_16_2368_0_join29 rfl rfl rfl
private theorem rec_2_16_2368_0_join31 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3840 640 = 11191348351447167932473095537327 :=
  phaseBlock_append rec_2_16_2368_0_join28 rec_2_16_2368_0_join30 rfl rfl rfl
private theorem rec_2_16_2368_0_join32 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4480 256 = 2229639831862686504988192411365 :=
  phaseBlock_append rec_2_16_2368_0_part35 rec_2_16_2368_0_part36 rfl rfl rfl
private theorem rec_2_16_2368_0_join33 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4864 219 = 430762005506382361904463369838 :=
  phaseBlock_append rec_2_16_2368_0_part38 rec_2_16_2368_0_part39 rfl rfl rfl
private theorem rec_2_16_2368_0_join34 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4736 347 = 1086186736152823924935654314634 :=
  phaseBlock_append rec_2_16_2368_0_part37 rec_2_16_2368_0_join33 rfl rfl rfl
private theorem rec_2_16_2368_0_join35 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 4480 603 = 3315826568015510429923846725999 :=
  phaseBlock_append rec_2_16_2368_0_join32 rec_2_16_2368_0_join34 rfl rfl rfl
private theorem rec_2_16_2368_0_join36 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 3840 1243 = 14507174919462678362396942263326 :=
  phaseBlock_append rec_2_16_2368_0_join31 rec_2_16_2368_0_join35 rfl rfl rfl
private theorem rec_2_16_2368_0_join37 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 2560 2523 = 63413767140363805816893810319087 :=
  phaseBlock_append rec_2_16_2368_0_join27 rec_2_16_2368_0_join36 rfl rfl rfl
private theorem rec_2_16_2368_0_join38 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 0) 0 5083 = 289302857224132357865784561697647 :=
  phaseBlock_append rec_2_16_2368_0_join18 rec_2_16_2368_0_join37 rfl rfl rfl

private theorem rec_2_16_2368_0 : fastPhase (bank 2 16).shape 179798 2368 138 1 0 7 0 = 289302857224132357865784561697647 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_2_16_2368_0_join38

private theorem rec_2_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 0 128 = 15967392715128605655075633641760 := by decide +kernel
private theorem rec_2_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 128 128 = 15432066180634707509822104283424 := by decide +kernel
private theorem rec_2_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 256 128 = 14904169434687840219481514842400 := by decide +kernel
private theorem rec_2_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 384 128 = 14383642022292500281856349178144 := by decide +kernel
private theorem rec_2_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 512 128 = 13870423706119925578727181121824 := by decide +kernel
private theorem rec_2_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 640 128 = 13364454466200120365713547323680 := by decide +kernel
private theorem rec_2_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 768 128 = 12865674499613880262134820100384 := by decide +kernel
private theorem rec_2_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 896 128 = 12374024220184817240871080282400 := by decide +kernel
private theorem rec_2_16_2368_1_part8 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1024 128 = 11889444258171384618223990061344 := by decide +kernel
private theorem rec_2_16_2368_1_part9 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1152 128 = 11411875459958902043777665837344 := by decide +kernel
private theorem rec_2_16_2368_1_part10 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1280 128 = 10941258887751580490259551066400 := by decide +kernel
private theorem rec_2_16_2368_1_part11 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1408 128 = 10477535819264547243401289107744 := by decide +kernel
private theorem rec_2_16_2368_1_part12 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1536 128 = 10020647747415870891799596071200 := by decide +kernel
private theorem rec_2_16_2368_1_part13 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1664 128 = 9570536380018586316777133664544 := by decide +kernel
private theorem rec_2_16_2368_1_part14 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1792 128 = 9127143639472719682243382040864 := by decide +kernel
private theorem rec_2_16_2368_1_part15 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1920 128 = 8690411662457313424555512645920 := by decide +kernel
private theorem rec_2_16_2368_1_part16 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2048 128 = 8260282799622451242379261065504 := by decide +kernel
private theorem rec_2_16_2368_1_part17 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2176 128 = 7836699615281283086549799872800 := by decide +kernel
private theorem rec_2_16_2368_1_part18 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2304 128 = 7419604887102050149932611475744 := by decide +kernel
private theorem rec_2_16_2368_1_part19 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2432 128 = 7008941605800109857284360964384 := by decide +kernel
private theorem rec_2_16_2368_1_part20 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2560 128 = 6604653126885072810754400815632 := by decide +kernel
private theorem rec_2_16_2368_1_part21 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2688 128 = 6206683349323347092507186544523 := by decide +kernel
private theorem rec_2_16_2368_1_part22 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2816 128 = 5814975893198857408387842536611 := by decide +kernel
private theorem rec_2_16_2368_1_part23 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2944 128 = 5429474470620415666051055473935 := by decide +kernel
private theorem rec_2_16_2368_1_part24 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3072 128 = 5050123006603740703528059007888 := by decide +kernel
private theorem rec_2_16_2368_1_part25 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3200 128 = 4676865637735902864926981631099 := by decide +kernel
private theorem rec_2_16_2368_1_part26 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3328 128 = 4309646711864185633918063309572 := by decide +kernel
private theorem rec_2_16_2368_1_part27 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3456 128 = 3948410788361398725758762683012 := by decide +kernel
private theorem rec_2_16_2368_1_part28 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3584 128 = 3593102637732669422649006644611 := by decide +kernel
private theorem rec_2_16_2368_1_part29 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3712 128 = 3243667240820284098978752787017 := by decide +kernel
private theorem rec_2_16_2368_1_part30 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3840 128 = 2900049788689313903038335874116 := by decide +kernel
private theorem rec_2_16_2368_1_part31 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3968 128 = 2562195682842907925004664044404 := by decide +kernel
private theorem rec_2_16_2368_1_part32 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4096 128 = 2230050534259166627785062725523 := by decide +kernel
private theorem rec_2_16_2368_1_part33 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4224 128 = 1903560163170850912570601617866 := by decide +kernel
private theorem rec_2_16_2368_1_part34 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4352 128 = 1582670599121860941224195342679 := by decide +kernel
private theorem rec_2_16_2368_1_part35 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4480 128 = 1267328080428945383767957513524 := by decide +kernel
private theorem rec_2_16_2368_1_part36 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4608 128 = 957479053759020666049585059882 := by decide +kernel
private theorem rec_2_16_2368_1_part37 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4736 128 = 653070173963172385151794825721 := by decide +kernel
private theorem rec_2_16_2368_1_part38 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4864 128 = 354048303856539975462733951620 := by decide +kernel
private theorem rec_2_16_2368_1_part39 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4992 91 = 72779274732663250404527571060 := by decide +kernel
private theorem rec_2_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 0 256 = 31399458895763313164897737925184 :=
  phaseBlock_append rec_2_16_2368_1_part0 rec_2_16_2368_1_part1 rfl rfl rfl
private theorem rec_2_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 384 256 = 28254065728412425860583530299968 :=
  phaseBlock_append rec_2_16_2368_1_part3 rec_2_16_2368_1_part4 rfl rfl rfl
private theorem rec_2_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 256 384 = 43158235163100266080065045142368 :=
  phaseBlock_append rec_2_16_2368_1_part2 rec_2_16_2368_1_join1 rfl rfl rfl
private theorem rec_2_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 0 640 = 74557694058863579244962783067552 :=
  phaseBlock_append rec_2_16_2368_1_join0 rec_2_16_2368_1_join2 rfl rfl rfl
private theorem rec_2_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 640 256 = 26230128965814000627848367424064 :=
  phaseBlock_append rec_2_16_2368_1_part5 rec_2_16_2368_1_part6 rfl rfl rfl
private theorem rec_2_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1024 256 = 23301319718130286662001655898688 :=
  phaseBlock_append rec_2_16_2368_1_part8 rec_2_16_2368_1_part9 rfl rfl rfl
private theorem rec_2_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 896 384 = 35675343938315103902872736181088 :=
  phaseBlock_append rec_2_16_2368_1_part7 rec_2_16_2368_1_join5 rfl rfl rfl
private theorem rec_2_16_2368_1_join7 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 640 640 = 61905472904129104530721103605152 :=
  phaseBlock_append rec_2_16_2368_1_join4 rec_2_16_2368_1_join6 rfl rfl rfl
private theorem rec_2_16_2368_1_join8 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 0 1280 = 136463166962992683775683886672704 :=
  phaseBlock_append rec_2_16_2368_1_join3 rec_2_16_2368_1_join7 rfl rfl rfl
private theorem rec_2_16_2368_1_join9 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1280 256 = 21418794707016127733660840174144 :=
  phaseBlock_append rec_2_16_2368_1_part10 rec_2_16_2368_1_part11 rfl rfl rfl
private theorem rec_2_16_2368_1_join10 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1664 256 = 18697680019491305999020515705408 :=
  phaseBlock_append rec_2_16_2368_1_part13 rec_2_16_2368_1_part14 rfl rfl rfl
private theorem rec_2_16_2368_1_join11 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1536 384 = 28718327766907176890820111776608 :=
  phaseBlock_append rec_2_16_2368_1_part12 rec_2_16_2368_1_join10 rfl rfl rfl
private theorem rec_2_16_2368_1_join12 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1280 640 = 50137122473923304624480951950752 :=
  phaseBlock_append rec_2_16_2368_1_join9 rec_2_16_2368_1_join11 rfl rfl rfl
private theorem rec_2_16_2368_1_join13 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1920 256 = 16950694462079764666934773711424 :=
  phaseBlock_append rec_2_16_2368_1_part15 rec_2_16_2368_1_part16 rfl rfl rfl
private theorem rec_2_16_2368_1_join14 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2304 256 = 14428546492902160007216972440128 :=
  phaseBlock_append rec_2_16_2368_1_part18 rec_2_16_2368_1_part19 rfl rfl rfl
private theorem rec_2_16_2368_1_join15 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2176 384 = 22265246108183443093766772312928 :=
  phaseBlock_append rec_2_16_2368_1_part17 rec_2_16_2368_1_join14 rfl rfl rfl
private theorem rec_2_16_2368_1_join16 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1920 640 = 39215940570263207760701546024352 :=
  phaseBlock_append rec_2_16_2368_1_join13 rec_2_16_2368_1_join15 rfl rfl rfl
private theorem rec_2_16_2368_1_join17 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 1280 1280 = 89353063044186512385182497975104 :=
  phaseBlock_append rec_2_16_2368_1_join12 rec_2_16_2368_1_join16 rfl rfl rfl
private theorem rec_2_16_2368_1_join18 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 0 2560 = 225816230007179196160866384647808 :=
  phaseBlock_append rec_2_16_2368_1_join8 rec_2_16_2368_1_join17 rfl rfl rfl
private theorem rec_2_16_2368_1_join19 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2560 256 = 12811336476208419903261587360155 :=
  phaseBlock_append rec_2_16_2368_1_part20 rec_2_16_2368_1_part21 rfl rfl rfl
private theorem rec_2_16_2368_1_join20 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2944 256 = 10479597477224156369579114481823 :=
  phaseBlock_append rec_2_16_2368_1_part23 rec_2_16_2368_1_part24 rfl rfl rfl
private theorem rec_2_16_2368_1_join21 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2816 384 = 16294573370423013777966957018434 :=
  phaseBlock_append rec_2_16_2368_1_part22 rec_2_16_2368_1_join20 rfl rfl rfl
private theorem rec_2_16_2368_1_join22 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2560 640 = 29105909846631433681228544378589 :=
  phaseBlock_append rec_2_16_2368_1_join19 rec_2_16_2368_1_join21 rfl rfl rfl
private theorem rec_2_16_2368_1_join23 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3200 256 = 8986512349600088498845044940671 :=
  phaseBlock_append rec_2_16_2368_1_part25 rec_2_16_2368_1_part26 rfl rfl rfl
private theorem rec_2_16_2368_1_join24 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3584 256 = 6836769878552953521627759431628 :=
  phaseBlock_append rec_2_16_2368_1_part28 rec_2_16_2368_1_part29 rfl rfl rfl
private theorem rec_2_16_2368_1_join25 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3456 384 = 10785180666914352247386522114640 :=
  phaseBlock_append rec_2_16_2368_1_part27 rec_2_16_2368_1_join24 rfl rfl rfl
private theorem rec_2_16_2368_1_join26 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3200 640 = 19771693016514440746231567055311 :=
  phaseBlock_append rec_2_16_2368_1_join23 rec_2_16_2368_1_join25 rfl rfl rfl
private theorem rec_2_16_2368_1_join27 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2560 1280 = 48877602863145874427460111433900 :=
  phaseBlock_append rec_2_16_2368_1_join22 rec_2_16_2368_1_join26 rfl rfl rfl
private theorem rec_2_16_2368_1_join28 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3840 256 = 5462245471532221828042999918520 :=
  phaseBlock_append rec_2_16_2368_1_part30 rec_2_16_2368_1_part31 rfl rfl rfl
private theorem rec_2_16_2368_1_join29 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4224 256 = 3486230762292711853794796960545 :=
  phaseBlock_append rec_2_16_2368_1_part33 rec_2_16_2368_1_part34 rfl rfl rfl
private theorem rec_2_16_2368_1_join30 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4096 384 = 5716281296551878481579859686068 :=
  phaseBlock_append rec_2_16_2368_1_part32 rec_2_16_2368_1_join29 rfl rfl rfl
private theorem rec_2_16_2368_1_join31 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3840 640 = 11178526768084100309622859604588 :=
  phaseBlock_append rec_2_16_2368_1_join28 rec_2_16_2368_1_join30 rfl rfl rfl
private theorem rec_2_16_2368_1_join32 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4480 256 = 2224807134187966049817542573406 :=
  phaseBlock_append rec_2_16_2368_1_part35 rec_2_16_2368_1_part36 rfl rfl rfl
private theorem rec_2_16_2368_1_join33 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4864 219 = 426827578589203225867261522680 :=
  phaseBlock_append rec_2_16_2368_1_part38 rec_2_16_2368_1_part39 rfl rfl rfl
private theorem rec_2_16_2368_1_join34 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4736 347 = 1079897752552375611019056348401 :=
  phaseBlock_append rec_2_16_2368_1_part37 rec_2_16_2368_1_join33 rfl rfl rfl
private theorem rec_2_16_2368_1_join35 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 4480 603 = 3304704886740341660836598921807 :=
  phaseBlock_append rec_2_16_2368_1_join32 rec_2_16_2368_1_join34 rfl rfl rfl
private theorem rec_2_16_2368_1_join36 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 3840 1243 = 14483231654824441970459458526395 :=
  phaseBlock_append rec_2_16_2368_1_join31 rec_2_16_2368_1_join35 rfl rfl rfl
private theorem rec_2_16_2368_1_join37 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 2560 2523 = 63360834517970316397919569960295 :=
  phaseBlock_append rec_2_16_2368_1_join27 rec_2_16_2368_1_join36 rfl rfl rfl
private theorem rec_2_16_2368_1_join38 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2368 138 1 0 7 1) 0 5083 = 289177064525149512558785954608103 :=
  phaseBlock_append rec_2_16_2368_1_join18 rec_2_16_2368_1_join37 rfl rfl rfl

private theorem rec_2_16_2368_1 : fastPhase (bank 2 16).shape 179798 2368 138 1 0 7 1 = 289177064525149512558785954608103 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_2_16_2368_1_join38

private theorem rec_2_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 0 128 = 15971695300573524210530241840192 := by decide +kernel
private theorem rec_2_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 128 128 = 15436305186847358397232468223040 := by decide +kernel
private theorem rec_2_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 256 128 = 14908345513289984668343395632192 := by decide +kernel
private theorem rec_2_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 384 128 = 14387755821310055517027072877632 := by decide +kernel
private theorem rec_2_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 512 128 = 13874475869992738167732030473280 := by decide +kernel
private theorem rec_2_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 640 128 = 13368445635791728790838201279552 := by decide +kernel
private theorem rec_2_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 768 128 = 12869605312221266717303841145920 := by decide +kernel
private theorem rec_2_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 896 128 = 12377895309548148653312449553472 := by decide +kernel
private theorem rec_2_16_2369_0_part8 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1024 128 = 11893256254483742894919690257472 := by decide +kernel
private theorem rec_2_16_2369_0_part9 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1152 128 = 11415628989876003542700311929920 := by decide +kernel
private theorem rec_2_16_2369_0_part10 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1280 128 = 10944954574401484716395068802112 := by decide +kernel
private theorem rec_2_16_2369_0_part11 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1408 128 = 10481174282257354769557641307200 := by decide +kernel
private theorem rec_2_16_2369_0_part12 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1536 128 = 10024229602853410504201556722752 := by decide +kernel
private theorem rec_2_16_2369_0_part13 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1664 128 = 9574062240504091385447109813312 := by decide +kernel
private theorem rec_2_16_2369_0_part14 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1792 128 = 9130614114120493756168283472960 := by decide +kernel
private theorem rec_2_16_2369_0_part15 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1920 128 = 8693827356902385051639669367872 := by decide +kernel
private theorem rec_2_16_2369_0_part16 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2048 128 = 8263644316030218014183388578880 := by decide +kernel
private theorem rec_2_16_2369_0_part17 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2176 128 = 7840007552357144907816012244032 := by decide +kernel
private theorem rec_2_16_2369_0_part18 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2304 128 = 7422859840101031732895482201152 := by decide +kernel
private theorem rec_2_16_2369_0_part19 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2432 128 = 7012144166536472440768031630400 := by decide +kernel
private theorem rec_2_16_2369_0_part20 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2560 128 = 6607803871526101110430702810203 := by decide +kernel
private theorem rec_2_16_2369_0_part21 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2688 128 = 6209782854779993300781007278723 := by decide +kernel
private theorem rec_2_16_2369_0_part22 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2816 128 = 5818024744175911782867494566172 := by decide +kernel
private theorem rec_2_16_2369_0_part23 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2944 128 = 5432473248583359920221301068187 := by decide +kernel
private theorem rec_2_16_2369_0_part24 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3072 128 = 5053072289478860880523666407612 := by decide +kernel
private theorem rec_2_16_2369_0_part25 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3200 128 = 4679765999815899334565694730602 := by decide +kernel
private theorem rec_2_16_2369_0_part26 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3328 128 = 4312498723895804732930422340376 := by decide +kernel
private theorem rec_2_16_2369_0_part27 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3456 128 = 3951215017872544184676057993898 := by decide +kernel
private theorem rec_2_16_2369_0_part28 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3584 128 = 3595859648609179597720529884562 := by decide +kernel
private theorem rec_2_16_2369_0_part29 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3712 128 = 3246377593389857582023248691454 := by decide +kernel
private theorem rec_2_16_2369_0_part30 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3840 128 = 2902714040015898497281304192998 := by decide +kernel
private theorem rec_2_16_2369_0_part31 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3968 128 = 2564814386491352686819228470867 := by decide +kernel
private theorem rec_2_16_2369_0_part32 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4096 128 = 2232624240302140868969132812626 := by decide +kernel
private theorem rec_2_16_2369_0_part33 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4224 128 = 1906089418268381554087914258378 := by decide +kernel
private theorem rec_2_16_2369_0_part34 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4352 128 = 1585155946606122197940244097262 := by decide +kernel
private theorem rec_2_16_2369_0_part35 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4480 128 = 1269770060160963388903903151586 := by decide +kernel
private theorem rec_2_16_2369_0_part36 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4608 128 = 959878202182641497881514387565 := by decide +kernel
private theorem rec_2_16_2369_0_part37 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4736 128 = 655427024210244884447176277076 := by decide +kernel
private theorem rec_2_16_2369_0_part38 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4864 128 = 356363385649178420172366967680 := by decide +kernel
private theorem rec_2_16_2369_0_part39 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4992 91 = 74400039663432118180072886736 := by decide +kernel
private theorem rec_2_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 0 256 = 31408000487420882607762710063232 :=
  phaseBlock_append rec_2_16_2369_0_part0 rec_2_16_2369_0_part1 rfl rfl rfl
private theorem rec_2_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 384 256 = 28262231691302793684759103350912 :=
  phaseBlock_append rec_2_16_2369_0_part3 rec_2_16_2369_0_part4 rfl rfl rfl
private theorem rec_2_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 256 384 = 43170577204592778353102498983104 :=
  phaseBlock_append rec_2_16_2369_0_part2 rec_2_16_2369_0_join1 rfl rfl rfl
private theorem rec_2_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 0 640 = 74578577692013660960865209046336 :=
  phaseBlock_append rec_2_16_2369_0_join0 rec_2_16_2369_0_join2 rfl rfl rfl
private theorem rec_2_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 640 256 = 26238050948012995508142042425472 :=
  phaseBlock_append rec_2_16_2369_0_part5 rec_2_16_2369_0_part6 rfl rfl rfl
private theorem rec_2_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1024 256 = 23308885244359746437620002187392 :=
  phaseBlock_append rec_2_16_2369_0_part8 rec_2_16_2369_0_part9 rfl rfl rfl
private theorem rec_2_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 896 384 = 35686780553907895090932451740864 :=
  phaseBlock_append rec_2_16_2369_0_part7 rec_2_16_2369_0_join5 rfl rfl rfl
private theorem rec_2_16_2369_0_join7 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 640 640 = 61924831501920890599074494166336 :=
  phaseBlock_append rec_2_16_2369_0_join4 rec_2_16_2369_0_join6 rfl rfl rfl
private theorem rec_2_16_2369_0_join8 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 0 1280 = 136503409193934551559939703212672 :=
  phaseBlock_append rec_2_16_2369_0_join3 rec_2_16_2369_0_join7 rfl rfl rfl
private theorem rec_2_16_2369_0_join9 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1280 256 = 21426128856658839485952710109312 :=
  phaseBlock_append rec_2_16_2369_0_part10 rec_2_16_2369_0_part11 rfl rfl rfl
private theorem rec_2_16_2369_0_join10 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1664 256 = 18704676354624585141615393286272 :=
  phaseBlock_append rec_2_16_2369_0_part13 rec_2_16_2369_0_part14 rfl rfl rfl
private theorem rec_2_16_2369_0_join11 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1536 384 = 28728905957477995645816950009024 :=
  phaseBlock_append rec_2_16_2369_0_part12 rec_2_16_2369_0_join10 rfl rfl rfl
private theorem rec_2_16_2369_0_join12 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1280 640 = 50155034814136835131769660118336 :=
  phaseBlock_append rec_2_16_2369_0_join9 rec_2_16_2369_0_join11 rfl rfl rfl
private theorem rec_2_16_2369_0_join13 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1920 256 = 16957471672932603065823057946752 :=
  phaseBlock_append rec_2_16_2369_0_part15 rec_2_16_2369_0_part16 rfl rfl rfl
private theorem rec_2_16_2369_0_join14 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2304 256 = 14435004006637504173663513831552 :=
  phaseBlock_append rec_2_16_2369_0_part18 rec_2_16_2369_0_part19 rfl rfl rfl
private theorem rec_2_16_2369_0_join15 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2176 384 = 22275011558994649081479526075584 :=
  phaseBlock_append rec_2_16_2369_0_part17 rec_2_16_2369_0_join14 rfl rfl rfl
private theorem rec_2_16_2369_0_join16 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1920 640 = 39232483231927252147302584022336 :=
  phaseBlock_append rec_2_16_2369_0_join13 rec_2_16_2369_0_join15 rfl rfl rfl
private theorem rec_2_16_2369_0_join17 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 1280 1280 = 89387518046064087279072244140672 :=
  phaseBlock_append rec_2_16_2369_0_join12 rec_2_16_2369_0_join16 rfl rfl rfl
private theorem rec_2_16_2369_0_join18 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 0 2560 = 225890927239998638839011947353344 :=
  phaseBlock_append rec_2_16_2369_0_join8 rec_2_16_2369_0_join17 rfl rfl rfl
private theorem rec_2_16_2369_0_join19 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2560 256 = 12817586726306094411211710088926 :=
  phaseBlock_append rec_2_16_2369_0_part20 rec_2_16_2369_0_part21 rfl rfl rfl
private theorem rec_2_16_2369_0_join20 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2944 256 = 10485545538062220800744967475799 :=
  phaseBlock_append rec_2_16_2369_0_part23 rec_2_16_2369_0_part24 rfl rfl rfl
private theorem rec_2_16_2369_0_join21 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2816 384 = 16303570282238132583612462041971 :=
  phaseBlock_append rec_2_16_2369_0_part22 rec_2_16_2369_0_join20 rfl rfl rfl
private theorem rec_2_16_2369_0_join22 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2560 640 = 29121157008544226994824172130897 :=
  phaseBlock_append rec_2_16_2369_0_join19 rec_2_16_2369_0_join21 rfl rfl rfl
private theorem rec_2_16_2369_0_join23 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3200 256 = 8992264723711704067496117070978 :=
  phaseBlock_append rec_2_16_2369_0_part25 rec_2_16_2369_0_part26 rfl rfl rfl
private theorem rec_2_16_2369_0_join24 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3584 256 = 6842237241999037179743778576016 :=
  phaseBlock_append rec_2_16_2369_0_part28 rec_2_16_2369_0_part29 rfl rfl rfl
private theorem rec_2_16_2369_0_join25 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3456 384 = 10793452259871581364419836569914 :=
  phaseBlock_append rec_2_16_2369_0_part27 rec_2_16_2369_0_join24 rfl rfl rfl
private theorem rec_2_16_2369_0_join26 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3200 640 = 19785716983583285431915953640892 :=
  phaseBlock_append rec_2_16_2369_0_join23 rec_2_16_2369_0_join25 rfl rfl rfl
private theorem rec_2_16_2369_0_join27 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2560 1280 = 48906873992127512426740125771789 :=
  phaseBlock_append rec_2_16_2369_0_join22 rec_2_16_2369_0_join26 rfl rfl rfl
private theorem rec_2_16_2369_0_join28 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3840 256 = 5467528426507251184100532663865 :=
  phaseBlock_append rec_2_16_2369_0_part30 rec_2_16_2369_0_part31 rfl rfl rfl
private theorem rec_2_16_2369_0_join29 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4224 256 = 3491245364874503752028158355640 :=
  phaseBlock_append rec_2_16_2369_0_part33 rec_2_16_2369_0_part34 rfl rfl rfl
private theorem rec_2_16_2369_0_join30 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4096 384 = 5723869605176644620997291168266 :=
  phaseBlock_append rec_2_16_2369_0_part32 rec_2_16_2369_0_join29 rfl rfl rfl
private theorem rec_2_16_2369_0_join31 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3840 640 = 11191398031683895805097823832131 :=
  phaseBlock_append rec_2_16_2369_0_join28 rec_2_16_2369_0_join30 rfl rfl rfl
private theorem rec_2_16_2369_0_join32 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4480 256 = 2229648262343604886785417539151 :=
  phaseBlock_append rec_2_16_2369_0_part35 rec_2_16_2369_0_part36 rfl rfl rfl
private theorem rec_2_16_2369_0_join33 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4864 219 = 430763425312610538352439854416 :=
  phaseBlock_append rec_2_16_2369_0_part38 rec_2_16_2369_0_part39 rfl rfl rfl
private theorem rec_2_16_2369_0_join34 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4736 347 = 1086190449522855422799616131492 :=
  phaseBlock_append rec_2_16_2369_0_part37 rec_2_16_2369_0_join33 rfl rfl rfl
private theorem rec_2_16_2369_0_join35 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 4480 603 = 3315838711866460309585033670643 :=
  phaseBlock_append rec_2_16_2369_0_join32 rec_2_16_2369_0_join34 rfl rfl rfl
private theorem rec_2_16_2369_0_join36 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 3840 1243 = 14507236743550356114682857502774 :=
  phaseBlock_append rec_2_16_2369_0_join31 rec_2_16_2369_0_join35 rfl rfl rfl
private theorem rec_2_16_2369_0_join37 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 2560 2523 = 63414110735677868541422983274563 :=
  phaseBlock_append rec_2_16_2369_0_join27 rec_2_16_2369_0_join36 rfl rfl rfl
private theorem rec_2_16_2369_0_join38 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 0) 0 5083 = 289305037975676507380434930627907 :=
  phaseBlock_append rec_2_16_2369_0_join18 rec_2_16_2369_0_join37 rfl rfl rfl

private theorem rec_2_16_2369_0 : fastPhase (bank 2 16).shape 179798 2369 138 1 0 7 0 = 289305037975676507380434930627907 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_2_16_2369_0_join38

private theorem rec_2_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 0 128 = 15967540500422100858564604448000 := by decide +kernel
private theorem rec_2_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 128 128 = 15432206973702224224879180418304 := by decide +kernel
private theorem rec_2_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 256 128 = 14904303427409380564167320096000 := by decide +kernel
private theorem rec_2_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 384 128 = 14383769404613631721958816877824 := by decide +kernel
private theorem rec_2_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 512 128 = 13870544666059195998273348881664 := by decide +kernel
private theorem rec_2_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 640 128 = 13364569189856462362267399589120 := by decide +kernel
private theorem rec_2_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 768 128 = 12865783171174004666881178488064 := by decide +kernel
private theorem rec_2_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 896 128 = 12374127021930595863485541715200 := by decide +kernel
private theorem rec_2_16_2369_1_part8 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1024 128 = 11889541370487222216528912698624 := by decide +kernel
private theorem rec_2_16_2369_1_part9 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1152 128 = 11411967061339097518184202800384 := by decide +kernel
private theorem rec_2_16_2369_1_part10 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1280 128 = 10941345154807677302995731959040 := by decide +kernel
private theorem rec_2_16_2369_1_part11 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1408 128 = 10477616926732673062526149332224 := by decide +kernel
private theorem rec_2_16_2369_1_part12 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1536 128 = 10020723868164066460003353939200 := by decide +kernel
private theorem rec_2_16_2369_1_part13 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1664 128 = 9570607685054123544967415303424 := by decide +kernel
private theorem rec_2_16_2369_1_part14 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1792 128 = 9127210297949408967917494095104 := by decide +kernel
private theorem rec_2_16_2369_1_part15 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1920 128 = 8690473841682800194958762773760 := by decide +kernel
private theorem rec_2_16_2369_1_part16 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2048 128 = 8260340665065501722449326230784 := by decide +kernel
private theorem rec_2_16_2369_1_part17 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2176 128 = 7836753330579059291647142432000 := by decide +kernel
private theorem rec_2_16_2369_1_part18 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2304 128 = 7419654614067374103356943060224 := by decide +kernel
private theorem rec_2_16_2369_1_part19 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2432 128 = 7008987504428717032577154157824 := by decide +kernel
private theorem rec_2_16_2369_1_part20 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2560 128 = 6604695343087636250155073422454 := by decide +kernel
private theorem rec_2_16_2369_1_part21 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2688 128 = 6206722031149742866395092113632 := by decide +kernel
private theorem rec_2_16_2369_1_part22 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2816 128 = 5815011198060848053669683972856 := by decide +kernel
private theorem rec_2_16_2369_1_part23 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2944 128 = 5429506554307399349271730833855 := by decide +kernel
private theorem rec_2_16_2369_1_part24 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3072 128 = 5050152022980273485859050799982 := by decide +kernel
private theorem rec_2_16_2369_1_part25 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3200 128 = 4676891738645126325182194498784 := by decide +kernel
private theorem rec_2_16_2369_1_part26 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3328 128 = 4309670047213249178422801818980 := by decide +kernel
private theorem rec_2_16_2369_1_part27 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3456 128 = 3948431506445885507830380961880 := by decide +kernel
private theorem rec_2_16_2369_1_part28 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3584 128 = 3593120884811111620345993510428 := by decide +kernel
private theorem rec_2_16_2369_1_part29 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3712 128 = 3243683161195886584229300144430 := by decide +kernel
private theorem rec_2_16_2369_1_part30 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3840 128 = 2900063525001896791317886401666 := by decide +kernel
private theorem rec_2_16_2369_1_part31 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3968 128 = 2562207375831016095028377506633 := by decide +kernel
private theorem rec_2_16_2369_1_part32 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4096 128 = 2230060322764801806850210426360 := by decide +kernel
private theorem rec_2_16_2369_1_part33 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4224 128 = 1903568184216780464875405396420 := by decide +kernel
private theorem rec_2_16_2369_1_part34 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4352 128 = 1582676987993720829069830167358 := by decide +kernel
private theorem rec_2_16_2369_1_part35 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4480 128 = 1267332970529704618374947813610 := by decide +kernel
private theorem rec_2_16_2369_1_part36 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4608 128 = 957482576660752451298802846131 := by decide +kernel
private theorem rec_2_16_2369_1_part37 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4736 128 = 653072459509734326400685611390 := by decide +kernel
private theorem rec_2_16_2369_1_part38 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4864 128 = 354049480063356170704776776618 := by decide +kernel
private theorem rec_2_16_2369_1_part39 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4992 91 = 72779505700904635815055777218 := by decide +kernel
private theorem rec_2_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 0 256 = 31399747474124325083443784866304 :=
  phaseBlock_append rec_2_16_2369_1_part0 rec_2_16_2369_1_part1 rfl rfl rfl
private theorem rec_2_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 384 256 = 28254314070672827720232165759488 :=
  phaseBlock_append rec_2_16_2369_1_part3 rec_2_16_2369_1_part4 rfl rfl rfl
private theorem rec_2_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 256 384 = 43158617498082208284399485855488 :=
  phaseBlock_append rec_2_16_2369_1_part2 rec_2_16_2369_1_join1 rfl rfl rfl
private theorem rec_2_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 0 640 = 74558364972206533367843270721792 :=
  phaseBlock_append rec_2_16_2369_1_join0 rec_2_16_2369_1_join2 rfl rfl rfl
private theorem rec_2_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 640 256 = 26230352361030467029148578077184 :=
  phaseBlock_append rec_2_16_2369_1_part5 rec_2_16_2369_1_part6 rfl rfl rfl
private theorem rec_2_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1024 256 = 23301508431826319734713115499008 :=
  phaseBlock_append rec_2_16_2369_1_part8 rec_2_16_2369_1_part9 rfl rfl rfl
private theorem rec_2_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 896 384 = 35675635453756915598198657214208 :=
  phaseBlock_append rec_2_16_2369_1_part7 rec_2_16_2369_1_join5 rfl rfl rfl
private theorem rec_2_16_2369_1_join7 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 640 640 = 61905987814787382627347235291392 :=
  phaseBlock_append rec_2_16_2369_1_join4 rec_2_16_2369_1_join6 rfl rfl rfl
private theorem rec_2_16_2369_1_join8 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 0 1280 = 136464352786993915995190506013184 :=
  phaseBlock_append rec_2_16_2369_1_join3 rec_2_16_2369_1_join7 rfl rfl rfl
private theorem rec_2_16_2369_1_join9 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1280 256 = 21418962081540350365521881291264 :=
  phaseBlock_append rec_2_16_2369_1_part10 rec_2_16_2369_1_part11 rfl rfl rfl
private theorem rec_2_16_2369_1_join10 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1664 256 = 18697817983003532512884909398528 :=
  phaseBlock_append rec_2_16_2369_1_part13 rec_2_16_2369_1_part14 rfl rfl rfl
private theorem rec_2_16_2369_1_join11 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1536 384 = 28718541851167598972888263337728 :=
  phaseBlock_append rec_2_16_2369_1_part12 rec_2_16_2369_1_join10 rfl rfl rfl
private theorem rec_2_16_2369_1_join12 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1280 640 = 50137503932707949338410144628992 :=
  phaseBlock_append rec_2_16_2369_1_join9 rec_2_16_2369_1_join11 rfl rfl rfl
private theorem rec_2_16_2369_1_join13 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1920 256 = 16950814506748301917408089004544 :=
  phaseBlock_append rec_2_16_2369_1_part15 rec_2_16_2369_1_part16 rfl rfl rfl
private theorem rec_2_16_2369_1_join14 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2304 256 = 14428642118496091135934097218048 :=
  phaseBlock_append rec_2_16_2369_1_part18 rec_2_16_2369_1_part19 rfl rfl rfl
private theorem rec_2_16_2369_1_join15 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2176 384 = 22265395449075150427581239650048 :=
  phaseBlock_append rec_2_16_2369_1_part17 rec_2_16_2369_1_join14 rfl rfl rfl
private theorem rec_2_16_2369_1_join16 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1920 640 = 39216209955823452344989328654592 :=
  phaseBlock_append rec_2_16_2369_1_join13 rec_2_16_2369_1_join15 rfl rfl rfl
private theorem rec_2_16_2369_1_join17 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 1280 1280 = 89353713888531401683399473283584 :=
  phaseBlock_append rec_2_16_2369_1_join12 rec_2_16_2369_1_join16 rfl rfl rfl
private theorem rec_2_16_2369_1_join18 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 0 2560 = 225818066675525317678589979296768 :=
  phaseBlock_append rec_2_16_2369_1_join8 rec_2_16_2369_1_join17 rfl rfl rfl
private theorem rec_2_16_2369_1_join19 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2560 256 = 12811417374237379116550165536086 :=
  phaseBlock_append rec_2_16_2369_1_part20 rec_2_16_2369_1_part21 rfl rfl rfl
private theorem rec_2_16_2369_1_join20 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2944 256 = 10479658577287672835130781633837 :=
  phaseBlock_append rec_2_16_2369_1_part23 rec_2_16_2369_1_part24 rfl rfl rfl
private theorem rec_2_16_2369_1_join21 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2816 384 = 16294669775348520888800465606693 :=
  phaseBlock_append rec_2_16_2369_1_part22 rec_2_16_2369_1_join20 rfl rfl rfl
private theorem rec_2_16_2369_1_join22 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2560 640 = 29106087149585900005350631142779 :=
  phaseBlock_append rec_2_16_2369_1_join19 rec_2_16_2369_1_join21 rfl rfl rfl
private theorem rec_2_16_2369_1_join23 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3200 256 = 8986561785858375503604996317764 :=
  phaseBlock_append rec_2_16_2369_1_part25 rec_2_16_2369_1_part26 rfl rfl rfl
private theorem rec_2_16_2369_1_join24 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3584 256 = 6836804046006998204575293654858 :=
  phaseBlock_append rec_2_16_2369_1_part28 rec_2_16_2369_1_part29 rfl rfl rfl
private theorem rec_2_16_2369_1_join25 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3456 384 = 10785235552452883712405674616738 :=
  phaseBlock_append rec_2_16_2369_1_part27 rec_2_16_2369_1_join24 rfl rfl rfl
private theorem rec_2_16_2369_1_join26 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3200 640 = 19771797338311259216010670934502 :=
  phaseBlock_append rec_2_16_2369_1_join23 rec_2_16_2369_1_join25 rfl rfl rfl
private theorem rec_2_16_2369_1_join27 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2560 1280 = 48877884487897159221361302077281 :=
  phaseBlock_append rec_2_16_2369_1_join22 rec_2_16_2369_1_join26 rfl rfl rfl
private theorem rec_2_16_2369_1_join28 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3840 256 = 5462270900832912886346263908299 :=
  phaseBlock_append rec_2_16_2369_1_part30 rec_2_16_2369_1_part31 rfl rfl rfl
private theorem rec_2_16_2369_1_join29 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4224 256 = 3486245172210501293945235563778 :=
  phaseBlock_append rec_2_16_2369_1_part33 rec_2_16_2369_1_part34 rfl rfl rfl
private theorem rec_2_16_2369_1_join30 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4096 384 = 5716305494975303100795445990138 :=
  phaseBlock_append rec_2_16_2369_1_part32 rec_2_16_2369_1_join29 rfl rfl rfl
private theorem rec_2_16_2369_1_join31 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3840 640 = 11178576395808215987141709898437 :=
  phaseBlock_append rec_2_16_2369_1_join28 rec_2_16_2369_1_join30 rfl rfl rfl
private theorem rec_2_16_2369_1_join32 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4480 256 = 2224815547190457069673750659741 :=
  phaseBlock_append rec_2_16_2369_1_part35 rec_2_16_2369_1_part36 rfl rfl rfl
private theorem rec_2_16_2369_1_join33 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4864 219 = 426828985764260806519832553836 :=
  phaseBlock_append rec_2_16_2369_1_part38 rec_2_16_2369_1_part39 rfl rfl rfl
private theorem rec_2_16_2369_1_join34 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4736 347 = 1079901445273995132920518165226 :=
  phaseBlock_append rec_2_16_2369_1_part37 rec_2_16_2369_1_join33 rfl rfl rfl
private theorem rec_2_16_2369_1_join35 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 4480 603 = 3304716992464452202594268824967 :=
  phaseBlock_append rec_2_16_2369_1_join32 rec_2_16_2369_1_join34 rfl rfl rfl
private theorem rec_2_16_2369_1_join36 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 3840 1243 = 14483293388272668189735978723404 :=
  phaseBlock_append rec_2_16_2369_1_join31 rec_2_16_2369_1_join35 rfl rfl rfl
private theorem rec_2_16_2369_1_join37 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 2560 2523 = 63361177876169827411097280800685 :=
  phaseBlock_append rec_2_16_2369_1_join27 rec_2_16_2369_1_join36 rfl rfl rfl
private theorem rec_2_16_2369_1_join38 :
    phaseBlock (fastLayerG (bank 2 16).shape 179798 2369 138 1 0 7 1) 0 5083 = 289179244551695145089687260097453 :=
  phaseBlock_append rec_2_16_2369_1_join18 rec_2_16_2369_1_join37 rfl rfl rfl

private theorem rec_2_16_2369_1 : fastPhase (bank 2 16).shape 179798 2369 138 1 0 7 1 = 289179244551695145089687260097453 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_2_16_2369_1_join38

theorem receipt_2_16 : Checked (bank 2 16) 138 0 7 := by
  refine checked_from_values (bank 2 16) 138 0 7
    (P3_7_1.checked (bank 2 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_22951_5082)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_2_16_2368_0 rec_2_16_2368_1 rec_2_16_2369_0 rec_2_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect2_checked (i : Fin 17) (hi : i ≠ 0) :
    Checked (bank 2 i) (reserve i) (excess 2) (seed 2) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact receipt_2_1
  · exact receipt_2_2
  · exact receipt_2_3
  · exact receipt_2_4
  · exact receipt_2_5
  · exact receipt_2_6
  · exact receipt_2_7
  · exact receipt_2_8
  · exact receipt_2_9
  · exact receipt_2_10
  · exact receipt_2_11
  · exact receipt_2_12
  · exact receipt_2_13
  · exact receipt_2_14
  · exact receipt_2_15
  · exact receipt_2_16

end Lower6961.Lo.RescueSource
