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


private theorem rec_10_0_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2368 0 1 2 14 0) 0 128 = 3315385514348183194368 := by decide +kernel
private theorem rec_10_0_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2368 0 1 2 14 0) 128 2 = 466983660458184160 := by decide +kernel
private theorem rec_10_0_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2368 0 1 2 14 0) 0 130 = 3315852498008641378528 :=
  phaseBlock_append rec_10_0_2368_0_part0 rec_10_0_2368_0_part1 rfl rfl rfl

private theorem rec_10_0_2368_0 : fastPhase (bank 10 0).shape 179798 2368 0 1 2 14 0 = 3315852498008641378528 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_0_2368_0_join0

private theorem rec_10_0_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2368 0 1 2 14 1) 0 128 = 3248940245742280938368 := by decide +kernel
private theorem rec_10_0_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2368 0 1 2 14 1) 128 2 = 154091120169575160 := by decide +kernel
private theorem rec_10_0_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2368 0 1 2 14 1) 0 130 = 3249094336862450513528 :=
  phaseBlock_append rec_10_0_2368_1_part0 rec_10_0_2368_1_part1 rfl rfl rfl

private theorem rec_10_0_2368_1 : fastPhase (bank 10 0).shape 179798 2368 0 1 2 14 1 = 3249094336862450513528 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_0_2368_1_join0

private theorem rec_10_0_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2369 0 1 2 14 0) 0 128 = 3315406056699411495936 := by decide +kernel
private theorem rec_10_0_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2369 0 1 2 14 0) 128 2 = 466983366751645200 := by decide +kernel
private theorem rec_10_0_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2369 0 1 2 14 0) 0 130 = 3315873040066163141136 :=
  phaseBlock_append rec_10_0_2369_0_part0 rec_10_0_2369_0_part1 rfl rfl rfl

private theorem rec_10_0_2369_0 : fastPhase (bank 10 0).shape 179798 2369 0 1 2 14 0 = 3315873040066163141136 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_0_2369_0_join0

private theorem rec_10_0_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2369 0 1 2 14 1) 0 128 = 3248960324271674991296 := by decide +kernel
private theorem rec_10_0_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2369 0 1 2 14 1) 128 2 = 154091023924147200 := by decide +kernel
private theorem rec_10_0_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 0).shape 179798 2369 0 1 2 14 1) 0 130 = 3249114415295599138496 :=
  phaseBlock_append rec_10_0_2369_1_part0 rec_10_0_2369_1_part1 rfl rfl rfl

private theorem rec_10_0_2369_1 : fastPhase (bank 10 0).shape 179798 2369 0 1 2 14 1 = 3249114415295599138496 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_0_2369_1_join0

theorem receipt_10_0 : Checked (bank 10 0) 0 2 14 := by
  refine checked_from_values (bank 10 0) 0 2 14
    (P3_7_1.checked (bank 10 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_0_2368_0 rec_10_0_2368_1 rec_10_0_2369_0 rec_10_0_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2368 1 1 2 14 0) 0 128 = 4792807065173248738720 := by decide +kernel
private theorem rec_10_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2368 1 1 2 14 0) 128 2 = 725308455488933187 := by decide +kernel
private theorem rec_10_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2368 1 1 2 14 0) 0 130 = 4793532373628737671907 :=
  phaseBlock_append rec_10_1_2368_0_part0 rec_10_1_2368_0_part1 rfl rfl rfl

private theorem rec_10_1_2368_0 : fastPhase (bank 10 1).shape 179798 2368 1 1 2 14 0 = 4793532373628737671907 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_1_2368_0_join0

private theorem rec_10_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2368 1 1 2 14 1) 0 128 = 4699029048396890464672 := by decide +kernel
private theorem rec_10_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2368 1 1 2 14 1) 128 2 = 239482721793924675 := by decide +kernel
private theorem rec_10_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2368 1 1 2 14 1) 0 130 = 4699268531118684389347 :=
  phaseBlock_append rec_10_1_2368_1_part0 rec_10_1_2368_1_part1 rfl rfl rfl

private theorem rec_10_1_2368_1 : fastPhase (bank 10 1).shape 179798 2368 1 1 2 14 1 = 4699268531118684389347 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_1_2368_1_join0

private theorem rec_10_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2369 1 1 2 14 0) 0 128 = 4792836288766752043584 := by decide +kernel
private theorem rec_10_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2369 1 1 2 14 0) 128 2 = 725307967413235752 := by decide +kernel
private theorem rec_10_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2369 1 1 2 14 0) 0 130 = 4793561596734165279336 :=
  phaseBlock_append rec_10_1_2369_0_part0 rec_10_1_2369_0_part1 rfl rfl rfl

private theorem rec_10_1_2369_0 : fastPhase (bank 10 1).shape 179798 2369 1 1 2 14 0 = 4793561596734165279336 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_1_2369_0_join0

private theorem rec_10_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2369 1 1 2 14 1) 0 128 = 4699057628077915774080 := by decide +kernel
private theorem rec_10_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2369 1 1 2 14 1) 128 2 = 239482561699303956 := by decide +kernel
private theorem rec_10_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 1).shape 179798 2369 1 1 2 14 1) 0 130 = 4699297110639615078036 :=
  phaseBlock_append rec_10_1_2369_1_part0 rec_10_1_2369_1_part1 rfl rfl rfl

private theorem rec_10_1_2369_1 : fastPhase (bank 10 1).shape 179798 2369 1 1 2 14 1 = 4699297110639615078036 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_1_2369_1_join0

theorem receipt_10_1 : Checked (bank 10 1) 1 2 14 := by
  refine checked_from_values (bank 10 1) 1 2 14
    (P3_7_1.checked (bank 10 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_1_2368_0 rec_10_1_2368_1 rec_10_1_2369_0 rec_10_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2368 2 1 2 14 0) 0 128 = 7521466881235096552000 := by decide +kernel
private theorem rec_10_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2368 2 1 2 14 0) 128 2 = 1219377279603265974 := by decide +kernel
private theorem rec_10_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2368 2 1 2 14 0) 0 130 = 7522686258514699817974 :=
  phaseBlock_append rec_10_2_2368_0_part0 rec_10_2_2368_0_part1 rfl rfl rfl

private theorem rec_10_2_2368_0 : fastPhase (bank 10 2).shape 179798 2368 2 1 2 14 0 = 7522686258514699817974 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_2_2368_0_join0

private theorem rec_10_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2368 2 1 2 14 1) 0 128 = 7377847638358989805504 := by decide +kernel
private theorem rec_10_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2368 2 1 2 14 1) 128 2 = 402851826022077630 := by decide +kernel
private theorem rec_10_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2368 2 1 2 14 1) 0 130 = 7378250490185011883134 :=
  phaseBlock_append rec_10_2_2368_1_part0 rec_10_2_2368_1_part1 rfl rfl rfl

private theorem rec_10_2_2368_1 : fastPhase (bank 10 2).shape 179798 2368 2 1 2 14 1 = 7378250490185011883134 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_2_2368_1_join0

private theorem rec_10_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2369 2 1 2 14 0) 0 128 = 7521511999600095686784 := by decide +kernel
private theorem rec_10_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2369 2 1 2 14 0) 128 2 = 1219376405422644732 := by decide +kernel
private theorem rec_10_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2369 2 1 2 14 0) 0 130 = 7522731376005518331516 :=
  phaseBlock_append rec_10_2_2369_0_part0 rec_10_2_2369_0_part1 rfl rfl rfl

private theorem rec_10_2_2369_0 : fastPhase (bank 10 2).shape 179798 2369 2 1 2 14 0 = 7522731376005518331516 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_2_2369_0_join0

private theorem rec_10_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2369 2 1 2 14 1) 0 128 = 7377891787304270154816 := by decide +kernel
private theorem rec_10_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2369 2 1 2 14 1) 128 2 = 402851539025646480 := by decide +kernel
private theorem rec_10_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 2).shape 179798 2369 2 1 2 14 1) 0 130 = 7378294638843295801296 :=
  phaseBlock_append rec_10_2_2369_1_part0 rec_10_2_2369_1_part1 rfl rfl rfl

private theorem rec_10_2_2369_1 : fastPhase (bank 10 2).shape 179798 2369 2 1 2 14 1 = 7378294638843295801296 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_10_2_2369_1_join0

theorem receipt_10_2 : Checked (bank 10 2) 2 2 14 := by
  refine checked_from_values (bank 10 2) 2 2 14
    (P3_7_1.checked (bank 10 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_2_2368_0 rec_10_2_2368_1 rec_10_2_2369_0 rec_10_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2368 3 1 2 14 0) 0 128 = 21507661233204780574752 := by decide +kernel
private theorem rec_10_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2368 3 1 2 14 0) 128 63 = 1367098129753407302160 := by decide +kernel
private theorem rec_10_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2368 3 1 2 14 0) 0 191 = 22874759362958187876912 :=
  phaseBlock_append rec_10_3_2368_0_part0 rec_10_3_2368_0_part1 rfl rfl rfl

private theorem rec_10_3_2368_0 : fastPhase (bank 10 3).shape 179798 2368 3 1 2 14 0 = 22874759362958187876912 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_3_2368_0_join0

private theorem rec_10_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2368 3 1 2 14 1) 0 128 = 21234535150474813767712 := by decide +kernel
private theorem rec_10_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2368 3 1 2 14 1) 128 63 = 1316707634809550892048 := by decide +kernel
private theorem rec_10_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2368 3 1 2 14 1) 0 191 = 22551242785284364659760 :=
  phaseBlock_append rec_10_3_2368_1_part0 rec_10_3_2368_1_part1 rfl rfl rfl

private theorem rec_10_3_2368_1 : fastPhase (bank 10 3).shape 179798 2368 3 1 2 14 1 = 22551242785284364659760 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_3_2368_1_join0

private theorem rec_10_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2369 3 1 2 14 0) 0 128 = 21507800177930325443072 := by decide +kernel
private theorem rec_10_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2369 3 1 2 14 0) 128 63 = 1367099629851517755648 := by decide +kernel
private theorem rec_10_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2369 3 1 2 14 0) 0 191 = 22874899807781843198720 :=
  phaseBlock_append rec_10_3_2369_0_part0 rec_10_3_2369_0_part1 rfl rfl rfl

private theorem rec_10_3_2369_0 : fastPhase (bank 10 3).shape 179798 2369 3 1 2 14 0 = 22874899807781843198720 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_3_2369_0_join0

private theorem rec_10_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2369 3 1 2 14 1) 0 128 = 21234671922332483116096 := by decide +kernel
private theorem rec_10_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2369 3 1 2 14 1) 128 63 = 1316709078086214638112 := by decide +kernel
private theorem rec_10_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 3).shape 179798 2369 3 1 2 14 1) 0 191 = 22551381000418697754208 :=
  phaseBlock_append rec_10_3_2369_1_part0 rec_10_3_2369_1_part1 rfl rfl rfl

private theorem rec_10_3_2369_1 : fastPhase (bank 10 3).shape 179798 2369 3 1 2 14 1 = 22551381000418697754208 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_3_2369_1_join0

theorem receipt_10_3 : Checked (bank 10 3) 3 2 14 := by
  refine checked_from_values (bank 10 3) 3 2 14
    (P3_7_1.checked (bank 10 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_3_2368_0 rec_10_3_2368_1 rec_10_3_2369_0 rec_10_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2368 4 1 2 14 0) 0 128 = 26132119797125774322752 := by decide +kernel
private theorem rec_10_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2368 4 1 2 14 0) 128 63 = 1719859208946222885408 := by decide +kernel
private theorem rec_10_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2368 4 1 2 14 0) 0 191 = 27851979006071997208160 :=
  phaseBlock_append rec_10_4_2368_0_part0 rec_10_4_2368_0_part1 rfl rfl rfl

private theorem rec_10_4_2368_0 : fastPhase (bank 10 4).shape 179798 2368 4 1 2 14 0 = 27851979006071997208160 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_4_2368_0_join0

private theorem rec_10_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2368 4 1 2 14 1) 0 128 = 25807180943084265126720 := by decide +kernel
private theorem rec_10_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2368 4 1 2 14 1) 128 63 = 1656950930267151077328 := by decide +kernel
private theorem rec_10_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2368 4 1 2 14 1) 0 191 = 27464131873351416204048 :=
  phaseBlock_append rec_10_4_2368_1_part0 rec_10_4_2368_1_part1 rfl rfl rfl

private theorem rec_10_4_2368_1 : fastPhase (bank 10 4).shape 179798 2368 4 1 2 14 1 = 27464131873351416204048 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_4_2368_1_join0

private theorem rec_10_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2369 4 1 2 14 0) 0 128 = 26132287129295716599744 := by decide +kernel
private theorem rec_10_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2369 4 1 2 14 0) 128 63 = 1719861035401517527008 := by decide +kernel
private theorem rec_10_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2369 4 1 2 14 0) 0 191 = 27852148164697234126752 :=
  phaseBlock_append rec_10_4_2369_0_part0 rec_10_4_2369_0_part1 rfl rfl rfl

private theorem rec_10_4_2369_0 : fastPhase (bank 10 4).shape 179798 2369 4 1 2 14 0 = 27852148164697234126752 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_4_2369_0_join0

private theorem rec_10_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2369 4 1 2 14 1) 0 128 = 25807345700525324247680 := by decide +kernel
private theorem rec_10_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2369 4 1 2 14 1) 128 63 = 1656952688231049447168 := by decide +kernel
private theorem rec_10_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 4).shape 179798 2369 4 1 2 14 1) 0 191 = 27464298388756373694848 :=
  phaseBlock_append rec_10_4_2369_1_part0 rec_10_4_2369_1_part1 rfl rfl rfl

private theorem rec_10_4_2369_1 : fastPhase (bank 10 4).shape 179798 2369 4 1 2 14 1 = 27464298388756373694848 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_4_2369_1_join0

theorem receipt_10_4 : Checked (bank 10 4) 4 2 14 := by
  refine checked_from_values (bank 10 4) 4 2 14
    (P3_7_1.checked (bank 10 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_4_2368_0 rec_10_4_2368_1 rec_10_4_2369_0 rec_10_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2368 5 1 2 14 0) 0 128 = 32423202311043155111136 := by decide +kernel
private theorem rec_10_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2368 5 1 2 14 0) 128 63 = 2208016200745089265776 := by decide +kernel
private theorem rec_10_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2368 5 1 2 14 0) 0 191 = 34631218511788244376912 :=
  phaseBlock_append rec_10_5_2368_0_part0 rec_10_5_2368_0_part1 rfl rfl rfl

private theorem rec_10_5_2368_0 : fastPhase (bank 10 5).shape 179798 2368 5 1 2 14 0 = 34631218511788244376912 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_5_2368_0_join0

private theorem rec_10_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2368 5 1 2 14 1) 0 128 = 32028615575171759896800 := by decide +kernel
private theorem rec_10_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2368 5 1 2 14 1) 128 63 = 2127852364309796559792 := by decide +kernel
private theorem rec_10_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2368 5 1 2 14 1) 0 191 = 34156467939481556456592 :=
  phaseBlock_append rec_10_5_2368_1_part0 rec_10_5_2368_1_part1 rfl rfl rfl

private theorem rec_10_5_2368_1 : fastPhase (bank 10 5).shape 179798 2368 5 1 2 14 1 = 34156467939481556456592 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_5_2368_1_join0

private theorem rec_10_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2369 5 1 2 14 0) 0 128 = 32423408080550256362112 := by decide +kernel
private theorem rec_10_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2369 5 1 2 14 0) 128 63 = 2208018467933447674176 := by decide +kernel
private theorem rec_10_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2369 5 1 2 14 0) 0 191 = 34631426548483704036288 :=
  phaseBlock_append rec_10_5_2369_0_part0 rec_10_5_2369_0_part1 rfl rfl rfl

private theorem rec_10_5_2369_0 : fastPhase (bank 10 5).shape 179798 2369 5 1 2 14 0 = 34631426548483704036288 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_5_2369_0_join0

private theorem rec_10_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2369 5 1 2 14 1) 0 128 = 32028818230370847438144 := by decide +kernel
private theorem rec_10_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2369 5 1 2 14 1) 128 63 = 2127854547325435418784 := by decide +kernel
private theorem rec_10_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 5).shape 179798 2369 5 1 2 14 1) 0 191 = 34156672777696282856928 :=
  phaseBlock_append rec_10_5_2369_1_part0 rec_10_5_2369_1_part1 rfl rfl rfl

private theorem rec_10_5_2369_1 : fastPhase (bank 10 5).shape 179798 2369 5 1 2 14 1 = 34156672777696282856928 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_5_2369_1_join0

theorem receipt_10_5 : Checked (bank 10 5) 5 2 14 := by
  refine checked_from_values (bank 10 5) 5 2 14
    (P3_7_1.checked (bank 10 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_5_2368_0 rec_10_5_2368_1 rec_10_5_2369_0 rec_10_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2368 7 1 2 14 0) 0 128 = 54358209820680439304832 := by decide +kernel
private theorem rec_10_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2368 7 1 2 14 0) 128 63 = 3956018940059017038144 := by decide +kernel
private theorem rec_10_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2368 7 1 2 14 0) 0 191 = 58314228760739456342976 :=
  phaseBlock_append rec_10_6_2368_0_part0 rec_10_6_2368_0_part1 rfl rfl rfl

private theorem rec_10_6_2368_0 : fastPhase (bank 10 6).shape 179798 2368 7 1 2 14 0 = 58314228760739456342976 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_6_2368_0_join0

private theorem rec_10_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2368 7 1 2 14 1) 0 128 = 53725442858563973161344 := by decide +kernel
private theorem rec_10_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2368 7 1 2 14 1) 128 63 = 3814431085450753066992 := by decide +kernel
private theorem rec_10_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2368 7 1 2 14 1) 0 191 = 57539873944014726228336 :=
  phaseBlock_append rec_10_6_2368_1_part0 rec_10_6_2368_1_part1 rfl rfl rfl

private theorem rec_10_6_2368_1 : fastPhase (bank 10 6).shape 179798 2368 7 1 2 14 1 = 57539873944014726228336 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_6_2368_1_join0

private theorem rec_10_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2369 7 1 2 14 0) 0 128 = 54358548603637487953536 := by decide +kernel
private theorem rec_10_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2369 7 1 2 14 0) 128 63 = 3956022725136787061568 := by decide +kernel
private theorem rec_10_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2369 7 1 2 14 0) 0 191 = 58314571328774275015104 :=
  phaseBlock_append rec_10_6_2369_0_part0 rec_10_6_2369_0_part1 rfl rfl rfl

private theorem rec_10_6_2369_0 : fastPhase (bank 10 6).shape 179798 2369 7 1 2 14 0 = 58314571328774275015104 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_6_2369_0_join0

private theorem rec_10_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2369 7 1 2 14 1) 0 128 = 53725776685410423867456 := by decide +kernel
private theorem rec_10_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2369 7 1 2 14 1) 128 63 = 3814434732777911115552 := by decide +kernel
private theorem rec_10_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 6).shape 179798 2369 7 1 2 14 1) 0 191 = 57540211418188334983008 :=
  phaseBlock_append rec_10_6_2369_1_part0 rec_10_6_2369_1_part1 rfl rfl rfl

private theorem rec_10_6_2369_1 : fastPhase (bank 10 6).shape 179798 2369 7 1 2 14 1 = 57540211418188334983008 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_10_6_2369_1_join0

theorem receipt_10_6 : Checked (bank 10 6) 7 2 14 := by
  refine checked_from_values (bank 10 6) 7 2 14
    (P3_7_1.checked (bank 10 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_6_2368_0 rec_10_6_2368_1 rec_10_6_2369_0 rec_10_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2368 10 1 2 14 0) 0 128 = 196306442757257025586848 := by decide +kernel
private theorem rec_10_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2368 10 1 2 14 0) 128 128 = 48491683503868891748000 := by decide +kernel
private theorem rec_10_7_2368_0_part2 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2368 10 1 2 14 0) 256 22 = 657076212236309332390 := by decide +kernel
private theorem rec_10_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2368 10 1 2 14 0) 128 150 = 49148759716105201080390 :=
  phaseBlock_append rec_10_7_2368_0_part1 rec_10_7_2368_0_part2 rfl rfl rfl
private theorem rec_10_7_2368_0_join1 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2368 10 1 2 14 0) 0 278 = 245455202473362226667238 :=
  phaseBlock_append rec_10_7_2368_0_part0 rec_10_7_2368_0_join0 rfl rfl rfl

private theorem rec_10_7_2368_0 : fastPhase (bank 10 7).shape 179798 2368 10 1 2 14 0 = 245455202473362226667238 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_7_2368_0_join1

private theorem rec_10_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2368 10 1 2 14 1) 0 128 = 194752405445445698430048 := by decide +kernel
private theorem rec_10_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2368 10 1 2 14 1) 128 128 = 47738659633963297027168 := by decide +kernel
private theorem rec_10_7_2368_1_part2 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2368 10 1 2 14 1) 256 22 = 597114751831015730697 := by decide +kernel
private theorem rec_10_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2368 10 1 2 14 1) 128 150 = 48335774385794312757865 :=
  phaseBlock_append rec_10_7_2368_1_part1 rec_10_7_2368_1_part2 rfl rfl rfl
private theorem rec_10_7_2368_1_join1 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2368 10 1 2 14 1) 0 278 = 243088179831240011187913 :=
  phaseBlock_append rec_10_7_2368_1_part0 rec_10_7_2368_1_join0 rfl rfl rfl

private theorem rec_10_7_2368_1 : fastPhase (bank 10 7).shape 179798 2368 10 1 2 14 1 = 243088179831240011187913 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_7_2368_1_join1

private theorem rec_10_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2369 10 1 2 14 0) 0 128 = 196307793188811730086752 := by decide +kernel
private theorem rec_10_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2369 10 1 2 14 0) 128 128 = 48491798491208582568800 := by decide +kernel
private theorem rec_10_7_2369_0_part2 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2369 10 1 2 14 0) 256 22 = 657075885963708852410 := by decide +kernel
private theorem rec_10_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2369 10 1 2 14 0) 128 150 = 49148874377172291421210 :=
  phaseBlock_append rec_10_7_2369_0_part1 rec_10_7_2369_0_part2 rfl rfl rfl
private theorem rec_10_7_2369_0_join1 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2369 10 1 2 14 0) 0 278 = 245456667565984021507962 :=
  phaseBlock_append rec_10_7_2369_0_part0 rec_10_7_2369_0_join0 rfl rfl rfl

private theorem rec_10_7_2369_0 : fastPhase (bank 10 7).shape 179798 2369 10 1 2 14 0 = 245456667565984021507962 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_7_2369_0_join1

private theorem rec_10_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2369 10 1 2 14 1) 0 128 = 194753742019893080459232 := by decide +kernel
private theorem rec_10_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2369 10 1 2 14 1) 128 128 = 47738772574431253305312 := by decide +kernel
private theorem rec_10_7_2369_1_part2 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2369 10 1 2 14 1) 256 22 = 597114456259972481523 := by decide +kernel
private theorem rec_10_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2369 10 1 2 14 1) 128 150 = 48335887030691225786835 :=
  phaseBlock_append rec_10_7_2369_1_part1 rec_10_7_2369_1_part2 rfl rfl rfl
private theorem rec_10_7_2369_1_join1 :
    phaseBlock (fastLayerG (bank 10 7).shape 179798 2369 10 1 2 14 1) 0 278 = 243089629050584306246067 :=
  phaseBlock_append rec_10_7_2369_1_part0 rec_10_7_2369_1_join0 rfl rfl rfl

private theorem rec_10_7_2369_1 : fastPhase (bank 10 7).shape 179798 2369 10 1 2 14 1 = 243089629050584306246067 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_7_2369_1_join1

theorem receipt_10_7 : Checked (bank 10 7) 10 2 14 := by
  refine checked_from_values (bank 10 7) 10 2 14
    (P3_7_1.checked (bank 10 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_7_2368_0 rec_10_7_2368_1 rec_10_7_2369_0 rec_10_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2368 16 1 2 14 0) 0 128 = 562094332462404402621120 := by decide +kernel
private theorem rec_10_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2368 16 1 2 14 0) 128 128 = 154678879790400388958912 := by decide +kernel
private theorem rec_10_8_2368_0_part2 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2368 16 1 2 14 0) 256 22 = 2318326507510000088068 := by decide +kernel
private theorem rec_10_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2368 16 1 2 14 0) 128 150 = 156997206297910389046980 :=
  phaseBlock_append rec_10_8_2368_0_part1 rec_10_8_2368_0_part2 rfl rfl rfl
private theorem rec_10_8_2368_0_join1 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2368 16 1 2 14 0) 0 278 = 719091538760314791668100 :=
  phaseBlock_append rec_10_8_2368_0_part0 rec_10_8_2368_0_join0 rfl rfl rfl

private theorem rec_10_8_2368_0 : fastPhase (bank 10 8).shape 179798 2368 16 1 2 14 0 = 719091538760314791668100 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_8_2368_0_join1

private theorem rec_10_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2368 16 1 2 14 1) 0 128 = 558090062133160402563776 := by decide +kernel
private theorem rec_10_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2368 16 1 2 14 1) 128 128 = 152404180673534556885696 := by decide +kernel
private theorem rec_10_8_2368_1_part2 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2368 16 1 2 14 1) 256 22 = 2108495685447177683734 := by decide +kernel
private theorem rec_10_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2368 16 1 2 14 1) 128 150 = 154512676358981734569430 :=
  phaseBlock_append rec_10_8_2368_1_part1 rec_10_8_2368_1_part2 rfl rfl rfl
private theorem rec_10_8_2368_1_join1 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2368 16 1 2 14 1) 0 278 = 712602738492142137133206 :=
  phaseBlock_append rec_10_8_2368_1_part0 rec_10_8_2368_1_join0 rfl rfl rfl

private theorem rec_10_8_2368_1 : fastPhase (bank 10 8).shape 179798 2368 16 1 2 14 1 = 712602738492142137133206 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_8_2368_1_join1

private theorem rec_10_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2369 16 1 2 14 0) 0 128 = 562098087739784454299424 := by decide +kernel
private theorem rec_10_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2369 16 1 2 14 0) 128 128 = 154679220287713983819552 := by decide +kernel
private theorem rec_10_8_2369_0_part2 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2369 16 1 2 14 0) 256 22 = 2318325065423434218558 := by decide +kernel
private theorem rec_10_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2369 16 1 2 14 0) 128 150 = 156997545353137418038110 :=
  phaseBlock_append rec_10_8_2369_0_part1 rec_10_8_2369_0_part2 rfl rfl rfl
private theorem rec_10_8_2369_0_join1 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2369 16 1 2 14 0) 0 278 = 719095633092921872337534 :=
  phaseBlock_append rec_10_8_2369_0_part0 rec_10_8_2369_0_join0 rfl rfl rfl

private theorem rec_10_8_2369_0 : fastPhase (bank 10 8).shape 179798 2369 16 1 2 14 0 = 719095633092921872337534 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_8_2369_0_join1

private theorem rec_10_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2369 16 1 2 14 1) 0 128 = 558093781695818349527136 := by decide +kernel
private theorem rec_10_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2369 16 1 2 14 1) 128 128 = 152404515377011926675552 := by decide +kernel
private theorem rec_10_8_2369_1_part2 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2369 16 1 2 14 1) 256 22 = 2108494377509939673408 := by decide +kernel
private theorem rec_10_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2369 16 1 2 14 1) 128 150 = 154513009754521866348960 :=
  phaseBlock_append rec_10_8_2369_1_part1 rec_10_8_2369_1_part2 rfl rfl rfl
private theorem rec_10_8_2369_1_join1 :
    phaseBlock (fastLayerG (bank 10 8).shape 179798 2369 16 1 2 14 1) 0 278 = 712606791450340215876096 :=
  phaseBlock_append rec_10_8_2369_1_part0 rec_10_8_2369_1_join0 rfl rfl rfl

private theorem rec_10_8_2369_1 : fastPhase (bank 10 8).shape 179798 2369 16 1 2 14 1 = 712606791450340215876096 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_8_2369_1_join1

theorem receipt_10_8 : Checked (bank 10 8) 16 2 14 := by
  refine checked_from_values (bank 10 8) 16 2 14
    (P3_7_1.checked (bank 10 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_8_2368_0 rec_10_8_2368_1 rec_10_8_2369_0 rec_10_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2368 10 1 2 14 0) 0 128 = 196306442757257025586848 := by decide +kernel
private theorem rec_10_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2368 10 1 2 14 0) 128 128 = 48491683503868891748000 := by decide +kernel
private theorem rec_10_9_2368_0_part2 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2368 10 1 2 14 0) 256 22 = 657076212236309332390 := by decide +kernel
private theorem rec_10_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2368 10 1 2 14 0) 128 150 = 49148759716105201080390 :=
  phaseBlock_append rec_10_9_2368_0_part1 rec_10_9_2368_0_part2 rfl rfl rfl
private theorem rec_10_9_2368_0_join1 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2368 10 1 2 14 0) 0 278 = 245455202473362226667238 :=
  phaseBlock_append rec_10_9_2368_0_part0 rec_10_9_2368_0_join0 rfl rfl rfl

private theorem rec_10_9_2368_0 : fastPhase (bank 10 9).shape 179798 2368 10 1 2 14 0 = 245455202473362226667238 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_9_2368_0_join1

private theorem rec_10_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2368 10 1 2 14 1) 0 128 = 194752405445445698430048 := by decide +kernel
private theorem rec_10_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2368 10 1 2 14 1) 128 128 = 47738659633963297027168 := by decide +kernel
private theorem rec_10_9_2368_1_part2 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2368 10 1 2 14 1) 256 22 = 597114751831015730697 := by decide +kernel
private theorem rec_10_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2368 10 1 2 14 1) 128 150 = 48335774385794312757865 :=
  phaseBlock_append rec_10_9_2368_1_part1 rec_10_9_2368_1_part2 rfl rfl rfl
private theorem rec_10_9_2368_1_join1 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2368 10 1 2 14 1) 0 278 = 243088179831240011187913 :=
  phaseBlock_append rec_10_9_2368_1_part0 rec_10_9_2368_1_join0 rfl rfl rfl

private theorem rec_10_9_2368_1 : fastPhase (bank 10 9).shape 179798 2368 10 1 2 14 1 = 243088179831240011187913 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_9_2368_1_join1

private theorem rec_10_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2369 10 1 2 14 0) 0 128 = 196307793188811730086752 := by decide +kernel
private theorem rec_10_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2369 10 1 2 14 0) 128 128 = 48491798491208582568800 := by decide +kernel
private theorem rec_10_9_2369_0_part2 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2369 10 1 2 14 0) 256 22 = 657075885963708852410 := by decide +kernel
private theorem rec_10_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2369 10 1 2 14 0) 128 150 = 49148874377172291421210 :=
  phaseBlock_append rec_10_9_2369_0_part1 rec_10_9_2369_0_part2 rfl rfl rfl
private theorem rec_10_9_2369_0_join1 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2369 10 1 2 14 0) 0 278 = 245456667565984021507962 :=
  phaseBlock_append rec_10_9_2369_0_part0 rec_10_9_2369_0_join0 rfl rfl rfl

private theorem rec_10_9_2369_0 : fastPhase (bank 10 9).shape 179798 2369 10 1 2 14 0 = 245456667565984021507962 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_9_2369_0_join1

private theorem rec_10_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2369 10 1 2 14 1) 0 128 = 194753742019893080459232 := by decide +kernel
private theorem rec_10_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2369 10 1 2 14 1) 128 128 = 47738772574431253305312 := by decide +kernel
private theorem rec_10_9_2369_1_part2 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2369 10 1 2 14 1) 256 22 = 597114456259972481523 := by decide +kernel
private theorem rec_10_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2369 10 1 2 14 1) 128 150 = 48335887030691225786835 :=
  phaseBlock_append rec_10_9_2369_1_part1 rec_10_9_2369_1_part2 rfl rfl rfl
private theorem rec_10_9_2369_1_join1 :
    phaseBlock (fastLayerG (bank 10 9).shape 179798 2369 10 1 2 14 1) 0 278 = 243089629050584306246067 :=
  phaseBlock_append rec_10_9_2369_1_part0 rec_10_9_2369_1_join0 rfl rfl rfl

private theorem rec_10_9_2369_1 : fastPhase (bank 10 9).shape 179798 2369 10 1 2 14 1 = 243089629050584306246067 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_10_9_2369_1_join1

theorem receipt_10_9 : Checked (bank 10 9) 10 2 14 := by
  refine checked_from_values (bank 10 9) 10 2 14
    (P3_7_1.checked (bank 10 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_9_2368_0 rec_10_9_2368_1 rec_10_9_2369_0 rec_10_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2368 20 1 2 14 0) 0 128 = 1327635735724431760657728 := by decide +kernel
private theorem rec_10_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2368 20 1 2 14 0) 128 128 = 559398932512688092220736 := by decide +kernel
private theorem rec_10_10_2368_0_part2 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2368 20 1 2 14 0) 256 114 = 109429227636946172348097 := by decide +kernel
private theorem rec_10_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2368 20 1 2 14 0) 128 242 = 668828160149634264568833 :=
  phaseBlock_append rec_10_10_2368_0_part1 rec_10_10_2368_0_part2 rfl rfl rfl
private theorem rec_10_10_2368_0_join1 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2368 20 1 2 14 0) 0 370 = 1996463895874066025226561 :=
  phaseBlock_append rec_10_10_2368_0_part0 rec_10_10_2368_0_join0 rfl rfl rfl

private theorem rec_10_10_2368_0 : fastPhase (bank 10 10).shape 179798 2368 20 1 2 14 0 = 1996463895874066025226561 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_10_10_2368_0_join1

private theorem rec_10_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2368 20 1 2 14 1) 0 128 = 1320445256729825954627904 := by decide +kernel
private theorem rec_10_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2368 20 1 2 14 1) 128 128 = 554693441768707655287104 := by decide +kernel
private theorem rec_10_10_2368_1_part2 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2368 20 1 2 14 1) 256 114 = 107236772764486364956143 := by decide +kernel
private theorem rec_10_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2368 20 1 2 14 1) 128 242 = 661930214533194020243247 :=
  phaseBlock_append rec_10_10_2368_1_part1 rec_10_10_2368_1_part2 rfl rfl rfl
private theorem rec_10_10_2368_1_join1 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2368 20 1 2 14 1) 0 370 = 1982375471263019974871151 :=
  phaseBlock_append rec_10_10_2368_1_part0 rec_10_10_2368_1_join0 rfl rfl rfl

private theorem rec_10_10_2368_1 : fastPhase (bank 10 10).shape 179798 2368 20 1 2 14 1 = 1982375471263019974871151 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_10_10_2368_1_join1

private theorem rec_10_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2369 20 1 2 14 0) 0 128 = 1327645290449313145906848 := by decide +kernel
private theorem rec_10_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2369 20 1 2 14 0) 128 128 = 559400878783123020789408 := by decide +kernel
private theorem rec_10_10_2369_0_part2 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2369 20 1 2 14 0) 256 114 = 109429306073494919595513 := by decide +kernel
private theorem rec_10_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2369 20 1 2 14 0) 128 242 = 668830184856617940384921 :=
  phaseBlock_append rec_10_10_2369_0_part1 rec_10_10_2369_0_part2 rfl rfl rfl
private theorem rec_10_10_2369_0_join1 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2369 20 1 2 14 0) 0 370 = 1996475475305931086291769 :=
  phaseBlock_append rec_10_10_2369_0_part0 rec_10_10_2369_0_join0 rfl rfl rfl

private theorem rec_10_10_2369_0 : fastPhase (bank 10 10).shape 179798 2369 20 1 2 14 0 = 1996475475305931086291769 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_10_10_2369_0_join1

private theorem rec_10_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2369 20 1 2 14 1) 0 128 = 1320454742195243875491936 := by decide +kernel
private theorem rec_10_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2369 20 1 2 14 1) 128 128 = 554695367155307460218976 := by decide +kernel
private theorem rec_10_10_2369_1_part2 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2369 20 1 2 14 1) 256 114 = 107236849608286471033077 := by decide +kernel
private theorem rec_10_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2369 20 1 2 14 1) 128 242 = 661932216763593931252053 :=
  phaseBlock_append rec_10_10_2369_1_part1 rec_10_10_2369_1_part2 rfl rfl rfl
private theorem rec_10_10_2369_1_join1 :
    phaseBlock (fastLayerG (bank 10 10).shape 179798 2369 20 1 2 14 1) 0 370 = 1982386958958837806743989 :=
  phaseBlock_append rec_10_10_2369_1_part0 rec_10_10_2369_1_join0 rfl rfl rfl

private theorem rec_10_10_2369_1 : fastPhase (bank 10 10).shape 179798 2369 20 1 2 14 1 = 1982386958958837806743989 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_10_10_2369_1_join1

theorem receipt_10_10 : Checked (bank 10 10) 20 2 14 := by
  refine checked_from_values (bank 10 10) 20 2 14
    (P3_7_1.checked (bank 10 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_10_2368_0 rec_10_10_2368_1 rec_10_10_2369_0 rec_10_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 0) 0 128 = 7237215283514109408086016 := by decide +kernel
private theorem rec_10_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 0) 128 128 = 4077735440034797140658176 := by decide +kernel
private theorem rec_10_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 0) 256 128 = 1787498729454495987271680 := by decide +kernel
private theorem rec_10_11_2368_0_part3 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 0) 384 109 = 356835292391270660190102 := by decide +kernel
private theorem rec_10_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 0) 0 256 = 11314950723548906548744192 :=
  phaseBlock_append rec_10_11_2368_0_part0 rec_10_11_2368_0_part1 rfl rfl rfl
private theorem rec_10_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 0) 256 237 = 2144334021845766647461782 :=
  phaseBlock_append rec_10_11_2368_0_part2 rec_10_11_2368_0_part3 rfl rfl rfl
private theorem rec_10_11_2368_0_join2 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 0) 0 493 = 13459284745394673196205974 :=
  phaseBlock_append rec_10_11_2368_0_join0 rec_10_11_2368_0_join1 rfl rfl rfl

private theorem rec_10_11_2368_0 : fastPhase (bank 10 11).shape 179798 2368 32 1 2 14 0 = 13459284745394673196205974 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_10_11_2368_0_join2

private theorem rec_10_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 1) 0 128 = 7209496570593746031153920 := by decide +kernel
private theorem rec_10_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 1) 128 128 = 4056587932292700057735936 := by decide +kernel
private theorem rec_10_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 1) 256 128 = 1773075505476575061349120 := by decide +kernel
private theorem rec_10_11_2368_1_part3 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 1) 384 109 = 349617122045997573505752 := by decide +kernel
private theorem rec_10_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 1) 0 256 = 11266084502886446088889856 :=
  phaseBlock_append rec_10_11_2368_1_part0 rec_10_11_2368_1_part1 rfl rfl rfl
private theorem rec_10_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 1) 256 237 = 2122692627522572634854872 :=
  phaseBlock_append rec_10_11_2368_1_part2 rec_10_11_2368_1_part3 rfl rfl rfl
private theorem rec_10_11_2368_1_join2 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2368 32 1 2 14 1) 0 493 = 13388777130409018723744728 :=
  phaseBlock_append rec_10_11_2368_1_join0 rec_10_11_2368_1_join1 rfl rfl rfl

private theorem rec_10_11_2368_1 : fastPhase (bank 10 11).shape 179798 2368 32 1 2 14 1 = 13388777130409018723744728 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_10_11_2368_1_join2

private theorem rec_10_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 0) 0 128 = 7237269675072566778425760 := by decide +kernel
private theorem rec_10_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 0) 128 128 = 4077754026410286394630560 := by decide +kernel
private theorem rec_10_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 0) 256 128 = 1787502421692748565008800 := by decide +kernel
private theorem rec_10_11_2369_0_part3 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 0) 384 109 = 356835341388557127170745 := by decide +kernel
private theorem rec_10_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 0) 0 256 = 11315023701482853173056320 :=
  phaseBlock_append rec_10_11_2369_0_part0 rec_10_11_2369_0_part1 rfl rfl rfl
private theorem rec_10_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 0) 256 237 = 2144337763081305692179545 :=
  phaseBlock_append rec_10_11_2369_0_part2 rec_10_11_2369_0_part3 rfl rfl rfl
private theorem rec_10_11_2369_0_join2 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 0) 0 493 = 13459361464564158865235865 :=
  phaseBlock_append rec_10_11_2369_0_join0 rec_10_11_2369_0_join1 rfl rfl rfl

private theorem rec_10_11_2369_0 : fastPhase (bank 10 11).shape 179798 2369 32 1 2 14 0 = 13459361464564158865235865 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_10_11_2369_0_join2

private theorem rec_10_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 1) 0 128 = 7209550678044806981919200 := by decide +kernel
private theorem rec_10_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 1) 128 128 = 4056606391370498056581600 := by decide +kernel
private theorem rec_10_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 1) 256 128 = 1773079158972122380452320 := by decide +kernel
private theorem rec_10_11_2369_1_part3 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 1) 384 109 = 349617170157071707975455 := by decide +kernel
private theorem rec_10_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 1) 0 256 = 11266157069415305038500800 :=
  phaseBlock_append rec_10_11_2369_1_part0 rec_10_11_2369_1_part1 rfl rfl rfl
private theorem rec_10_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 1) 256 237 = 2122696329129194088427775 :=
  phaseBlock_append rec_10_11_2369_1_part2 rec_10_11_2369_1_part3 rfl rfl rfl
private theorem rec_10_11_2369_1_join2 :
    phaseBlock (fastLayerG (bank 10 11).shape 179798 2369 32 1 2 14 1) 0 493 = 13388853398544499126928575 :=
  phaseBlock_append rec_10_11_2369_1_join0 rec_10_11_2369_1_join1 rfl rfl rfl

private theorem rec_10_11_2369_1 : fastPhase (bank 10 11).shape 179798 2369 32 1 2 14 1 = 13388853398544499126928575 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_10_11_2369_1_join2

theorem receipt_10_11 : Checked (bank 10 11) 32 2 14 := by
  refine checked_from_values (bank 10 11) 32 2 14
    (P3_7_1.checked (bank 10 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_11_2368_0 rec_10_11_2368_1 rec_10_11_2369_0 rec_10_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 0) 0 128 = 6572336469682965367925696 := by decide +kernel
private theorem rec_10_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 0) 128 128 = 3682267996993990274862016 := by decide +kernel
private theorem rec_10_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 0) 256 128 = 1604110432498012661607360 := by decide +kernel
private theorem rec_10_12_2368_0_part3 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 0) 384 109 = 318261309170318488582542 := by decide +kernel
private theorem rec_10_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 0) 0 256 = 10254604466676955642787712 :=
  phaseBlock_append rec_10_12_2368_0_part0 rec_10_12_2368_0_part1 rfl rfl rfl
private theorem rec_10_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 0) 256 237 = 1922371741668331150189902 :=
  phaseBlock_append rec_10_12_2368_0_part2 rec_10_12_2368_0_part3 rfl rfl rfl
private theorem rec_10_12_2368_0_join2 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 0) 0 493 = 12176976208345286792977614 :=
  phaseBlock_append rec_10_12_2368_0_join0 rec_10_12_2368_0_join1 rfl rfl rfl

private theorem rec_10_12_2368_0 : fastPhase (bank 10 12).shape 179798 2368 31 1 2 14 0 = 12176976208345286792977614 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_10_12_2368_0_join2

private theorem rec_10_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 1) 0 128 = 6546890339203306226644800 := by decide +kernel
private theorem rec_10_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 1) 128 128 = 3663001189609960064309056 := by decide +kernel
private theorem rec_10_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 1) 256 128 = 1591086344039764544304960 := by decide +kernel
private theorem rec_10_12_2368_1_part3 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 1) 384 109 = 311810502870674183437002 := by decide +kernel
private theorem rec_10_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 1) 0 256 = 10209891528813266290953856 :=
  phaseBlock_append rec_10_12_2368_1_part0 rec_10_12_2368_1_part1 rfl rfl rfl
private theorem rec_10_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 1) 256 237 = 1902896846910438727741962 :=
  phaseBlock_append rec_10_12_2368_1_part2 rec_10_12_2368_1_part3 rfl rfl rfl
private theorem rec_10_12_2368_1_join2 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2368 31 1 2 14 1) 0 493 = 12112788375723705018695818 :=
  phaseBlock_append rec_10_12_2368_1_join0 rec_10_12_2368_1_join1 rfl rfl rfl

private theorem rec_10_12_2368_1 : fastPhase (bank 10 12).shape 179798 2368 31 1 2 14 1 = 12112788375723705018695818 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_10_12_2368_1_join2

private theorem rec_10_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 0) 0 128 = 6572385969884372301245280 := by decide +kernel
private theorem rec_10_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 0) 128 128 = 3682284835802410815093600 := by decide +kernel
private theorem rec_10_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 0) 256 128 = 1604113768290713359682400 := by decide +kernel
private theorem rec_10_12_2369_0_part3 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 0) 384 109 = 318261356881552953213675 := by decide +kernel
private theorem rec_10_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 0) 0 256 = 10254670805686783116338880 :=
  phaseBlock_append rec_10_12_2369_0_part0 rec_10_12_2369_0_part1 rfl rfl rfl
private theorem rec_10_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 0) 256 237 = 1922375125172266312896075 :=
  phaseBlock_append rec_10_12_2369_0_part2 rec_10_12_2369_0_part3 rfl rfl rfl
private theorem rec_10_12_2369_0_join2 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 0) 0 493 = 12177045930859049429234955 :=
  phaseBlock_append rec_10_12_2369_0_join0 rec_10_12_2369_0_join1 rfl rfl rfl

private theorem rec_10_12_2369_0 : fastPhase (bank 10 12).shape 179798 2369 31 1 2 14 0 = 12177045930859049429234955 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_10_12_2369_0_join2

private theorem rec_10_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 1) 0 128 = 6546939578867614845357600 := by decide +kernel
private theorem rec_10_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 1) 128 128 = 3663017912372573760798240 := by decide +kernel
private theorem rec_10_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 1) 256 128 = 1591089644704430061956640 := by decide +kernel
private theorem rec_10_12_2369_1_part3 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 1) 384 109 = 311810549703511074767865 := by decide +kernel
private theorem rec_10_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 1) 0 256 = 10209957491240188606155840 :=
  phaseBlock_append rec_10_12_2369_1_part0 rec_10_12_2369_1_part1 rfl rfl rfl
private theorem rec_10_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 1) 256 237 = 1902900194407941136724505 :=
  phaseBlock_append rec_10_12_2369_1_part2 rec_10_12_2369_1_part3 rfl rfl rfl
private theorem rec_10_12_2369_1_join2 :
    phaseBlock (fastLayerG (bank 10 12).shape 179798 2369 31 1 2 14 1) 0 493 = 12112857685648129742880345 :=
  phaseBlock_append rec_10_12_2369_1_join0 rec_10_12_2369_1_join1 rfl rfl rfl

private theorem rec_10_12_2369_1 : fastPhase (bank 10 12).shape 179798 2369 31 1 2 14 1 = 12112857685648129742880345 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_10_12_2369_1_join2

theorem receipt_10_12 : Checked (bank 10 12) 31 2 14 := by
  refine checked_from_values (bank 10 12) 31 2 14
    (P3_7_1.checked (bank 10 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_12_2368_0 rec_10_12_2368_1 rec_10_12_2369_0 rec_10_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 0 128 = 29408282951933223539010624 := by decide +kernel
private theorem rec_10_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 128 128 = 19781316996134263581346880 := by decide +kernel
private theorem rec_10_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 256 128 = 12051094940649314962222144 := by decide +kernel
private theorem rec_10_13_2368_0_part3 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 384 128 = 6198489149510662105779264 := by decide +kernel
private theorem rec_10_13_2368_0_part4 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 512 128 = 2131720966403307638352960 := by decide +kernel
private theorem rec_10_13_2368_0_part5 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 640 38 = 95525055477661759368692 := by decide +kernel
private theorem rec_10_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 128 256 = 31832411936783578543569024 :=
  phaseBlock_append rec_10_13_2368_0_part1 rec_10_13_2368_0_part2 rfl rfl rfl
private theorem rec_10_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 0 384 = 61240694888716802082579648 :=
  phaseBlock_append rec_10_13_2368_0_part0 rec_10_13_2368_0_join0 rfl rfl rfl
private theorem rec_10_13_2368_0_join2 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 512 166 = 2227246021880969397721652 :=
  phaseBlock_append rec_10_13_2368_0_part4 rec_10_13_2368_0_part5 rfl rfl rfl
private theorem rec_10_13_2368_0_join3 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 384 294 = 8425735171391631503500916 :=
  phaseBlock_append rec_10_13_2368_0_part3 rec_10_13_2368_0_join2 rfl rfl rfl
private theorem rec_10_13_2368_0_join4 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 0) 0 678 = 69666430060108433586080564 :=
  phaseBlock_append rec_10_13_2368_0_join1 rec_10_13_2368_0_join3 rfl rfl rfl

private theorem rec_10_13_2368_0 : fastPhase (bank 10 13).shape 179798 2368 44 1 2 14 0 = 69666430060108433586080564 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_10_13_2368_0_join4

private theorem rec_10_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 0 128 = 29326588611636832930300864 := by decide +kernel
private theorem rec_10_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 128 128 = 19714026911356246995002304 := by decide +kernel
private theorem rec_10_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 256 128 = 11998445791703489507083200 := by decide +kernel
private theorem rec_10_13_2368_1_part3 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 384 128 = 6160092846025210820502464 := by decide +kernel
private theorem rec_10_13_2368_1_part4 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 512 128 = 2106656163165883095614400 := by decide +kernel
private theorem rec_10_13_2368_1_part5 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 640 38 = 90459301750969159567072 := by decide +kernel
private theorem rec_10_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 128 256 = 31712472703059736502085504 :=
  phaseBlock_append rec_10_13_2368_1_part1 rec_10_13_2368_1_part2 rfl rfl rfl
private theorem rec_10_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 0 384 = 61039061314696569432386368 :=
  phaseBlock_append rec_10_13_2368_1_part0 rec_10_13_2368_1_join0 rfl rfl rfl
private theorem rec_10_13_2368_1_join2 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 512 166 = 2197115464916852255181472 :=
  phaseBlock_append rec_10_13_2368_1_part4 rec_10_13_2368_1_part5 rfl rfl rfl
private theorem rec_10_13_2368_1_join3 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 384 294 = 8357208310942063075683936 :=
  phaseBlock_append rec_10_13_2368_1_part3 rec_10_13_2368_1_join2 rfl rfl rfl
private theorem rec_10_13_2368_1_join4 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2368 44 1 2 14 1) 0 678 = 69396269625638632508070304 :=
  phaseBlock_append rec_10_13_2368_1_join1 rec_10_13_2368_1_join3 rfl rfl rfl

private theorem rec_10_13_2368_1 : fastPhase (bank 10 13).shape 179798 2368 44 1 2 14 1 = 69396269625638632508070304 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_10_13_2368_1_join4

private theorem rec_10_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 0 128 = 29408514981922539408385920 := by decide +kernel
private theorem rec_10_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 128 128 = 19781428440923179228899200 := by decide +kernel
private theorem rec_10_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 256 128 = 12051138746130685987022720 := by decide +kernel
private theorem rec_10_13_2369_0_part3 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 384 128 = 6198500684758516045457280 := by decide +kernel
private theorem rec_10_13_2369_0_part4 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 512 128 = 2131721655133525995808640 := by decide +kernel
private theorem rec_10_13_2369_0_part5 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 640 38 = 95524981976391441548360 := by decide +kernel
private theorem rec_10_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 128 256 = 31832567187053865215921920 :=
  phaseBlock_append rec_10_13_2369_0_part1 rec_10_13_2369_0_part2 rfl rfl rfl
private theorem rec_10_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 0 384 = 61241082168976404624307840 :=
  phaseBlock_append rec_10_13_2369_0_part0 rec_10_13_2369_0_join0 rfl rfl rfl
private theorem rec_10_13_2369_0_join2 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 512 166 = 2227246637109917437357000 :=
  phaseBlock_append rec_10_13_2369_0_part4 rec_10_13_2369_0_part5 rfl rfl rfl
private theorem rec_10_13_2369_0_join3 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 384 294 = 8425747321868433482814280 :=
  phaseBlock_append rec_10_13_2369_0_part3 rec_10_13_2369_0_join2 rfl rfl rfl
private theorem rec_10_13_2369_0_join4 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 0) 0 678 = 69666829490844838107122120 :=
  phaseBlock_append rec_10_13_2369_0_join1 rec_10_13_2369_0_join3 rfl rfl rfl

private theorem rec_10_13_2369_0 : fastPhase (bank 10 13).shape 179798 2369 44 1 2 14 0 = 69666829490844838107122120 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_10_13_2369_0_join4

private theorem rec_10_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 0 128 = 29326819762160550769796160 := by decide +kernel
private theorem rec_10_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 128 128 = 19714137850695193570804800 := by decide +kernel
private theorem rec_10_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 256 128 = 11998489344995377664746560 := by decide +kernel
private theorem rec_10_13_2369_1_part3 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 384 128 = 6160104286152628752106560 := by decide +kernel
private theorem rec_10_13_2369_1_part4 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 512 128 = 2106656839859898314433600 := by decide +kernel
private theorem rec_10_13_2369_1_part5 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 640 38 = 90459232217769209746830 := by decide +kernel
private theorem rec_10_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 128 256 = 31712627195690571235551360 :=
  phaseBlock_append rec_10_13_2369_1_part1 rec_10_13_2369_1_part2 rfl rfl rfl
private theorem rec_10_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 0 384 = 61039446957851122005347520 :=
  phaseBlock_append rec_10_13_2369_1_part0 rec_10_13_2369_1_join0 rfl rfl rfl
private theorem rec_10_13_2369_1_join2 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 512 166 = 2197116072077667524180430 :=
  phaseBlock_append rec_10_13_2369_1_part4 rec_10_13_2369_1_part5 rfl rfl rfl
private theorem rec_10_13_2369_1_join3 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 384 294 = 8357220358230296276286990 :=
  phaseBlock_append rec_10_13_2369_1_part3 rec_10_13_2369_1_join2 rfl rfl rfl
private theorem rec_10_13_2369_1_join4 :
    phaseBlock (fastLayerG (bank 10 13).shape 179798 2369 44 1 2 14 1) 0 678 = 69396667316081418281634510 :=
  phaseBlock_append rec_10_13_2369_1_join1 rec_10_13_2369_1_join3 rfl rfl rfl

private theorem rec_10_13_2369_1 : fastPhase (bank 10 13).shape 179798 2369 44 1 2 14 1 = 69396667316081418281634510 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_10_13_2369_1_join4

theorem receipt_10_13 : Checked (bank 10 13) 44 2 14 := by
  refine checked_from_values (bank 10 13) 44 2 14
    (P3_7_1.checked (bank 10 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_13_2368_0 rec_10_13_2368_1 rec_10_13_2369_0 rec_10_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 0 128 = 282862785032338569265956224 := by decide +kernel
private theorem rec_10_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 128 128 = 218782315353918261787739520 := by decide +kernel
private theorem rec_10_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 256 128 = 161987641093720381051848064 := by decide +kernel
private theorem rec_10_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 384 128 = 112898515194715153056187776 := by decide +kernel
private theorem rec_10_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 512 128 = 71769041497655038231594368 := by decide +kernel
private theorem rec_10_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 640 128 = 38699266293856126439245184 := by decide +kernel
private theorem rec_10_14_2368_0_part6 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 768 128 = 13646769877979531968071040 := by decide +kernel
private theorem rec_10_14_2368_0_part7 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 896 29 = 424829293211047990942614 := by decide +kernel
private theorem rec_10_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 0 256 = 501645100386256831053695744 :=
  phaseBlock_append rec_10_14_2368_0_part0 rec_10_14_2368_0_part1 rfl rfl rfl
private theorem rec_10_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 256 256 = 274886156288435534108035840 :=
  phaseBlock_append rec_10_14_2368_0_part2 rec_10_14_2368_0_part3 rfl rfl rfl
private theorem rec_10_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 0 512 = 776531256674692365161731584 :=
  phaseBlock_append rec_10_14_2368_0_join0 rec_10_14_2368_0_join1 rfl rfl rfl
private theorem rec_10_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 512 256 = 110468307791511164670839552 :=
  phaseBlock_append rec_10_14_2368_0_part4 rec_10_14_2368_0_part5 rfl rfl rfl
private theorem rec_10_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 768 157 = 14071599171190579959013654 :=
  phaseBlock_append rec_10_14_2368_0_part6 rec_10_14_2368_0_part7 rfl rfl rfl
private theorem rec_10_14_2368_0_join5 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 512 413 = 124539906962701744629853206 :=
  phaseBlock_append rec_10_14_2368_0_join3 rec_10_14_2368_0_join4 rfl rfl rfl
private theorem rec_10_14_2368_0_join6 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 0) 0 925 = 901071163637394109791584790 :=
  phaseBlock_append rec_10_14_2368_0_join2 rec_10_14_2368_0_join5 rfl rfl rfl

private theorem rec_10_14_2368_0 : fastPhase (bank 10 14).shape 179798 2368 76 1 2 14 0 = 901071163637394109791584790 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_10_14_2368_0_join6

private theorem rec_10_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 0 128 = 282340737555499170324393344 := by decide +kernel
private theorem rec_10_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 128 128 = 218313702408473968327454080 := by decide +kernel
private theorem rec_10_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 256 128 = 161576661269533537905945984 := by decide +kernel
private theorem rec_10_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 384 128 = 112548004826649951688289664 := by decide +kernel
private theorem rec_10_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 512 128 = 71480566181422620340039040 := by decide +kernel
private theorem rec_10_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 640 128 = 38473212401859687561293184 := by decide +kernel
private theorem rec_10_14_2368_1_part6 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 768 128 = 13482436075159425084108160 := by decide +kernel
private theorem rec_10_14_2368_1_part7 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 896 29 = 396016838582745406072284 := by decide +kernel
private theorem rec_10_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 0 256 = 500654439963973138651847424 :=
  phaseBlock_append rec_10_14_2368_1_part0 rec_10_14_2368_1_part1 rfl rfl rfl
private theorem rec_10_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 256 256 = 274124666096183489594235648 :=
  phaseBlock_append rec_10_14_2368_1_part2 rec_10_14_2368_1_part3 rfl rfl rfl
private theorem rec_10_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 0 512 = 774779106060156628246083072 :=
  phaseBlock_append rec_10_14_2368_1_join0 rec_10_14_2368_1_join1 rfl rfl rfl
private theorem rec_10_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 512 256 = 109953778583282307901332224 :=
  phaseBlock_append rec_10_14_2368_1_part4 rec_10_14_2368_1_part5 rfl rfl rfl
private theorem rec_10_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 768 157 = 13878452913742170490180444 :=
  phaseBlock_append rec_10_14_2368_1_part6 rec_10_14_2368_1_part7 rfl rfl rfl
private theorem rec_10_14_2368_1_join5 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 512 413 = 123832231497024478391512668 :=
  phaseBlock_append rec_10_14_2368_1_join3 rec_10_14_2368_1_join4 rfl rfl rfl
private theorem rec_10_14_2368_1_join6 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2368 76 1 2 14 1) 0 925 = 898611337557181106637595740 :=
  phaseBlock_append rec_10_14_2368_1_join2 rec_10_14_2368_1_join5 rfl rfl rfl

private theorem rec_10_14_2368_1 : fastPhase (bank 10 14).shape 179798 2368 76 1 2 14 1 = 898611337557181106637595740 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_10_14_2368_1_join6

private theorem rec_10_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 0 128 = 282865060466592850914767904 := by decide +kernel
private theorem rec_10_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 128 128 = 218783702180895369250874400 := by decide +kernel
private theorem rec_10_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 256 128 = 161988415298955057299018784 := by decide +kernel
private theorem rec_10_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 384 128 = 112898893297254382917944352 := by decide +kernel
private theorem rec_10_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 512 128 = 71769187524940626202178592 := by decide +kernel
private theorem rec_10_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 640 128 = 38699298403180256847127584 := by decide +kernel
private theorem rec_10_14_2369_0_part6 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 768 128 = 13646766624513311514170400 := by decide +kernel
private theorem rec_10_14_2369_0_part7 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 896 29 = 424828868337576340803249 := by decide +kernel
private theorem rec_10_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 0 256 = 501648762647488220165642304 :=
  phaseBlock_append rec_10_14_2369_0_part0 rec_10_14_2369_0_part1 rfl rfl rfl
private theorem rec_10_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 256 256 = 274887308596209440216963136 :=
  phaseBlock_append rec_10_14_2369_0_part2 rec_10_14_2369_0_part3 rfl rfl rfl
private theorem rec_10_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 0 512 = 776536071243697660382605440 :=
  phaseBlock_append rec_10_14_2369_0_join0 rec_10_14_2369_0_join1 rfl rfl rfl
private theorem rec_10_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 512 256 = 110468485928120883049306176 :=
  phaseBlock_append rec_10_14_2369_0_part4 rec_10_14_2369_0_part5 rfl rfl rfl
private theorem rec_10_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 768 157 = 14071595492850887854973649 :=
  phaseBlock_append rec_10_14_2369_0_part6 rec_10_14_2369_0_part7 rfl rfl rfl
private theorem rec_10_14_2369_0_join5 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 512 413 = 124540081420971770904279825 :=
  phaseBlock_append rec_10_14_2369_0_join3 rec_10_14_2369_0_join4 rfl rfl rfl
private theorem rec_10_14_2369_0_join6 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 0) 0 925 = 901076152664669431286885265 :=
  phaseBlock_append rec_10_14_2369_0_join2 rec_10_14_2369_0_join5 rfl rfl rfl

private theorem rec_10_14_2369_0 : fastPhase (bank 10 14).shape 179798 2369 76 1 2 14 0 = 901076152664669431286885265 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_10_14_2369_0_join6

private theorem rec_10_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 0 128 = 282343007092056011303897184 := by decide +kernel
private theorem rec_10_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 128 128 = 218315085147457107897243744 := by decide +kernel
private theorem rec_10_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 256 128 = 161577432808440241496746080 := by decide +kernel
private theorem rec_10_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 384 128 = 112548381342555333363529824 := by decide +kernel
private theorem rec_10_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 512 128 = 71480711403505142546663520 := by decide +kernel
private theorem rec_10_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 640 128 = 38473244230499643248253024 := by decide +kernel
private theorem rec_10_14_2369_1_part6 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 768 128 = 13482432847610402188535904 := by decide +kernel
private theorem rec_10_14_2369_1_part7 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 896 29 = 396016442787705649380135 := by decide +kernel
private theorem rec_10_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 0 256 = 500658092239513119201140928 :=
  phaseBlock_append rec_10_14_2369_1_part0 rec_10_14_2369_1_part1 rfl rfl rfl
private theorem rec_10_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 256 256 = 274125814150995574860275904 :=
  phaseBlock_append rec_10_14_2369_1_part2 rec_10_14_2369_1_part3 rfl rfl rfl
private theorem rec_10_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 0 512 = 774783906390508694061416832 :=
  phaseBlock_append rec_10_14_2369_1_join0 rec_10_14_2369_1_join1 rfl rfl rfl
private theorem rec_10_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 512 256 = 109953955634004785794916544 :=
  phaseBlock_append rec_10_14_2369_1_part4 rec_10_14_2369_1_part5 rfl rfl rfl
private theorem rec_10_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 768 157 = 13878449290398107837916039 :=
  phaseBlock_append rec_10_14_2369_1_part6 rec_10_14_2369_1_part7 rfl rfl rfl
private theorem rec_10_14_2369_1_join5 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 512 413 = 123832404924402893632832583 :=
  phaseBlock_append rec_10_14_2369_1_join3 rec_10_14_2369_1_join4 rfl rfl rfl
private theorem rec_10_14_2369_1_join6 :
    phaseBlock (fastLayerG (bank 10 14).shape 179798 2369 76 1 2 14 1) 0 925 = 898616311314911587694249415 :=
  phaseBlock_append rec_10_14_2369_1_join2 rec_10_14_2369_1_join5 rfl rfl rfl

private theorem rec_10_14_2369_1 : fastPhase (bank 10 14).shape 179798 2369 76 1 2 14 1 = 898616311314911587694249415 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_10_14_2369_1_join6

theorem receipt_10_14 : Checked (bank 10 14) 76 2 14 := by
  refine checked_from_values (bank 10 14) 76 2 14
    (P3_7_1.checked (bank 10 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_14_2368_0 rec_10_14_2368_1 rec_10_14_2369_0 rec_10_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 0 128 = 1233537720492572603686488960 := by decide +kernel
private theorem rec_10_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 128 128 = 1029781633714502850086062976 := by decide +kernel
private theorem rec_10_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 256 128 = 842734632739575460357868416 := by decide +kernel
private theorem rec_10_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 384 128 = 673050311405667241979399040 := by decide +kernel
private theorem rec_10_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 512 128 = 521170417910174455502572416 := by decide +kernel
private theorem rec_10_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 640 128 = 387336446362794209551141760 := by decide +kernel
private theorem rec_10_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 768 128 = 271601228338305855818107776 := by decide +kernel
private theorem rec_10_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 896 128 = 173840524429352384063130496 := by decide +kernel
private theorem rec_10_15_2368_0_part8 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 1024 128 = 93764615799221817109941120 := by decide +kernel
private theorem rec_10_15_2368_0_part9 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 1152 128 = 30929895734628605843753856 := by decide +kernel
private theorem rec_10_15_2368_0_part10 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 1280 14 = 287678381435434933382208 := by decide +kernel
private theorem rec_10_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 0 256 = 2263319354207075453772551936 :=
  phaseBlock_append rec_10_15_2368_0_part0 rec_10_15_2368_0_part1 rfl rfl rfl
private theorem rec_10_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 384 256 = 1194220729315841697481971456 :=
  phaseBlock_append rec_10_15_2368_0_part3 rec_10_15_2368_0_part4 rfl rfl rfl
private theorem rec_10_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 256 384 = 2036955362055417157839839872 :=
  phaseBlock_append rec_10_15_2368_0_part2 rec_10_15_2368_0_join1 rfl rfl rfl
private theorem rec_10_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 0 640 = 4300274716262492611612391808 :=
  phaseBlock_append rec_10_15_2368_0_join0 rec_10_15_2368_0_join2 rfl rfl rfl
private theorem rec_10_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 768 256 = 445441752767658239881238272 :=
  phaseBlock_append rec_10_15_2368_0_part6 rec_10_15_2368_0_part7 rfl rfl rfl
private theorem rec_10_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 640 384 = 832778199130452449432380032 :=
  phaseBlock_append rec_10_15_2368_0_part5 rec_10_15_2368_0_join4 rfl rfl rfl
private theorem rec_10_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 1152 142 = 31217574116064040777136064 :=
  phaseBlock_append rec_10_15_2368_0_part9 rec_10_15_2368_0_part10 rfl rfl rfl
private theorem rec_10_15_2368_0_join7 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 1024 270 = 124982189915285857887077184 :=
  phaseBlock_append rec_10_15_2368_0_part8 rec_10_15_2368_0_join6 rfl rfl rfl
private theorem rec_10_15_2368_0_join8 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 640 654 = 957760389045738307319457216 :=
  phaseBlock_append rec_10_15_2368_0_join5 rec_10_15_2368_0_join7 rfl rfl rfl
private theorem rec_10_15_2368_0_join9 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 0) 0 1294 = 5258035105308230918931849024 :=
  phaseBlock_append rec_10_15_2368_0_join3 rec_10_15_2368_0_join8 rfl rfl rfl

private theorem rec_10_15_2368_0 : fastPhase (bank 10 15).shape 179798 2368 105 1 2 14 0 = 5258035105308230918931849024 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_10_15_2368_0_join9

private theorem rec_10_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 0 128 = 1231900161987863750155343360 := by decide +kernel
private theorem rec_10_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 128 128 = 1028268257515163631738164736 := by decide +kernel
private theorem rec_10_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 256 128 = 841351815193287482401461760 := by decide +kernel
private theorem rec_10_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 384 128 = 671802698913062373174744576 := by decide +kernel
private theorem rec_10_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 512 128 = 520061018440679931766150656 := by decide +kernel
private theorem rec_10_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 640 128 = 386366720970477737559856640 := by decide +kernel
private theorem rec_10_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 768 128 = 270771182677720716613490176 := by decide +kernel
private theorem rec_10_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 896 128 = 173148800271382536655541760 := by decide +kernel
private theorem rec_10_15_2368_1_part8 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 1024 128 = 93208582546927002082776576 := by decide +kernel
private theorem rec_10_15_2368_1_part9 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 1152 128 = 30505741939089448957646336 := by decide +kernel
private theorem rec_10_15_2368_1_part10 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 1280 14 = 249088296642333140433532 := by decide +kernel
private theorem rec_10_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 0 256 = 2260168419503027381893508096 :=
  phaseBlock_append rec_10_15_2368_1_part0 rec_10_15_2368_1_part1 rfl rfl rfl
private theorem rec_10_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 384 256 = 1191863717353742304940895232 :=
  phaseBlock_append rec_10_15_2368_1_part3 rec_10_15_2368_1_part4 rfl rfl rfl
private theorem rec_10_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 256 384 = 2033215532547029787342356992 :=
  phaseBlock_append rec_10_15_2368_1_part2 rec_10_15_2368_1_join1 rfl rfl rfl
private theorem rec_10_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 0 640 = 4293383952050057169235865088 :=
  phaseBlock_append rec_10_15_2368_1_join0 rec_10_15_2368_1_join2 rfl rfl rfl
private theorem rec_10_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 768 256 = 443919982949103253269031936 :=
  phaseBlock_append rec_10_15_2368_1_part6 rec_10_15_2368_1_part7 rfl rfl rfl
private theorem rec_10_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 640 384 = 830286703919580990828888576 :=
  phaseBlock_append rec_10_15_2368_1_part5 rec_10_15_2368_1_join4 rfl rfl rfl
private theorem rec_10_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 1152 142 = 30754830235731782098079868 :=
  phaseBlock_append rec_10_15_2368_1_part9 rec_10_15_2368_1_part10 rfl rfl rfl
private theorem rec_10_15_2368_1_join7 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 1024 270 = 123963412782658784180856444 :=
  phaseBlock_append rec_10_15_2368_1_part8 rec_10_15_2368_1_join6 rfl rfl rfl
private theorem rec_10_15_2368_1_join8 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 640 654 = 954250116702239775009745020 :=
  phaseBlock_append rec_10_15_2368_1_join5 rec_10_15_2368_1_join7 rfl rfl rfl
private theorem rec_10_15_2368_1_join9 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2368 105 1 2 14 1) 0 1294 = 5247634068752296944245610108 :=
  phaseBlock_append rec_10_15_2368_1_join3 rec_10_15_2368_1_join8 rfl rfl rfl

private theorem rec_10_15_2368_1 : fastPhase (bank 10 15).shape 179798 2368 105 1 2 14 1 = 5247634068752296944245610108 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_10_15_2368_1_join9

private theorem rec_10_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 0 128 = 1233547940749179012920258688 := by decide +kernel
private theorem rec_10_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 128 128 = 1029788877990062198075453568 := by decide +kernel
private theorem rec_10_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 256 128 = 842739573399903476001452160 := by decide +kernel
private theorem rec_10_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 384 128 = 673053516433330038286643328 := by decide +kernel
private theorem rec_10_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 512 128 = 521172360058334872811548800 := by decide +kernel
private theorem rec_10_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 640 128 = 387337511955631141113917568 := by decide +kernel
private theorem rec_10_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 768 128 = 271601725718006555753820288 := by decide +kernel
private theorem rec_10_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 896 128 = 173840692049677757678743680 := by decide +kernel
private theorem rec_10_15_2369_0_part8 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 1024 128 = 93764629965644693588684928 := by decide +kernel
private theorem rec_10_15_2369_0_part9 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 1152 128 = 30929877991044993301246080 := by decide +kernel
private theorem rec_10_15_2369_0_part10 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 1280 14 = 287678066811758822918544 := by decide +kernel
private theorem rec_10_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 0 256 = 2263336818739241210995712256 :=
  phaseBlock_append rec_10_15_2369_0_part0 rec_10_15_2369_0_part1 rfl rfl rfl
private theorem rec_10_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 384 256 = 1194225876491664911098192128 :=
  phaseBlock_append rec_10_15_2369_0_part3 rec_10_15_2369_0_part4 rfl rfl rfl
private theorem rec_10_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 256 384 = 2036965449891568387099644288 :=
  phaseBlock_append rec_10_15_2369_0_part2 rec_10_15_2369_0_join1 rfl rfl rfl
private theorem rec_10_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 0 640 = 4300302268630809598095356544 :=
  phaseBlock_append rec_10_15_2369_0_join0 rec_10_15_2369_0_join2 rfl rfl rfl
private theorem rec_10_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 768 256 = 445442417767684313432563968 :=
  phaseBlock_append rec_10_15_2369_0_part6 rec_10_15_2369_0_part7 rfl rfl rfl
private theorem rec_10_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 640 384 = 832779929723315454546481536 :=
  phaseBlock_append rec_10_15_2369_0_part5 rec_10_15_2369_0_join4 rfl rfl rfl
private theorem rec_10_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 1152 142 = 31217556057856752124164624 :=
  phaseBlock_append rec_10_15_2369_0_part9 rec_10_15_2369_0_part10 rfl rfl rfl
private theorem rec_10_15_2369_0_join7 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 1024 270 = 124982186023501445712849552 :=
  phaseBlock_append rec_10_15_2369_0_part8 rec_10_15_2369_0_join6 rfl rfl rfl
private theorem rec_10_15_2369_0_join8 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 640 654 = 957762115746816900259331088 :=
  phaseBlock_append rec_10_15_2369_0_join5 rec_10_15_2369_0_join7 rfl rfl rfl
private theorem rec_10_15_2369_0_join9 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 0) 0 1294 = 5258064384377626498354687632 :=
  phaseBlock_append rec_10_15_2369_0_join3 rec_10_15_2369_0_join8 rfl rfl rfl

private theorem rec_10_15_2369_0 : fastPhase (bank 10 15).shape 179798 2369 105 1 2 14 0 = 5258064384377626498354687632 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_10_15_2369_0_join9

private theorem rec_10_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 0 128 = 1231910363254766021064581952 := by decide +kernel
private theorem rec_10_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 128 128 = 1028275487107373127910867776 := by decide +kernel
private theorem rec_10_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 256 128 = 841356744801788689005978432 := by decide +kernel
private theorem rec_10_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 384 128 = 671805895905815070846255936 := by decide +kernel
private theorem rec_10_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 512 128 = 520062955014108461772333888 := by decide +kernel
private theorem rec_10_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 640 128 = 386367782947533249334231872 := by decide +kernel
private theorem rec_10_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 768 128 = 270771677952516397656449856 := by decide +kernel
private theorem rec_10_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 896 128 = 173148966900401824803062592 := by decide +kernel
private theorem rec_10_15_2369_1_part8 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 1024 128 = 93208596486804780142814016 := by decide +kernel
private theorem rec_10_15_2369_1_part9 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 1152 128 = 30505724430966221714211648 := by decide +kernel
private theorem rec_10_15_2369_1_part10 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 1280 14 = 249088024350469894640778 := by decide +kernel
private theorem rec_10_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 0 256 = 2260185850362139148975449728 :=
  phaseBlock_append rec_10_15_2369_1_part0 rec_10_15_2369_1_part1 rfl rfl rfl
private theorem rec_10_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 384 256 = 1191868850919923532618589824 :=
  phaseBlock_append rec_10_15_2369_1_part3 rec_10_15_2369_1_part4 rfl rfl rfl
private theorem rec_10_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 256 384 = 2033225595721712221624568256 :=
  phaseBlock_append rec_10_15_2369_1_part2 rec_10_15_2369_1_join1 rfl rfl rfl
private theorem rec_10_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 0 640 = 4293411446083851370600017984 :=
  phaseBlock_append rec_10_15_2369_1_join0 rec_10_15_2369_1_join2 rfl rfl rfl
private theorem rec_10_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 768 256 = 443920644852918222459512448 :=
  phaseBlock_append rec_10_15_2369_1_part6 rec_10_15_2369_1_part7 rfl rfl rfl
private theorem rec_10_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 640 384 = 830288427800451471793744320 :=
  phaseBlock_append rec_10_15_2369_1_part5 rec_10_15_2369_1_join4 rfl rfl rfl
private theorem rec_10_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 1152 142 = 30754812455316691608852426 :=
  phaseBlock_append rec_10_15_2369_1_part9 rec_10_15_2369_1_part10 rfl rfl rfl
private theorem rec_10_15_2369_1_join7 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 1024 270 = 123963408942121471751666442 :=
  phaseBlock_append rec_10_15_2369_1_part8 rec_10_15_2369_1_join6 rfl rfl rfl
private theorem rec_10_15_2369_1_join8 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 640 654 = 954251836742572943545410762 :=
  phaseBlock_append rec_10_15_2369_1_join5 rec_10_15_2369_1_join7 rfl rfl rfl
private theorem rec_10_15_2369_1_join9 :
    phaseBlock (fastLayerG (bank 10 15).shape 179798 2369 105 1 2 14 1) 0 1294 = 5247663282826424314145428746 :=
  phaseBlock_append rec_10_15_2369_1_join3 rec_10_15_2369_1_join8 rfl rfl rfl

private theorem rec_10_15_2369_1 : fastPhase (bank 10 15).shape 179798 2369 105 1 2 14 1 = 5247663282826424314145428746 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_10_15_2369_1_join9

theorem receipt_10_15 : Checked (bank 10 15) 105 2 14 := by
  refine checked_from_values (bank 10 15) 105 2 14
    (P3_7_1.checked (bank 10 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_15_2368_0 rec_10_15_2368_1 rec_10_15_2369_0 rec_10_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_10_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 0 128 = 4712767990551724906631174304 := by decide +kernel
private theorem rec_10_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 128 128 = 4131480177835649879707175072 := by decide +kernel
private theorem rec_10_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 256 128 = 3586555283804555611444213920 := by decide +kernel
private theorem rec_10_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 384 128 = 3078806794479725186924193952 := by decide +kernel
private theorem rec_10_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 512 128 = 2608791533239445854581905568 := by decide +kernel
private theorem rec_10_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 640 128 = 2176821252371790421202438304 := by decide +kernel
private theorem rec_10_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 768 128 = 1782974224627398646918592672 := by decide +kernel
private theorem rec_10_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 896 128 = 1427106834772258640208292000 := by decide +kernel
private theorem rec_10_16_2368_0_part8 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 1024 128 = 1108865171140488252891994272 := by decide +kernel
private theorem rec_10_16_2368_0_part9 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 1152 128 = 827696617187116475130103968 := by decide +kernel
private theorem rec_10_16_2368_0_part10 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 1280 128 = 582861443040864830420383904 := by decide +kernel
private theorem rec_10_16_2368_0_part11 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 1408 128 = 373444397056928770595367072 := by decide +kernel
private theorem rec_10_16_2368_0_part12 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 1536 128 = 198366297369759070819768480 := by decide +kernel
private theorem rec_10_16_2368_0_part13 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 1664 123 = 56463273381916057466995745 := by decide +kernel
private theorem rec_10_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 128 256 = 7718035461640205491151388992 :=
  phaseBlock_append rec_10_16_2368_0_part1 rec_10_16_2368_0_part2 rfl rfl rfl
private theorem rec_10_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 0 384 = 12430803452191930397782563296 :=
  phaseBlock_append rec_10_16_2368_0_part0 rec_10_16_2368_0_join0 rfl rfl rfl
private theorem rec_10_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 384 256 = 5687598327719171041506099520 :=
  phaseBlock_append rec_10_16_2368_0_part3 rec_10_16_2368_0_part4 rfl rfl rfl
private theorem rec_10_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 640 256 = 3959795476999189068121030976 :=
  phaseBlock_append rec_10_16_2368_0_part5 rec_10_16_2368_0_part6 rfl rfl rfl
private theorem rec_10_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 384 512 = 9647393804718360109627130496 :=
  phaseBlock_append rec_10_16_2368_0_join2 rec_10_16_2368_0_join3 rfl rfl rfl
private theorem rec_10_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 0 896 = 22078197256910290507409693792 :=
  phaseBlock_append rec_10_16_2368_0_join1 rec_10_16_2368_0_join4 rfl rfl rfl
private theorem rec_10_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 1024 256 = 1936561788327604728022098240 :=
  phaseBlock_append rec_10_16_2368_0_part8 rec_10_16_2368_0_part9 rfl rfl rfl
private theorem rec_10_16_2368_0_join7 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 896 384 = 3363668623099863368230390240 :=
  phaseBlock_append rec_10_16_2368_0_part7 rec_10_16_2368_0_join6 rfl rfl rfl
private theorem rec_10_16_2368_0_join8 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 1280 256 = 956305840097793601015750976 :=
  phaseBlock_append rec_10_16_2368_0_part10 rec_10_16_2368_0_part11 rfl rfl rfl
private theorem rec_10_16_2368_0_join9 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 1536 251 = 254829570751675128286764225 :=
  phaseBlock_append rec_10_16_2368_0_part12 rec_10_16_2368_0_part13 rfl rfl rfl
private theorem rec_10_16_2368_0_join10 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 1280 507 = 1211135410849468729302515201 :=
  phaseBlock_append rec_10_16_2368_0_join8 rec_10_16_2368_0_join9 rfl rfl rfl
private theorem rec_10_16_2368_0_join11 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 896 891 = 4574804033949332097532905441 :=
  phaseBlock_append rec_10_16_2368_0_join7 rec_10_16_2368_0_join10 rfl rfl rfl
private theorem rec_10_16_2368_0_join12 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 0) 0 1787 = 26653001290859622604942599233 :=
  phaseBlock_append rec_10_16_2368_0_join5 rec_10_16_2368_0_join11 rfl rfl rfl

private theorem rec_10_16_2368_0 : fastPhase (bank 10 16).shape 179798 2368 138 1 2 14 0 = 26653001290859622604942599233 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_10_16_2368_0_join12

private theorem rec_10_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 0 128 = 4708135430114106151942982880 := by decide +kernel
private theorem rec_10_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 128 128 = 4127121078207298338036251872 := by decide +kernel
private theorem rec_10_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 256 128 = 3582477686191288183614106848 := by decide +kernel
private theorem rec_10_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 384 128 = 3075016652696148354912148704 := by decide +kernel
private theorem rec_10_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 512 128 = 2605292805224800785123069152 := by decide +kernel
private theorem rec_10_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 640 128 = 2173615991705798069394062560 := by decide +kernel
private theorem rec_10_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 768 128 = 1780062672046104859824237792 := by decide +kernel
private theorem rec_10_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 896 128 = 1424487509683879260462030048 := by decide +kernel
private theorem rec_10_16_2368_1_part8 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 1024 128 = 1106534963141254222302612704 := by decide +kernel
private theorem rec_10_16_2368_1_part9 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 1152 128 = 825650877577118938285309152 := by decide +kernel
private theorem rec_10_16_2368_1_part10 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 1280 128 = 581094076339900238291004640 := by decide +kernel
private theorem rec_10_16_2368_1_part11 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 1408 128 = 371947952520343984139558112 := by decide +kernel
private theorem rec_10_16_2368_1_part12 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 1536 128 = 197132060504296464587214048 := by decide +kernel
private theorem rec_10_16_2368_1_part13 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 1664 123 = 55515109189765268531259177 := by decide +kernel
private theorem rec_10_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 128 256 = 7709598764398586521650358720 :=
  phaseBlock_append rec_10_16_2368_1_part1 rec_10_16_2368_1_part2 rfl rfl rfl
private theorem rec_10_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 0 384 = 12417734194512692673593341600 :=
  phaseBlock_append rec_10_16_2368_1_part0 rec_10_16_2368_1_join0 rfl rfl rfl
private theorem rec_10_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 384 256 = 5680309457920949140035217856 :=
  phaseBlock_append rec_10_16_2368_1_part3 rec_10_16_2368_1_part4 rfl rfl rfl
private theorem rec_10_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 640 256 = 3953678663751902929218300352 :=
  phaseBlock_append rec_10_16_2368_1_part5 rec_10_16_2368_1_part6 rfl rfl rfl
private theorem rec_10_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 384 512 = 9633988121672852069253518208 :=
  phaseBlock_append rec_10_16_2368_1_join2 rec_10_16_2368_1_join3 rfl rfl rfl
private theorem rec_10_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 0 896 = 22051722316185544742846859808 :=
  phaseBlock_append rec_10_16_2368_1_join1 rec_10_16_2368_1_join4 rfl rfl rfl
private theorem rec_10_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 1024 256 = 1932185840718373160587921856 :=
  phaseBlock_append rec_10_16_2368_1_part8 rec_10_16_2368_1_part9 rfl rfl rfl
private theorem rec_10_16_2368_1_join7 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 896 384 = 3356673350402252421049951904 :=
  phaseBlock_append rec_10_16_2368_1_part7 rec_10_16_2368_1_join6 rfl rfl rfl
private theorem rec_10_16_2368_1_join8 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 1280 256 = 953042028860244222430562752 :=
  phaseBlock_append rec_10_16_2368_1_part10 rec_10_16_2368_1_part11 rfl rfl rfl
private theorem rec_10_16_2368_1_join9 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 1536 251 = 252647169694061733118473225 :=
  phaseBlock_append rec_10_16_2368_1_part12 rec_10_16_2368_1_part13 rfl rfl rfl
private theorem rec_10_16_2368_1_join10 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 1280 507 = 1205689198554305955549035977 :=
  phaseBlock_append rec_10_16_2368_1_join8 rec_10_16_2368_1_join9 rfl rfl rfl
private theorem rec_10_16_2368_1_join11 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 896 891 = 4562362548956558376598987881 :=
  phaseBlock_append rec_10_16_2368_1_join7 rec_10_16_2368_1_join10 rfl rfl rfl
private theorem rec_10_16_2368_1_join12 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2368 138 1 2 14 1) 0 1787 = 26614084865142103119445847689 :=
  phaseBlock_append rec_10_16_2368_1_join5 rec_10_16_2368_1_join11 rfl rfl rfl

private theorem rec_10_16_2368_1 : fastPhase (bank 10 16).shape 179798 2368 138 1 2 14 1 = 26614084865142103119445847689 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_10_16_2368_1_join12

private theorem rec_10_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 0 128 = 4712807960105091229996373600 := by decide +kernel
private theorem rec_10_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 128 128 = 4131511405266268329608513120 := by decide +kernel
private theorem rec_10_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 256 128 = 3586579236412038618368423520 := by decide +kernel
private theorem rec_10_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 384 128 = 3078824769569573193504188000 := by decide +kernel
private theorem rec_10_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 512 128 = 2608804669673033785581377120 := by decide +kernel
private theorem rec_10_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 640 128 = 2176830541762927135868143200 := by decide +kernel
private theorem rec_10_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 768 128 = 1782980522185459373700314720 := by decide +kernel
private theorem rec_10_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 896 128 = 1427110869791890393846490720 := by decide +kernel
private theorem rec_10_16_2369_0_part8 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 1024 128 = 1108867557137888233873135200 := by decide +kernel
private theorem rec_10_16_2369_0_part9 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 1152 128 = 827697861682883451509671520 := by decide +kernel
private theorem rec_10_16_2369_0_part10 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 1280 128 = 582861956989423502013576800 := by decide +kernel
private theorem rec_10_16_2369_0_part11 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 1408 128 = 373444503922527115535476320 := by decide +kernel
private theorem rec_10_16_2369_0_part12 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 1536 128 = 198366241849038674484237920 := by decide +kernel
private theorem rec_10_16_2369_0_part13 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 1664 123 = 56463229695889579350189955 := by decide +kernel
private theorem rec_10_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 128 256 = 7718090641678306947976936640 :=
  phaseBlock_append rec_10_16_2369_0_part1 rec_10_16_2369_0_part2 rfl rfl rfl
private theorem rec_10_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 0 384 = 12430898601783398177973310240 :=
  phaseBlock_append rec_10_16_2369_0_part0 rec_10_16_2369_0_join0 rfl rfl rfl
private theorem rec_10_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 384 256 = 5687629439242606979085565120 :=
  phaseBlock_append rec_10_16_2369_0_part3 rec_10_16_2369_0_part4 rfl rfl rfl
private theorem rec_10_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 640 256 = 3959811063948386509568457920 :=
  phaseBlock_append rec_10_16_2369_0_part5 rec_10_16_2369_0_part6 rfl rfl rfl
private theorem rec_10_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 384 512 = 9647440503190993488654023040 :=
  phaseBlock_append rec_10_16_2369_0_join2 rec_10_16_2369_0_join3 rfl rfl rfl
private theorem rec_10_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 0 896 = 22078339104974391666627333280 :=
  phaseBlock_append rec_10_16_2369_0_join1 rec_10_16_2369_0_join4 rfl rfl rfl
private theorem rec_10_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 1024 256 = 1936565418820771685382806720 :=
  phaseBlock_append rec_10_16_2369_0_part8 rec_10_16_2369_0_part9 rfl rfl rfl
private theorem rec_10_16_2369_0_join7 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 896 384 = 3363676288612662079229297440 :=
  phaseBlock_append rec_10_16_2369_0_part7 rec_10_16_2369_0_join6 rfl rfl rfl
private theorem rec_10_16_2369_0_join8 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 1280 256 = 956306460911950617549053120 :=
  phaseBlock_append rec_10_16_2369_0_part10 rec_10_16_2369_0_part11 rfl rfl rfl
private theorem rec_10_16_2369_0_join9 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 1536 251 = 254829471544928253834427875 :=
  phaseBlock_append rec_10_16_2369_0_part12 rec_10_16_2369_0_part13 rfl rfl rfl
private theorem rec_10_16_2369_0_join10 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 1280 507 = 1211135932456878871383480995 :=
  phaseBlock_append rec_10_16_2369_0_join8 rec_10_16_2369_0_join9 rfl rfl rfl
private theorem rec_10_16_2369_0_join11 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 896 891 = 4574812221069540950612778435 :=
  phaseBlock_append rec_10_16_2369_0_join7 rec_10_16_2369_0_join10 rfl rfl rfl
private theorem rec_10_16_2369_0_join12 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 0) 0 1787 = 26653151326043932617240111715 :=
  phaseBlock_append rec_10_16_2369_0_join5 rec_10_16_2369_0_join11 rfl rfl rfl

private theorem rec_10_16_2369_0 : fastPhase (bank 10 16).shape 179798 2369 138 1 2 14 0 = 26653151326043932617240111715 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_10_16_2369_0_join12

private theorem rec_10_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 0 128 = 4708175345103343233862570080 := by decide +kernel
private theorem rec_10_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 128 128 = 4127152260359457045254774880 := by decide +kernel
private theorem rec_10_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 256 128 = 3582501601711474724528369760 := by decide +kernel
private theorem rec_10_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 384 128 = 3075034597871214151882850400 := by decide +kernel
private theorem rec_10_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 512 128 = 2605305917970971866407358560 := by decide +kernel
private theorem rec_10_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 640 128 = 2173625262762877443445776480 := by decide +kernel
private theorem rec_10_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 768 128 = 1780068955818247871961821280 := by decide +kernel
private theorem rec_10_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 896 128 = 1424491534726941931904139360 := by decide +kernel
private theorem rec_10_16_2369_1_part8 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 1024 128 = 1106537342296714571571400800 := by decide +kernel
private theorem rec_10_16_2369_1_part9 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 1152 128 = 825652117752571284977393760 := by decide +kernel
private theorem rec_10_16_2369_1_part10 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 1280 128 = 581094587936122489216118880 := by decide +kernel
private theorem rec_10_16_2369_1_part11 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 1408 128 = 371948058504937901826883680 := by decide +kernel
private theorem rec_10_16_2369_1_part12 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 1536 128 = 197132005131900918159396960 := by decide +kernel
private theorem rec_10_16_2369_1_part13 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 1664 123 = 55515066253216458406586040 := by decide +kernel
private theorem rec_10_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 128 256 = 7709653862070931769783144640 :=
  phaseBlock_append rec_10_16_2369_1_part1 rec_10_16_2369_1_part2 rfl rfl rfl
private theorem rec_10_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 0 384 = 12417829207174275003645714720 :=
  phaseBlock_append rec_10_16_2369_1_part0 rec_10_16_2369_1_join0 rfl rfl rfl
private theorem rec_10_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 384 256 = 5680340515842186018290208960 :=
  phaseBlock_append rec_10_16_2369_1_part3 rec_10_16_2369_1_part4 rfl rfl rfl
private theorem rec_10_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 640 256 = 3953694218581125315407597760 :=
  phaseBlock_append rec_10_16_2369_1_part5 rec_10_16_2369_1_part6 rfl rfl rfl
private theorem rec_10_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 384 512 = 9634034734423311333697806720 :=
  phaseBlock_append rec_10_16_2369_1_join2 rec_10_16_2369_1_join3 rfl rfl rfl
private theorem rec_10_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 0 896 = 22051863941597586337343521440 :=
  phaseBlock_append rec_10_16_2369_1_join1 rec_10_16_2369_1_join4 rfl rfl rfl
private theorem rec_10_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 1024 256 = 1932189460049285856548794560 :=
  phaseBlock_append rec_10_16_2369_1_part8 rec_10_16_2369_1_part9 rfl rfl rfl
private theorem rec_10_16_2369_1_join7 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 896 384 = 3356680994776227788452933920 :=
  phaseBlock_append rec_10_16_2369_1_part7 rec_10_16_2369_1_join6 rfl rfl rfl
private theorem rec_10_16_2369_1_join8 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 1280 256 = 953042646441060391043002560 :=
  phaseBlock_append rec_10_16_2369_1_part10 rec_10_16_2369_1_part11 rfl rfl rfl
private theorem rec_10_16_2369_1_join9 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 1536 251 = 252647071385117376565983000 :=
  phaseBlock_append rec_10_16_2369_1_part12 rec_10_16_2369_1_part13 rfl rfl rfl
private theorem rec_10_16_2369_1_join10 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 1280 507 = 1205689717826177767608985560 :=
  phaseBlock_append rec_10_16_2369_1_join8 rec_10_16_2369_1_join9 rfl rfl rfl
private theorem rec_10_16_2369_1_join11 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 896 891 = 4562370712602405556061919480 :=
  phaseBlock_append rec_10_16_2369_1_join7 rec_10_16_2369_1_join10 rfl rfl rfl
private theorem rec_10_16_2369_1_join12 :
    phaseBlock (fastLayerG (bank 10 16).shape 179798 2369 138 1 2 14 1) 0 1787 = 26614234654199991893405440920 :=
  phaseBlock_append rec_10_16_2369_1_join5 rec_10_16_2369_1_join11 rfl rfl rfl

private theorem rec_10_16_2369_1 : fastPhase (bank 10 16).shape 179798 2369 138 1 2 14 1 = 26614234654199991893405440920 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_10_16_2369_1_join12

theorem receipt_10_16 : Checked (bank 10 16) 138 2 14 := by
  refine checked_from_values (bank 10 16) 138 2 14
    (P3_7_1.checked (bank 10 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_10_16_2368_0 rec_10_16_2368_1 rec_10_16_2369_0 rec_10_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect10_checked (i : Fin 17) :
    Checked (bank 10 i) (reserve i) (excess 10) (seed 10) := by
  fin_cases i
  · exact receipt_10_0
  · exact receipt_10_1
  · exact receipt_10_2
  · exact receipt_10_3
  · exact receipt_10_4
  · exact receipt_10_5
  · exact receipt_10_6
  · exact receipt_10_7
  · exact receipt_10_8
  · exact receipt_10_9
  · exact receipt_10_10
  · exact receipt_10_11
  · exact receipt_10_12
  · exact receipt_10_13
  · exact receipt_10_14
  · exact receipt_10_15
  · exact receipt_10_16

end Lower6961.Lo.RescueSource
