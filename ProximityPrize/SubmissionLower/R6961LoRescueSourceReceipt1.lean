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


private theorem rec_1_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2368 1 1 0 2 0) 0 128 = 66189241820170453669044224 := by decide +kernel
private theorem rec_1_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2368 1 1 0 2 0) 128 128 = 34901719402462489884166318 := by decide +kernel
private theorem rec_1_1_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2368 1 1 0 2 0) 256 114 = 9146122687107033435856666 := by decide +kernel
private theorem rec_1_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2368 1 1 0 2 0) 128 242 = 44047842089569523320022984 :=
  phaseBlock_append rec_1_1_2368_0_part1 rec_1_1_2368_0_part2 rfl rfl rfl
private theorem rec_1_1_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2368 1 1 0 2 0) 0 370 = 110237083909739976989067208 :=
  phaseBlock_append rec_1_1_2368_0_part0 rec_1_1_2368_0_join0 rfl rfl rfl

private theorem rec_1_1_2368_0 : fastPhase (bank 1 1).shape 179798 2368 1 1 0 2 0 = 110237083909739976989067208 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_1_1_2368_0_join1

private theorem rec_1_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2368 1 1 0 2 1) 0 128 = 65925782729485079928640512 := by decide +kernel
private theorem rec_1_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2368 1 1 0 2 1) 128 128 = 34681103658263198700882983 := by decide +kernel
private theorem rec_1_1_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2368 1 1 0 2 1) 256 114 = 8982516189047939723530585 := by decide +kernel
private theorem rec_1_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2368 1 1 0 2 1) 128 242 = 43663619847311138424413568 :=
  phaseBlock_append rec_1_1_2368_1_part1 rec_1_1_2368_1_part2 rfl rfl rfl
private theorem rec_1_1_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2368 1 1 0 2 1) 0 370 = 109589402576796218353054080 :=
  phaseBlock_append rec_1_1_2368_1_part0 rec_1_1_2368_1_join0 rfl rfl rfl

private theorem rec_1_1_2368_1 : fastPhase (bank 1 1).shape 179798 2368 1 1 0 2 1 = 109589402576796218353054080 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_1_1_2368_1_join1

private theorem rec_1_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2369 1 1 0 2 0) 0 128 = 66189814721721818346289376 := by decide +kernel
private theorem rec_1_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2369 1 1 0 2 0) 128 128 = 34901953397035262424923663 := by decide +kernel
private theorem rec_1_1_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2369 1 1 0 2 0) 256 114 = 9146166239845972179197998 := by decide +kernel
private theorem rec_1_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2369 1 1 0 2 0) 128 242 = 44048119636881234604121661 :=
  phaseBlock_append rec_1_1_2369_0_part1 rec_1_1_2369_0_part2 rfl rfl rfl
private theorem rec_1_1_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2369 1 1 0 2 0) 0 370 = 110237934358603052950411037 :=
  phaseBlock_append rec_1_1_2369_0_part0 rec_1_1_2369_0_join0 rfl rfl rfl

private theorem rec_1_1_2369_0 : fastPhase (bank 1 1).shape 179798 2369 1 1 0 2 0 = 110237934358603052950411037 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_1_1_2369_0_join1

private theorem rec_1_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2369 1 1 0 2 1) 0 128 = 65926353757834355538492960 := by decide +kernel
private theorem rec_1_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2369 1 1 0 2 1) 128 128 = 34681336386136105261472518 := by decide +kernel
private theorem rec_1_1_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2369 1 1 0 2 1) 256 114 = 8982559060440660507723483 := by decide +kernel
private theorem rec_1_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2369 1 1 0 2 1) 128 242 = 43663895446576765769196001 :=
  phaseBlock_append rec_1_1_2369_1_part1 rec_1_1_2369_1_part2 rfl rfl rfl
private theorem rec_1_1_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 1).shape 179798 2369 1 1 0 2 1) 0 370 = 109590249204411121307688961 :=
  phaseBlock_append rec_1_1_2369_1_part0 rec_1_1_2369_1_join0 rfl rfl rfl

private theorem rec_1_1_2369_1 : fastPhase (bank 1 1).shape 179798 2369 1 1 0 2 1 = 109590249204411121307688961 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_1_1_2369_1_join1

theorem receipt_1_1 : Checked (bank 1 1) 1 0 2 := by
  refine checked_from_values (bank 1 1) 1 0 2
    (P3_7_1.checked (bank 1 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_1_2368_0 rec_1_1_2368_1 rec_1_1_2369_0 rec_1_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 0) 0 128 = 137313071756720200016696448 := by decide +kernel
private theorem rec_1_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 0) 128 128 = 89324710340293133553833088 := by decide +kernel
private theorem rec_1_2_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 0) 256 128 = 47593302213191823944866703 := by decide +kernel
private theorem rec_1_2_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 0) 384 109 = 11994610401656570504942106 := by decide +kernel
private theorem rec_1_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 0) 0 256 = 226637782097013333570529536 :=
  phaseBlock_append rec_1_2_2368_0_part0 rec_1_2_2368_0_part1 rfl rfl rfl
private theorem rec_1_2_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 0) 256 237 = 59587912614848394449808809 :=
  phaseBlock_append rec_1_2_2368_0_part2 rec_1_2_2368_0_part3 rfl rfl rfl
private theorem rec_1_2_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 0) 0 493 = 286225694711861728020338345 :=
  phaseBlock_append rec_1_2_2368_0_join0 rec_1_2_2368_0_join1 rfl rfl rfl

private theorem rec_1_2_2368_0 : fastPhase (bank 1 2).shape 179798 2368 2 1 0 2 0 = 286225694711861728020338345 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_2_2368_0_join2

private theorem rec_1_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 1) 0 128 = 136917857572661470414684544 := by decide +kernel
private theorem rec_1_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 1) 128 128 = 88978474025942807298638208 := by decide +kernel
private theorem rec_1_2_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 1) 256 128 = 47292633022257047956613062 := by decide +kernel
private theorem rec_1_2_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 1) 384 109 = 11771969309373206105393121 := by decide +kernel
private theorem rec_1_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 1) 0 256 = 225896331598604277713322752 :=
  phaseBlock_append rec_1_2_2368_1_part0 rec_1_2_2368_1_part1 rfl rfl rfl
private theorem rec_1_2_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 1) 256 237 = 59064602331630254062006183 :=
  phaseBlock_append rec_1_2_2368_1_part2 rec_1_2_2368_1_part3 rfl rfl rfl
private theorem rec_1_2_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2368 2 1 0 2 1) 0 493 = 284960933930234531775328935 :=
  phaseBlock_append rec_1_2_2368_1_join0 rec_1_2_2368_1_join1 rfl rfl rfl

private theorem rec_1_2_2368_1 : fastPhase (bank 1 2).shape 179798 2368 2 1 0 2 1 = 284960933930234531775328935 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_2_2368_1_join2

private theorem rec_1_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 0) 0 128 = 137314285867729530778451232 := by decide +kernel
private theorem rec_1_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 0) 128 128 = 89325371202049278650166560 := by decide +kernel
private theorem rec_1_2_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 0) 256 128 = 47593580023797345142300817 := by decide +kernel
private theorem rec_1_2_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 0) 384 109 = 11994662563593070294924215 := by decide +kernel
private theorem rec_1_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 0) 0 256 = 226639657069778809428617792 :=
  phaseBlock_append rec_1_2_2369_0_part0 rec_1_2_2369_0_part1 rfl rfl rfl
private theorem rec_1_2_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 0) 256 237 = 59588242587390415437225032 :=
  phaseBlock_append rec_1_2_2369_0_part2 rec_1_2_2369_0_part3 rfl rfl rfl
private theorem rec_1_2_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 0) 0 493 = 286227899657169224865842824 :=
  phaseBlock_append rec_1_2_2369_0_join0 rec_1_2_2369_0_join1 rfl rfl rfl

private theorem rec_1_2_2369_0 : fastPhase (bank 1 2).shape 179798 2369 2 1 0 2 0 = 286227899657169224865842824 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_2_2369_0_join2

private theorem rec_1_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 1) 0 128 = 136919068817220843217450464 := by decide +kernel
private theorem rec_1_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 1) 128 128 = 88979132716475340461983200 := by decide +kernel
private theorem rec_1_2_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 1) 256 128 = 47292909288391804519473894 := by decide +kernel
private theorem rec_1_2_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 1) 384 109 = 11772020599147458993234780 := by decide +kernel
private theorem rec_1_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 1) 0 256 = 225898201533696183679433664 :=
  phaseBlock_append rec_1_2_2369_1_part0 rec_1_2_2369_1_part1 rfl rfl rfl
private theorem rec_1_2_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 1) 256 237 = 59064929887539263512708674 :=
  phaseBlock_append rec_1_2_2369_1_part2 rec_1_2_2369_1_part3 rfl rfl rfl
private theorem rec_1_2_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 2).shape 179798 2369 2 1 0 2 1) 0 493 = 284963131421235447192142338 :=
  phaseBlock_append rec_1_2_2369_1_join0 rec_1_2_2369_1_join1 rfl rfl rfl

private theorem rec_1_2_2369_1 : fastPhase (bank 1 2).shape 179798 2369 2 1 0 2 1 = 284963131421235447192142338 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_2_2369_1_join2

theorem receipt_1_2 : Checked (bank 1 2) 2 0 2 := by
  refine checked_from_values (bank 1 2) 2 0 2
    (P3_7_1.checked (bank 1 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_2_2368_0 rec_1_2_2368_1 rec_1_2_2369_0 rec_1_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 0) 0 128 = 174710971695204996523541504 := by decide +kernel
private theorem rec_1_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 0) 128 128 = 113698646780830799541371904 := by decide +kernel
private theorem rec_1_3_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 0) 256 128 = 60604200420334435674454393 := by decide +kernel
private theorem rec_1_3_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 0) 384 109 = 15278988106415382364319391 := by decide +kernel
private theorem rec_1_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 0) 0 256 = 288409618476035796064913408 :=
  phaseBlock_append rec_1_3_2368_0_part0 rec_1_3_2368_0_part1 rfl rfl rfl
private theorem rec_1_3_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 0) 256 237 = 75883188526749818038773784 :=
  phaseBlock_append rec_1_3_2368_0_part2 rec_1_3_2368_0_part3 rfl rfl rfl
private theorem rec_1_3_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 0) 0 493 = 364292807002785614103687192 :=
  phaseBlock_append rec_1_3_2368_0_join0 rec_1_3_2368_0_join1 rfl rfl rfl

private theorem rec_1_3_2368_0 : fastPhase (bank 1 3).shape 179798 2368 3 1 0 2 0 = 364292807002785614103687192 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_3_2368_0_join2

private theorem rec_1_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 1) 0 128 = 174208669693622714371811840 := by decide +kernel
private theorem rec_1_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 1) 128 128 = 113258289780936413720029696 := by decide +kernel
private theorem rec_1_3_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 1) 256 128 = 60221519583706580284240965 := by decide +kernel
private theorem rec_1_3_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 1) 384 109 = 14995415679131849546132118 := by decide +kernel
private theorem rec_1_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 1) 0 256 = 287466959474559128091841536 :=
  phaseBlock_append rec_1_3_2368_1_part0 rec_1_3_2368_1_part1 rfl rfl rfl
private theorem rec_1_3_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 1) 256 237 = 75216935262838429830373083 :=
  phaseBlock_append rec_1_3_2368_1_part2 rec_1_3_2368_1_part3 rfl rfl rfl
private theorem rec_1_3_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2368 3 1 0 2 1) 0 493 = 362683894737397557922214619 :=
  phaseBlock_append rec_1_3_2368_1_join0 rec_1_3_2368_1_join1 rfl rfl rfl

private theorem rec_1_3_2368_1 : fastPhase (bank 1 3).shape 179798 2368 3 1 0 2 1 = 362683894737397557922214619 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_3_2368_1_join2

private theorem rec_1_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 0) 0 128 = 174712513772480188707302880 := by decide +kernel
private theorem rec_1_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 0) 128 128 = 113699486134635670140730848 := by decide +kernel
private theorem rec_1_3_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 0) 256 128 = 60604553141411654507708052 := by decide +kernel
private theorem rec_1_3_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 0) 384 109 = 15279054280022467159424460 := by decide +kernel
private theorem rec_1_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 0) 0 256 = 288411999907115858848033728 :=
  phaseBlock_append rec_1_3_2369_0_part0 rec_1_3_2369_0_part1 rfl rfl rfl
private theorem rec_1_3_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 0) 256 237 = 75883607421434121667132512 :=
  phaseBlock_append rec_1_3_2369_0_part2 rec_1_3_2369_0_part3 rfl rfl rfl
private theorem rec_1_3_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 0) 0 493 = 364295607328549980515166240 :=
  phaseBlock_append rec_1_3_2369_0_join0 rec_1_3_2369_0_join1 rfl rfl rfl

private theorem rec_1_3_2369_0 : fastPhase (bank 1 3).shape 179798 2369 3 1 0 2 0 = 364295607328549980515166240 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_3_2369_0_join2

private theorem rec_1_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 1) 0 128 = 174210208135704995594641056 := by decide +kernel
private theorem rec_1_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 1) 128 128 = 113259126380331430109679264 := by decide +kernel
private theorem rec_1_3_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 1) 256 128 = 60221870345443082367042573 := by decide +kernel
private theorem rec_1_3_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 1) 384 109 = 14995480746900115638931419 := by decide +kernel
private theorem rec_1_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 1) 0 256 = 287469334516036425704320320 :=
  phaseBlock_append rec_1_3_2369_1_part0 rec_1_3_2369_1_part1 rfl rfl rfl
private theorem rec_1_3_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 1) 256 237 = 75217351092343198005973992 :=
  phaseBlock_append rec_1_3_2369_1_part2 rec_1_3_2369_1_part3 rfl rfl rfl
private theorem rec_1_3_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 3).shape 179798 2369 3 1 0 2 1) 0 493 = 362686685608379623710294312 :=
  phaseBlock_append rec_1_3_2369_1_join0 rec_1_3_2369_1_join1 rfl rfl rfl

private theorem rec_1_3_2369_1 : fastPhase (bank 1 3).shape 179798 2369 3 1 0 2 1 = 362686685608379623710294312 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_3_2369_1_join2

theorem receipt_1_3 : Checked (bank 1 3) 3 0 2 := by
  refine checked_from_values (bank 1 3) 3 0 2
    (P3_7_1.checked (bank 1 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_3_2368_0 rec_1_3_2368_1 rec_1_3_2369_0 rec_1_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 0) 0 128 = 229752969692120093622459648 := by decide +kernel
private theorem rec_1_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 0) 128 128 = 149579326154779445053299968 := by decide +kernel
private theorem rec_1_4_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 0) 256 128 = 79761273656909704994153080 := by decide +kernel
private theorem rec_1_4_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 0) 384 109 = 20115708572503757380473846 := by decide +kernel
private theorem rec_1_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 0) 0 256 = 379332295846899538675759616 :=
  phaseBlock_append rec_1_4_2368_0_part0 rec_1_4_2368_0_part1 rfl rfl rfl
private theorem rec_1_4_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 0) 256 237 = 99876982229413462374626926 :=
  phaseBlock_append rec_1_4_2368_0_part2 rec_1_4_2368_0_part3 rfl rfl rfl
private theorem rec_1_4_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 0) 0 493 = 479209278076313001050386542 :=
  phaseBlock_append rec_1_4_2368_0_join0 rec_1_4_2368_0_join1 rfl rfl rfl

private theorem rec_1_4_2368_0 : fastPhase (bank 1 4).shape 179798 2368 4 1 0 2 0 = 479209278076313001050386542 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_4_2368_0_join2

private theorem rec_1_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 1) 0 128 = 229093143581452186147960576 := by decide +kernel
private theorem rec_1_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 1) 128 128 = 149000471276415486202132224 := by decide +kernel
private theorem rec_1_4_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 1) 256 128 = 79257869188371540794613757 := by decide +kernel
private theorem rec_1_4_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 1) 384 109 = 19742411113806111217901085 := by decide +kernel
private theorem rec_1_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 1) 0 256 = 378093614857867672350092800 :=
  phaseBlock_append rec_1_4_2368_1_part0 rec_1_4_2368_1_part1 rfl rfl rfl
private theorem rec_1_4_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 1) 256 237 = 99000280302177652012514842 :=
  phaseBlock_append rec_1_4_2368_1_part2 rec_1_4_2368_1_part3 rfl rfl rfl
private theorem rec_1_4_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2368 4 1 0 2 1) 0 493 = 477093895160045324362607642 :=
  phaseBlock_append rec_1_4_2368_1_join0 rec_1_4_2368_1_join1 rfl rfl rfl

private theorem rec_1_4_2368_1 : fastPhase (bank 1 4).shape 179798 2368 4 1 0 2 1 = 477093895160045324362607642 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_4_2368_1_join2

private theorem rec_1_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 0) 0 128 = 229754994039977285729189088 := by decide +kernel
private theorem rec_1_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 0) 128 128 = 149580427973000061596880096 := by decide +kernel
private theorem rec_1_4_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 0) 256 128 = 79761736507066452918180465 := by decide +kernel
private theorem rec_1_4_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 0) 384 109 = 20115795338903326938951105 := by decide +kernel
private theorem rec_1_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 0) 0 256 = 379335422012977347326069184 :=
  phaseBlock_append rec_1_4_2369_0_part0 rec_1_4_2369_0_part1 rfl rfl rfl
private theorem rec_1_4_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 0) 256 237 = 99877531845969779857131570 :=
  phaseBlock_append rec_1_4_2369_0_part2 rec_1_4_2369_0_part3 rfl rfl rfl
private theorem rec_1_4_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 0) 0 493 = 479212953858947127183200754 :=
  phaseBlock_append rec_1_4_2369_0_join0 rec_1_4_2369_0_join1 rfl rfl rfl

private theorem rec_1_4_2369_0 : fastPhase (bank 1 4).shape 179798 2369 4 1 0 2 0 = 479212953858947127183200754 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_4_2369_0_join2

private theorem rec_1_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 1) 0 128 = 229095163164554208283028512 := by decide +kernel
private theorem rec_1_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 1) 128 128 = 149001569483181009524890656 := by decide +kernel
private theorem rec_1_4_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 1) 256 128 = 79258329469524174696779656 := by decide +kernel
private theorem rec_1_4_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 1) 384 109 = 19742496431048101185947976 := by decide +kernel
private theorem rec_1_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 1) 0 256 = 378096732647735217807919168 :=
  phaseBlock_append rec_1_4_2369_1_part0 rec_1_4_2369_1_part1 rfl rfl rfl
private theorem rec_1_4_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 1) 256 237 = 99000825900572275882727632 :=
  phaseBlock_append rec_1_4_2369_1_part2 rec_1_4_2369_1_part3 rfl rfl rfl
private theorem rec_1_4_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 4).shape 179798 2369 4 1 0 2 1) 0 493 = 477097558548307493690646800 :=
  phaseBlock_append rec_1_4_2369_1_join0 rec_1_4_2369_1_join1 rfl rfl rfl

private theorem rec_1_4_2369_1 : fastPhase (bank 1 4).shape 179798 2369 4 1 0 2 1 = 477097558548307493690646800 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_4_2369_1_join2

theorem receipt_1_4 : Checked (bank 1 4) 4 0 2 := by
  refine checked_from_values (bank 1 4) 4 0 2
    (P3_7_1.checked (bank 1 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_4_2368_0 rec_1_4_2368_1 rec_1_4_2369_0 rec_1_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 0) 0 128 = 315567066048740061937929536 := by decide +kernel
private theorem rec_1_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 0) 128 128 = 205531014251247933246270784 := by decide +kernel
private theorem rec_1_5_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 0) 256 128 = 109640451407107372790763415 := by decide +kernel
private theorem rec_1_5_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 0) 384 109 = 27660834586454199338659281 := by decide +kernel
private theorem rec_1_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 0) 0 256 = 521098080299987995184200320 :=
  phaseBlock_append rec_1_5_2368_0_part0 rec_1_5_2368_0_part1 rfl rfl rfl
private theorem rec_1_5_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 0) 256 237 = 137301285993561572129422696 :=
  phaseBlock_append rec_1_5_2368_0_part2 rec_1_5_2368_0_part3 rfl rfl rfl
private theorem rec_1_5_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 0) 0 493 = 658399366293549567313623016 :=
  phaseBlock_append rec_1_5_2368_0_join0 rec_1_5_2368_0_join1 rfl rfl rfl

private theorem rec_1_5_2368_0 : fastPhase (bank 1 5).shape 179798 2368 5 1 0 2 0 = 658399366293549567313623016 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_5_2368_0_join2

private theorem rec_1_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 1) 0 128 = 314661785407842810311072448 := by decide +kernel
private theorem rec_1_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 1) 128 128 = 204736276342080504430131904 := by decide +kernel
private theorem rec_1_5_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 1) 256 128 = 108948800574392987069070450 := by decide +kernel
private theorem rec_1_5_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 1) 384 109 = 27147577055251783364029428 := by decide +kernel
private theorem rec_1_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 1) 0 256 = 519398061749923314741204352 :=
  phaseBlock_append rec_1_5_2368_1_part0 rec_1_5_2368_1_part1 rfl rfl rfl
private theorem rec_1_5_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 1) 256 237 = 136096377629644770433099878 :=
  phaseBlock_append rec_1_5_2368_1_part2 rec_1_5_2368_1_part3 rfl rfl rfl
private theorem rec_1_5_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2368 5 1 0 2 1) 0 493 = 655494439379568085174304230 :=
  phaseBlock_append rec_1_5_2368_1_join0 rec_1_5_2368_1_join1 rfl rfl rfl

private theorem rec_1_5_2368_1 : fastPhase (bank 1 5).shape 179798 2368 5 1 0 2 1 = 655494439379568085174304230 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_5_2368_1_join2

private theorem rec_1_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 0) 0 128 = 315569841619691191608856224 := by decide +kernel
private theorem rec_1_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 0) 128 128 = 205532524895453387657002656 := by decide +kernel
private theorem rec_1_5_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 0) 256 128 = 109641085765676268980467119 := by decide +kernel
private theorem rec_1_5_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 0) 384 109 = 27660953409234375721995960 := by decide +kernel
private theorem rec_1_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 0) 0 256 = 521102366515144579265858880 :=
  phaseBlock_append rec_1_5_2369_0_part0 rec_1_5_2369_0_part1 rfl rfl rfl
private theorem rec_1_5_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 0) 256 237 = 137302039174910644702463079 :=
  phaseBlock_append rec_1_5_2369_0_part2 rec_1_5_2369_0_part3 rfl rfl rfl
private theorem rec_1_5_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 0) 0 493 = 658404405690055223968321959 :=
  phaseBlock_append rec_1_5_2369_0_join0 rec_1_5_2369_0_join1 rfl rfl rfl

private theorem rec_1_5_2369_0 : fastPhase (bank 1 5).shape 179798 2369 5 1 0 2 0 = 658404405690055223968321959 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_5_2369_0_join2

private theorem rec_1_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 1) 0 128 = 314664554455894479811805280 := by decide +kernel
private theorem rec_1_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 1) 128 128 = 204737782040646634161524832 := by decide +kernel
private theorem rec_1_5_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 1) 256 128 = 108949431414892480368204031 := by decide +kernel
private theorem rec_1_5_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 1) 384 109 = 27147693894589563337061663 := by decide +kernel
private theorem rec_1_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 1) 0 256 = 519402336496541113973330112 :=
  phaseBlock_append rec_1_5_2369_1_part0 rec_1_5_2369_1_part1 rfl rfl rfl
private theorem rec_1_5_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 1) 256 237 = 136097125309482043705265694 :=
  phaseBlock_append rec_1_5_2369_1_part2 rec_1_5_2369_1_part3 rfl rfl rfl
private theorem rec_1_5_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 5).shape 179798 2369 5 1 0 2 1) 0 493 = 655499461806023157678595806 :=
  phaseBlock_append rec_1_5_2369_1_join0 rec_1_5_2369_1_join1 rfl rfl rfl

private theorem rec_1_5_2369_1 : fastPhase (bank 1 5).shape 179798 2369 5 1 0 2 1 = 655499461806023157678595806 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_1_5_2369_1_join2

theorem receipt_1_5 : Checked (bank 1 5) 5 0 2 := by
  refine checked_from_values (bank 1 5) 5 0 2
    (P3_7_1.checked (bank 1 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_5_2368_0 rec_1_5_2368_1 rec_1_5_2369_0 rec_1_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 0 128 = 764913864985126204556895808 := by decide +kernel
private theorem rec_1_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 128 128 = 573042858106788062425531968 := by decide +kernel
private theorem rec_1_6_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 256 128 = 399212723856680184301320870 := by decide +kernel
private theorem rec_1_6_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 384 128 = 242508282576932311541123627 := by decide +kernel
private theorem rec_1_6_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 512 128 = 102021539001843845412938269 := by decide +kernel
private theorem rec_1_6_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 640 38 = 5523831358864299199053045 := by decide +kernel
private theorem rec_1_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 128 256 = 972255581963468246726852838 :=
  phaseBlock_append rec_1_6_2368_0_part1 rec_1_6_2368_0_part2 rfl rfl rfl
private theorem rec_1_6_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 0 384 = 1737169446948594451283748646 :=
  phaseBlock_append rec_1_6_2368_0_part0 rec_1_6_2368_0_join0 rfl rfl rfl
private theorem rec_1_6_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 512 166 = 107545370360708144611991314 :=
  phaseBlock_append rec_1_6_2368_0_part4 rec_1_6_2368_0_part5 rfl rfl rfl
private theorem rec_1_6_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 384 294 = 350053652937640456153114941 :=
  phaseBlock_append rec_1_6_2368_0_part3 rec_1_6_2368_0_join2 rfl rfl rfl
private theorem rec_1_6_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 0) 0 678 = 2087223099886234907436863587 :=
  phaseBlock_append rec_1_6_2368_0_join1 rec_1_6_2368_0_join3 rfl rfl rfl

private theorem rec_1_6_2368_0 : fastPhase (bank 1 6).shape 179798 2368 7 1 0 2 0 = 2087223099886234907436863587 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_6_2368_0_join4

private theorem rec_1_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 0 128 = 763363201996459934259455424 := by decide +kernel
private theorem rec_1_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 128 128 = 571631980582428830308582848 := by decide +kernel
private theorem rec_1_6_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 256 128 = 397934672873875046485129049 := by decide +kernel
private theorem rec_1_6_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 384 128 = 241356159637380209836995003 := by decide +kernel
private theorem rec_1_6_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 512 128 = 100988504167005221147837663 := by decide +kernel
private theorem rec_1_6_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 640 38 = 5239073643008721272554290 := by decide +kernel
private theorem rec_1_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 128 256 = 969566653456303876793711897 :=
  phaseBlock_append rec_1_6_2368_1_part1 rec_1_6_2368_1_part2 rfl rfl rfl
private theorem rec_1_6_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 0 384 = 1732929855452763811053167321 :=
  phaseBlock_append rec_1_6_2368_1_part0 rec_1_6_2368_1_join0 rfl rfl rfl
private theorem rec_1_6_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 512 166 = 106227577810013942420391953 :=
  phaseBlock_append rec_1_6_2368_1_part4 rec_1_6_2368_1_part5 rfl rfl rfl
private theorem rec_1_6_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 384 294 = 347583737447394152257386956 :=
  phaseBlock_append rec_1_6_2368_1_part3 rec_1_6_2368_1_join2 rfl rfl rfl
private theorem rec_1_6_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2368 7 1 0 2 1) 0 678 = 2080513592900157963310554277 :=
  phaseBlock_append rec_1_6_2368_1_join1 rec_1_6_2368_1_join3 rfl rfl rfl

private theorem rec_1_6_2368_1 : fastPhase (bank 1 6).shape 179798 2368 7 1 0 2 1 = 2080513592900157963310554277 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_6_2368_1_join4

private theorem rec_1_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 0 128 = 764920725629955045697870272 := by decide +kernel
private theorem rec_1_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 128 128 = 573047404869975597584955840 := by decide +kernel
private theorem rec_1_6_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 256 128 = 399215452641381727446899982 := by decide +kernel
private theorem rec_1_6_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 384 128 = 242509654618711214245775442 := by decide +kernel
private theorem rec_1_6_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 512 128 = 102021993428891845076035209 := by decide +kernel
private theorem rec_1_6_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 640 38 = 5523850723504397052282429 := by decide +kernel
private theorem rec_1_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 128 256 = 972262857511357325031855822 :=
  phaseBlock_append rec_1_6_2369_0_part1 rec_1_6_2369_0_part2 rfl rfl rfl
private theorem rec_1_6_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 0 384 = 1737183583141312370729726094 :=
  phaseBlock_append rec_1_6_2369_0_part0 rec_1_6_2369_0_join0 rfl rfl rfl
private theorem rec_1_6_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 512 166 = 107545844152396242128317638 :=
  phaseBlock_append rec_1_6_2369_0_part4 rec_1_6_2369_0_part5 rfl rfl rfl
private theorem rec_1_6_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 384 294 = 350055498771107456374093080 :=
  phaseBlock_append rec_1_6_2369_0_part3 rec_1_6_2369_0_join2 rfl rfl rfl
private theorem rec_1_6_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 0) 0 678 = 2087239081912419827103819174 :=
  phaseBlock_append rec_1_6_2369_0_join1 rec_1_6_2369_0_join3 rfl rfl rfl

private theorem rec_1_6_2369_0 : fastPhase (bank 1 6).shape 179798 2369 7 1 0 2 0 = 2087239081912419827103819174 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_6_2369_0_join4

private theorem rec_1_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 0 128 = 763370051269215718201832064 := by decide +kernel
private theorem rec_1_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 128 128 = 571636517975049021217895040 := by decide +kernel
private theorem rec_1_6_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 256 128 = 397937394142323903158065509 := by decide +kernel
private theorem rec_1_6_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 384 128 = 241357525889297699610376830 := by decide +kernel
private theorem rec_1_6_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 512 128 = 100988954385652064245080396 := by decide +kernel
private theorem rec_1_6_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 640 38 = 5239092040513407616436964 := by decide +kernel
private theorem rec_1_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 128 256 = 969573912117372924375960549 :=
  phaseBlock_append rec_1_6_2369_1_part1 rec_1_6_2369_1_part2 rfl rfl rfl
private theorem rec_1_6_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 0 384 = 1732943963386588642577792613 :=
  phaseBlock_append rec_1_6_2369_1_part0 rec_1_6_2369_1_join0 rfl rfl rfl
private theorem rec_1_6_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 512 166 = 106228046426165471861517360 :=
  phaseBlock_append rec_1_6_2369_1_part4 rec_1_6_2369_1_part5 rfl rfl rfl
private theorem rec_1_6_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 384 294 = 347585572315463171471894190 :=
  phaseBlock_append rec_1_6_2369_1_part3 rec_1_6_2369_1_join2 rfl rfl rfl
private theorem rec_1_6_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 6).shape 179798 2369 7 1 0 2 1) 0 678 = 2080529535702051814049686803 :=
  phaseBlock_append rec_1_6_2369_1_join1 rec_1_6_2369_1_join3 rfl rfl rfl

private theorem rec_1_6_2369_1 : fastPhase (bank 1 6).shape 179798 2369 7 1 0 2 1 = 2080529535702051814049686803 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_6_2369_1_join4

theorem receipt_1_6 : Checked (bank 1 6) 7 0 2 := by
  refine checked_from_values (bank 1 6) 7 0 2
    (P3_7_1.checked (bank 1 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_6_2368_0 rec_1_6_2368_1 rec_1_6_2369_0 rec_1_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 0 128 = 1386116624180048389376976576 := by decide +kernel
private theorem rec_1_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 128 128 = 1039092016722486998893610688 := by decide +kernel
private theorem rec_1_7_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 256 128 = 724353556040038419828711541 := by decide +kernel
private theorem rec_1_7_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 384 128 = 440301624007934059099621321 := by decide +kernel
private theorem rec_1_7_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 512 128 = 185345520327057729963214175 := by decide +kernel
private theorem rec_1_7_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 640 38 = 10039942141899765075032896 := by decide +kernel
private theorem rec_1_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 128 256 = 1763445572762525418722322229 :=
  phaseBlock_append rec_1_7_2368_0_part1 rec_1_7_2368_0_part2 rfl rfl rfl
private theorem rec_1_7_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 0 384 = 3149562196942573808099298805 :=
  phaseBlock_append rec_1_7_2368_0_part0 rec_1_7_2368_0_join0 rfl rfl rfl
private theorem rec_1_7_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 512 166 = 195385462468957495038247071 :=
  phaseBlock_append rec_1_7_2368_0_part4 rec_1_7_2368_0_part5 rfl rfl rfl
private theorem rec_1_7_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 384 294 = 635687086476891554137868392 :=
  phaseBlock_append rec_1_7_2368_0_part3 rec_1_7_2368_0_join2 rfl rfl rfl
private theorem rec_1_7_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 0) 0 678 = 3785249283419465362237167197 :=
  phaseBlock_append rec_1_7_2368_0_join1 rec_1_7_2368_0_join3 rfl rfl rfl

private theorem rec_1_7_2368_0 : fastPhase (bank 1 7).shape 179798 2368 10 1 0 2 0 = 3785249283419465362237167197 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_7_2368_0_join4

private theorem rec_1_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 0 128 = 1383313596864433741292003392 := by decide +kernel
private theorem rec_1_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 128 128 = 1036538904860043064096047168 := by decide +kernel
private theorem rec_1_7_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 256 128 = 722038213062779489295805281 := by decide +kernel
private theorem rec_1_7_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 384 128 = 438211982414477681388155996 := by decide +kernel
private theorem rec_1_7_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 512 128 = 183469588814463140412834913 := by decide +kernel
private theorem rec_1_7_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 640 38 = 9522407947147773341607813 := by decide +kernel
private theorem rec_1_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 128 256 = 1758577117922822553391852449 :=
  phaseBlock_append rec_1_7_2368_1_part1 rec_1_7_2368_1_part2 rfl rfl rfl
private theorem rec_1_7_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 0 384 = 3141890714787256294683855841 :=
  phaseBlock_append rec_1_7_2368_1_part0 rec_1_7_2368_1_join0 rfl rfl rfl
private theorem rec_1_7_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 512 166 = 192991996761610913754442726 :=
  phaseBlock_append rec_1_7_2368_1_part4 rec_1_7_2368_1_part5 rfl rfl rfl
private theorem rec_1_7_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 384 294 = 631203979176088595142598722 :=
  phaseBlock_append rec_1_7_2368_1_part3 rec_1_7_2368_1_join2 rfl rfl rfl
private theorem rec_1_7_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2368 10 1 0 2 1) 0 678 = 3773094693963344889826454563 :=
  phaseBlock_append rec_1_7_2368_1_join1 rec_1_7_2368_1_join3 rfl rfl rfl

private theorem rec_1_7_2368_1 : fastPhase (bank 1 7).shape 179798 2368 10 1 0 2 1 = 3773094693963344889826454563 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_7_2368_1_join4

private theorem rec_1_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 0 128 = 1386129009994657029727990656 := by decide +kernel
private theorem rec_1_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 128 128 = 1039100225344300977912378240 := by decide +kernel
private theorem rec_1_7_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 256 128 = 724358481276864890640685643 := by decide +kernel
private theorem rec_1_7_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 384 128 = 440304098635595608685019438 := by decide +kernel
private theorem rec_1_7_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 512 128 = 185346338749381512615497504 := by decide +kernel
private theorem rec_1_7_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 640 38 = 10039976944744569111234928 := by decide +kernel
private theorem rec_1_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 128 256 = 1763458706621165868553063883 :=
  phaseBlock_append rec_1_7_2369_0_part1 rec_1_7_2369_0_part2 rfl rfl rfl
private theorem rec_1_7_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 0 384 = 3149587716615822898281054539 :=
  phaseBlock_append rec_1_7_2369_0_part0 rec_1_7_2369_0_join0 rfl rfl rfl
private theorem rec_1_7_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 512 166 = 195386315694126081726732432 :=
  phaseBlock_append rec_1_7_2369_0_part4 rec_1_7_2369_0_part5 rfl rfl rfl
private theorem rec_1_7_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 384 294 = 635690414329721690411751870 :=
  phaseBlock_append rec_1_7_2369_0_part3 rec_1_7_2369_0_join2 rfl rfl rfl
private theorem rec_1_7_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 0) 0 678 = 3785278130945544588692806409 :=
  phaseBlock_append rec_1_7_2369_0_join1 rec_1_7_2369_0_join3 rfl rfl rfl

private theorem rec_1_7_2369_0 : fastPhase (bank 1 7).shape 179798 2369 10 1 0 2 0 = 3785278130945544588692806409 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_7_2369_0_join4

private theorem rec_1_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 0 128 = 1383325962219259937268410048 := by decide +kernel
private theorem rec_1_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 128 128 = 1036547096613250123514889920 := by decide +kernel
private theorem rec_1_7_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 256 128 = 722043124764666477216418569 := by decide +kernel
private theorem rec_1_7_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 384 128 = 438214446617216533943464601 := by decide +kernel
private theorem rec_1_7_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 512 128 = 183470399666010080739804784 := by decide +kernel
private theorem rec_1_7_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 640 38 = 9522441012488733132425305 := by decide +kernel
private theorem rec_1_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 128 256 = 1758590221377916600731308489 :=
  phaseBlock_append rec_1_7_2369_1_part1 rec_1_7_2369_1_part2 rfl rfl rfl
private theorem rec_1_7_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 0 384 = 3141916183597176537999718537 :=
  phaseBlock_append rec_1_7_2369_1_part0 rec_1_7_2369_1_join0 rfl rfl rfl
private theorem rec_1_7_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 512 166 = 192992840678498813872230089 :=
  phaseBlock_append rec_1_7_2369_1_part4 rec_1_7_2369_1_part5 rfl rfl rfl
private theorem rec_1_7_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 384 294 = 631207287295715347815694690 :=
  phaseBlock_append rec_1_7_2369_1_part3 rec_1_7_2369_1_join2 rfl rfl rfl
private theorem rec_1_7_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 7).shape 179798 2369 10 1 0 2 1) 0 678 = 3773123470892891885815413227 :=
  phaseBlock_append rec_1_7_2369_1_join1 rec_1_7_2369_1_join3 rfl rfl rfl

private theorem rec_1_7_2369_1 : fastPhase (bank 1 7).shape 179798 2369 10 1 0 2 1 = 3773123470892891885815413227 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_7_2369_1_join4

theorem receipt_1_7 : Checked (bank 1 7) 10 0 2 := by
  refine checked_from_values (bank 1 7) 10 0 2
    (P3_7_1.checked (bank 1 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_7_2368_0 rec_1_7_2368_1 rec_1_7_2369_0 rec_1_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 0 128 = 5563516040443896278939702976 := by decide +kernel
private theorem rec_1_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 128 128 = 4550847188636719655059240640 := by decide +kernel
private theorem rec_1_8_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 256 128 = 3607130178598297420621141696 := by decide +kernel
private theorem rec_1_8_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 384 128 = 2729879775975969204740763771 := by decide +kernel
private theorem rec_1_8_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 512 128 = 1916627140364213885086998712 := by decide +kernel
private theorem rec_1_8_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 640 128 = 1164913509262610206304561633 := by decide +kernel
private theorem rec_1_8_2368_0_part6 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 768 128 = 472286991815877518033577016 := by decide +kernel
private theorem rec_1_8_2368_0_part7 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 896 29 = 16654762645127312579610370 := by decide +kernel
private theorem rec_1_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 0 256 = 10114363229080615933998943616 :=
  phaseBlock_append rec_1_8_2368_0_part0 rec_1_8_2368_0_part1 rfl rfl rfl
private theorem rec_1_8_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 256 256 = 6337009954574266625361905467 :=
  phaseBlock_append rec_1_8_2368_0_part2 rec_1_8_2368_0_part3 rfl rfl rfl
private theorem rec_1_8_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 0 512 = 16451373183654882559360849083 :=
  phaseBlock_append rec_1_8_2368_0_join0 rec_1_8_2368_0_join1 rfl rfl rfl
private theorem rec_1_8_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 512 256 = 3081540649626824091391560345 :=
  phaseBlock_append rec_1_8_2368_0_part4 rec_1_8_2368_0_part5 rfl rfl rfl
private theorem rec_1_8_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 768 157 = 488941754461004830613187386 :=
  phaseBlock_append rec_1_8_2368_0_part6 rec_1_8_2368_0_part7 rfl rfl rfl
private theorem rec_1_8_2368_0_join5 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 512 413 = 3570482404087828922004747731 :=
  phaseBlock_append rec_1_8_2368_0_join3 rec_1_8_2368_0_join4 rfl rfl rfl
private theorem rec_1_8_2368_0_join6 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 0) 0 925 = 20021855587742711481365596814 :=
  phaseBlock_append rec_1_8_2368_0_join2 rec_1_8_2368_0_join5 rfl rfl rfl

private theorem rec_1_8_2368_0 : fastPhase (bank 1 8).shape 179798 2368 16 1 0 2 0 = 20021855587742711481365596814 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_1_8_2368_0_join6

private theorem rec_1_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 0 128 = 5555440610866685374159096640 := by decide +kernel
private theorem rec_1_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 128 128 = 4543302034966920151065160512 := by decide +kernel
private theorem rec_1_8_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 256 128 = 3600096451283845161459665728 := by decide +kernel
private theorem rec_1_8_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 384 128 = 2723338729738198093892648811 := by decide +kernel
private theorem rec_1_8_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 512 128 = 1910560125502824932064138405 := by decide +kernel
private theorem rec_1_8_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 640 128 = 1159301969099284151067080960 := by decide +kernel
private theorem rec_1_8_2368_1_part6 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 768 128 = 467112473073509237201250481 := by decide +kernel
private theorem rec_1_8_2368_1_part7 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 896 29 = 15541239014945823462411702 := by decide +kernel
private theorem rec_1_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 0 256 = 10098742645833605525224257152 :=
  phaseBlock_append rec_1_8_2368_1_part0 rec_1_8_2368_1_part1 rfl rfl rfl
private theorem rec_1_8_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 256 256 = 6323435181022043255352314539 :=
  phaseBlock_append rec_1_8_2368_1_part2 rec_1_8_2368_1_part3 rfl rfl rfl
private theorem rec_1_8_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 0 512 = 16422177826855648780576571691 :=
  phaseBlock_append rec_1_8_2368_1_join0 rec_1_8_2368_1_join1 rfl rfl rfl
private theorem rec_1_8_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 512 256 = 3069862094602109083131219365 :=
  phaseBlock_append rec_1_8_2368_1_part4 rec_1_8_2368_1_part5 rfl rfl rfl
private theorem rec_1_8_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 768 157 = 482653712088455060663662183 :=
  phaseBlock_append rec_1_8_2368_1_part6 rec_1_8_2368_1_part7 rfl rfl rfl
private theorem rec_1_8_2368_1_join5 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 512 413 = 3552515806690564143794881548 :=
  phaseBlock_append rec_1_8_2368_1_join3 rec_1_8_2368_1_join4 rfl rfl rfl
private theorem rec_1_8_2368_1_join6 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2368 16 1 0 2 1) 0 925 = 19974693633546212924371453239 :=
  phaseBlock_append rec_1_8_2368_1_join2 rec_1_8_2368_1_join5 rfl rfl rfl

private theorem rec_1_8_2368_1 : fastPhase (bank 1 8).shape 179798 2368 16 1 0 2 1 = 19974693633546212924371453239 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_1_8_2368_1_join6

private theorem rec_1_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 0 128 = 5563566351553806112029813216 := by decide +kernel
private theorem rec_1_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 128 128 = 4550884929645553143019960800 := by decide +kernel
private theorem rec_1_8_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 256 128 = 3607157264021098947769584096 := by decide +kernel
private theorem rec_1_8_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 384 128 = 2729898031644419588765601699 := by decide +kernel
private theorem rec_1_8_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 512 128 = 1916638288054988880383687281 := by decide +kernel
private theorem rec_1_8_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 640 128 = 1164919229755613456378665600 := by decide +kernel
private theorem rec_1_8_2369_0_part6 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 768 128 = 472288886471227580981182035 := by decide +kernel
private theorem rec_1_8_2369_0_part7 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 896 29 = 16654817954270902678424911 := by decide +kernel
private theorem rec_1_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 0 256 = 10114451281199359255049774016 :=
  phaseBlock_append rec_1_8_2369_0_part0 rec_1_8_2369_0_part1 rfl rfl rfl
private theorem rec_1_8_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 256 256 = 6337055295665518536535185795 :=
  phaseBlock_append rec_1_8_2369_0_part2 rec_1_8_2369_0_part3 rfl rfl rfl
private theorem rec_1_8_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 0 512 = 16451506576864877791584959811 :=
  phaseBlock_append rec_1_8_2369_0_join0 rec_1_8_2369_0_join1 rfl rfl rfl
private theorem rec_1_8_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 512 256 = 3081557517810602336762352881 :=
  phaseBlock_append rec_1_8_2369_0_part4 rec_1_8_2369_0_part5 rfl rfl rfl
private theorem rec_1_8_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 768 157 = 488943704425498483659606946 :=
  phaseBlock_append rec_1_8_2369_0_part6 rec_1_8_2369_0_part7 rfl rfl rfl
private theorem rec_1_8_2369_0_join5 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 512 413 = 3570501222236100820421959827 :=
  phaseBlock_append rec_1_8_2369_0_join3 rec_1_8_2369_0_join4 rfl rfl rfl
private theorem rec_1_8_2369_0_join6 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 0) 0 925 = 20022007799100978612006919638 :=
  phaseBlock_append rec_1_8_2369_0_join2 rec_1_8_2369_0_join5 rfl rfl rfl

private theorem rec_1_8_2369_0 : fastPhase (bank 1 8).shape 179798 2369 16 1 0 2 0 = 20022007799100978612006919638 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_1_8_2369_0_join6

private theorem rec_1_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 0 128 = 5555490862462298708480960928 := by decide +kernel
private theorem rec_1_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 128 128 = 4543339724114638293055265184 := by decide +kernel
private theorem rec_1_8_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 256 128 = 3600123492095303263958960544 := by decide +kernel
private theorem rec_1_8_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 384 128 = 2723356947653086028204489355 := by decide +kernel
private theorem rec_1_8_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 512 128 = 1910571241973654659341712850 := by decide +kernel
private theorem rec_1_8_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 640 128 = 1159307664513315285953990625 := by decide +kernel
private theorem rec_1_8_2369_1_part6 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 768 128 = 467114348379314072403130174 := by decide +kernel
private theorem rec_1_8_2369_1_part7 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 896 29 = 15541290694023585440142053 := by decide +kernel
private theorem rec_1_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 0 256 = 10098830586576937001536226112 :=
  phaseBlock_append rec_1_8_2369_1_part0 rec_1_8_2369_1_part1 rfl rfl rfl
private theorem rec_1_8_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 256 256 = 6323480439748389292163449899 :=
  phaseBlock_append rec_1_8_2369_1_part2 rec_1_8_2369_1_part3 rfl rfl rfl
private theorem rec_1_8_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 0 512 = 16422311026325326293699676011 :=
  phaseBlock_append rec_1_8_2369_1_join0 rec_1_8_2369_1_join1 rfl rfl rfl
private theorem rec_1_8_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 512 256 = 3069878906486969945295703475 :=
  phaseBlock_append rec_1_8_2369_1_part4 rec_1_8_2369_1_part5 rfl rfl rfl
private theorem rec_1_8_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 768 157 = 482655639073337657843272227 :=
  phaseBlock_append rec_1_8_2369_1_part6 rec_1_8_2369_1_part7 rfl rfl rfl
private theorem rec_1_8_2369_1_join5 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 512 413 = 3552534545560307603138975702 :=
  phaseBlock_append rec_1_8_2369_1_join3 rec_1_8_2369_1_join4 rfl rfl rfl
private theorem rec_1_8_2369_1_join6 :
    phaseBlock (fastLayerG (bank 1 8).shape 179798 2369 16 1 0 2 1) 0 925 = 19974845571885633896838651713 :=
  phaseBlock_append rec_1_8_2369_1_join2 rec_1_8_2369_1_join5 rfl rfl rfl

private theorem rec_1_8_2369_1 : fastPhase (bank 1 8).shape 179798 2369 16 1 0 2 1 = 19974845571885633896838651713 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_1_8_2369_1_join6

theorem receipt_1_8 : Checked (bank 1 8) 16 0 2 := by
  refine checked_from_values (bank 1 8) 16 0 2
    (P3_7_1.checked (bank 1 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_8_2368_0 rec_1_8_2368_1 rec_1_8_2369_0 rec_1_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 0 128 = 1386116624180048389376976576 := by decide +kernel
private theorem rec_1_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 128 128 = 1039092016722486998893610688 := by decide +kernel
private theorem rec_1_9_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 256 128 = 724353556040038419828711541 := by decide +kernel
private theorem rec_1_9_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 384 128 = 440301624007934059099621321 := by decide +kernel
private theorem rec_1_9_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 512 128 = 185345520327057729963214175 := by decide +kernel
private theorem rec_1_9_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 640 38 = 10039942141899765075032896 := by decide +kernel
private theorem rec_1_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 128 256 = 1763445572762525418722322229 :=
  phaseBlock_append rec_1_9_2368_0_part1 rec_1_9_2368_0_part2 rfl rfl rfl
private theorem rec_1_9_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 0 384 = 3149562196942573808099298805 :=
  phaseBlock_append rec_1_9_2368_0_part0 rec_1_9_2368_0_join0 rfl rfl rfl
private theorem rec_1_9_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 512 166 = 195385462468957495038247071 :=
  phaseBlock_append rec_1_9_2368_0_part4 rec_1_9_2368_0_part5 rfl rfl rfl
private theorem rec_1_9_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 384 294 = 635687086476891554137868392 :=
  phaseBlock_append rec_1_9_2368_0_part3 rec_1_9_2368_0_join2 rfl rfl rfl
private theorem rec_1_9_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 0) 0 678 = 3785249283419465362237167197 :=
  phaseBlock_append rec_1_9_2368_0_join1 rec_1_9_2368_0_join3 rfl rfl rfl

private theorem rec_1_9_2368_0 : fastPhase (bank 1 9).shape 179798 2368 10 1 0 2 0 = 3785249283419465362237167197 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_9_2368_0_join4

private theorem rec_1_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 0 128 = 1383313596864433741292003392 := by decide +kernel
private theorem rec_1_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 128 128 = 1036538904860043064096047168 := by decide +kernel
private theorem rec_1_9_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 256 128 = 722038213062779489295805281 := by decide +kernel
private theorem rec_1_9_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 384 128 = 438211982414477681388155996 := by decide +kernel
private theorem rec_1_9_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 512 128 = 183469588814463140412834913 := by decide +kernel
private theorem rec_1_9_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 640 38 = 9522407947147773341607813 := by decide +kernel
private theorem rec_1_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 128 256 = 1758577117922822553391852449 :=
  phaseBlock_append rec_1_9_2368_1_part1 rec_1_9_2368_1_part2 rfl rfl rfl
private theorem rec_1_9_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 0 384 = 3141890714787256294683855841 :=
  phaseBlock_append rec_1_9_2368_1_part0 rec_1_9_2368_1_join0 rfl rfl rfl
private theorem rec_1_9_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 512 166 = 192991996761610913754442726 :=
  phaseBlock_append rec_1_9_2368_1_part4 rec_1_9_2368_1_part5 rfl rfl rfl
private theorem rec_1_9_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 384 294 = 631203979176088595142598722 :=
  phaseBlock_append rec_1_9_2368_1_part3 rec_1_9_2368_1_join2 rfl rfl rfl
private theorem rec_1_9_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2368 10 1 0 2 1) 0 678 = 3773094693963344889826454563 :=
  phaseBlock_append rec_1_9_2368_1_join1 rec_1_9_2368_1_join3 rfl rfl rfl

private theorem rec_1_9_2368_1 : fastPhase (bank 1 9).shape 179798 2368 10 1 0 2 1 = 3773094693963344889826454563 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_9_2368_1_join4

private theorem rec_1_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 0 128 = 1386129009994657029727990656 := by decide +kernel
private theorem rec_1_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 128 128 = 1039100225344300977912378240 := by decide +kernel
private theorem rec_1_9_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 256 128 = 724358481276864890640685643 := by decide +kernel
private theorem rec_1_9_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 384 128 = 440304098635595608685019438 := by decide +kernel
private theorem rec_1_9_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 512 128 = 185346338749381512615497504 := by decide +kernel
private theorem rec_1_9_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 640 38 = 10039976944744569111234928 := by decide +kernel
private theorem rec_1_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 128 256 = 1763458706621165868553063883 :=
  phaseBlock_append rec_1_9_2369_0_part1 rec_1_9_2369_0_part2 rfl rfl rfl
private theorem rec_1_9_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 0 384 = 3149587716615822898281054539 :=
  phaseBlock_append rec_1_9_2369_0_part0 rec_1_9_2369_0_join0 rfl rfl rfl
private theorem rec_1_9_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 512 166 = 195386315694126081726732432 :=
  phaseBlock_append rec_1_9_2369_0_part4 rec_1_9_2369_0_part5 rfl rfl rfl
private theorem rec_1_9_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 384 294 = 635690414329721690411751870 :=
  phaseBlock_append rec_1_9_2369_0_part3 rec_1_9_2369_0_join2 rfl rfl rfl
private theorem rec_1_9_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 0) 0 678 = 3785278130945544588692806409 :=
  phaseBlock_append rec_1_9_2369_0_join1 rec_1_9_2369_0_join3 rfl rfl rfl

private theorem rec_1_9_2369_0 : fastPhase (bank 1 9).shape 179798 2369 10 1 0 2 0 = 3785278130945544588692806409 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_9_2369_0_join4

private theorem rec_1_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 0 128 = 1383325962219259937268410048 := by decide +kernel
private theorem rec_1_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 128 128 = 1036547096613250123514889920 := by decide +kernel
private theorem rec_1_9_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 256 128 = 722043124764666477216418569 := by decide +kernel
private theorem rec_1_9_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 384 128 = 438214446617216533943464601 := by decide +kernel
private theorem rec_1_9_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 512 128 = 183470399666010080739804784 := by decide +kernel
private theorem rec_1_9_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 640 38 = 9522441012488733132425305 := by decide +kernel
private theorem rec_1_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 128 256 = 1758590221377916600731308489 :=
  phaseBlock_append rec_1_9_2369_1_part1 rec_1_9_2369_1_part2 rfl rfl rfl
private theorem rec_1_9_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 0 384 = 3141916183597176537999718537 :=
  phaseBlock_append rec_1_9_2369_1_part0 rec_1_9_2369_1_join0 rfl rfl rfl
private theorem rec_1_9_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 512 166 = 192992840678498813872230089 :=
  phaseBlock_append rec_1_9_2369_1_part4 rec_1_9_2369_1_part5 rfl rfl rfl
private theorem rec_1_9_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 384 294 = 631207287295715347815694690 :=
  phaseBlock_append rec_1_9_2369_1_part3 rec_1_9_2369_1_join2 rfl rfl rfl
private theorem rec_1_9_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 9).shape 179798 2369 10 1 0 2 1) 0 678 = 3773123470892891885815413227 :=
  phaseBlock_append rec_1_9_2369_1_join1 rec_1_9_2369_1_join3 rfl rfl rfl

private theorem rec_1_9_2369_1 : fastPhase (bank 1 9).shape 179798 2369 10 1 0 2 1 = 3773123470892891885815413227 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_1_9_2369_1_join4

theorem receipt_1_9 : Checked (bank 1 9) 10 0 2 := by
  refine checked_from_values (bank 1 9) 10 0 2
    (P3_7_1.checked (bank 1 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_9_2368_0 rec_1_9_2368_1 rec_1_9_2369_0 rec_1_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 0 128 = 11585762427706340347600726912 := by decide +kernel
private theorem rec_1_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 128 128 = 9481312236638502918289746816 := by decide +kernel
private theorem rec_1_10_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 256 128 = 7518634662938043872588819328 := by decide +kernel
private theorem rec_1_10_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 384 128 = 5692742786758065712208097021 := by decide +kernel
private theorem rec_1_10_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 512 128 = 3998675108816229205767731325 := by decide +kernel
private theorem rec_1_10_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 640 128 = 2431481381521251895407279443 := by decide +kernel
private theorem rec_1_10_2368_0_part6 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 768 128 = 986217159794611495934033069 := by decide +kernel
private theorem rec_1_10_2368_0_part7 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 896 29 = 34789300055011240324208623 := by decide +kernel
private theorem rec_1_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 0 256 = 21067074664344843265890473728 :=
  phaseBlock_append rec_1_10_2368_0_part0 rec_1_10_2368_0_part1 rfl rfl rfl
private theorem rec_1_10_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 256 256 = 13211377449696109584796916349 :=
  phaseBlock_append rec_1_10_2368_0_part2 rec_1_10_2368_0_part3 rfl rfl rfl
private theorem rec_1_10_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 0 512 = 34278452114040952850687390077 :=
  phaseBlock_append rec_1_10_2368_0_join0 rec_1_10_2368_0_join1 rfl rfl rfl
private theorem rec_1_10_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 512 256 = 6430156490337481101175010768 :=
  phaseBlock_append rec_1_10_2368_0_part4 rec_1_10_2368_0_part5 rfl rfl rfl
private theorem rec_1_10_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 768 157 = 1021006459849622736258241692 :=
  phaseBlock_append rec_1_10_2368_0_part6 rec_1_10_2368_0_part7 rfl rfl rfl
private theorem rec_1_10_2368_0_join5 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 512 413 = 7451162950187103837433252460 :=
  phaseBlock_append rec_1_10_2368_0_join3 rec_1_10_2368_0_join4 rfl rfl rfl
private theorem rec_1_10_2368_0_join6 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 0) 0 925 = 41729615064228056688120642537 :=
  phaseBlock_append rec_1_10_2368_0_join2 rec_1_10_2368_0_join5 rfl rfl rfl

private theorem rec_1_10_2368_0 : fastPhase (bank 1 10).shape 179798 2368 20 1 0 2 0 = 41729615064228056688120642537 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_1_10_2368_0_join6

private theorem rec_1_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 0 128 = 11568987544703202909241468032 := by decide +kernel
private theorem rec_1_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 128 128 = 9465626770212671349956846720 := by decide +kernel
private theorem rec_1_10_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 256 128 = 7504000832882340439514768512 := by decide +kernel
private theorem rec_1_10_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 384 128 = 5679122961616631264050627877 := by decide +kernel
private theorem rec_1_10_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 512 128 = 3986031787204722260785022742 := by decide +kernel
private theorem rec_1_10_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 640 128 = 2419777188605960127161061160 := by decide +kernel
private theorem rec_1_10_2368_1_part6 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 768 128 = 975414868529173900099335576 := by decide +kernel
private theorem rec_1_10_2368_1_part7 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 896 29 = 32463395412436583681257787 := by decide +kernel
private theorem rec_1_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 0 256 = 21034614314915874259198314752 :=
  phaseBlock_append rec_1_10_2368_1_part0 rec_1_10_2368_1_part1 rfl rfl rfl
private theorem rec_1_10_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 256 256 = 13183123794498971703565396389 :=
  phaseBlock_append rec_1_10_2368_1_part2 rec_1_10_2368_1_part3 rfl rfl rfl
private theorem rec_1_10_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 0 512 = 34217738109414845962763711141 :=
  phaseBlock_append rec_1_10_2368_1_join0 rec_1_10_2368_1_join1 rfl rfl rfl
private theorem rec_1_10_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 512 256 = 6405808975810682387946083902 :=
  phaseBlock_append rec_1_10_2368_1_part4 rec_1_10_2368_1_part5 rfl rfl rfl
private theorem rec_1_10_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 768 157 = 1007878263941610483780593363 :=
  phaseBlock_append rec_1_10_2368_1_part6 rec_1_10_2368_1_part7 rfl rfl rfl
private theorem rec_1_10_2368_1_join5 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 512 413 = 7413687239752292871726677265 :=
  phaseBlock_append rec_1_10_2368_1_join3 rec_1_10_2368_1_join4 rfl rfl rfl
private theorem rec_1_10_2368_1_join6 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2368 20 1 0 2 1) 0 925 = 41631425349167138834490388406 :=
  phaseBlock_append rec_1_10_2368_1_join2 rec_1_10_2368_1_join5 rfl rfl rfl

private theorem rec_1_10_2368_1 : fastPhase (bank 1 10).shape 179798 2368 20 1 0 2 1 = 41631425349167138834490388406 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_1_10_2368_1_join6

private theorem rec_1_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 0 128 = 11585866819739987659312548448 := by decide +kernel
private theorem rec_1_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 128 128 = 9481390549971912034846300768 := by decide +kernel
private theorem rec_1_10_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 256 128 = 7518690862059116496893667936 := by decide +kernel
private theorem rec_1_10_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 384 128 = 5692780655429351136692989289 := by decide +kernel
private theorem rec_1_10_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 512 128 = 3998698220621912237658327960 := by decide +kernel
private theorem rec_1_10_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 640 128 = 2431493231431197416473025046 := by decide +kernel
private theorem rec_1_10_2369_0_part6 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 768 128 = 986221078633512131629787514 := by decide +kernel
private theorem rec_1_10_2369_0_part7 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 896 29 = 34789414244011227430785876 := by decide +kernel
private theorem rec_1_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 0 256 = 21067257369711899694158849216 :=
  phaseBlock_append rec_1_10_2369_0_part0 rec_1_10_2369_0_part1 rfl rfl rfl
private theorem rec_1_10_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 256 256 = 13211471517488467633586657225 :=
  phaseBlock_append rec_1_10_2369_0_part2 rec_1_10_2369_0_part3 rfl rfl rfl
private theorem rec_1_10_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 0 512 = 34278728887200367327745506441 :=
  phaseBlock_append rec_1_10_2369_0_join0 rec_1_10_2369_0_join1 rfl rfl rfl
private theorem rec_1_10_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 512 256 = 6430191452053109654131353006 :=
  phaseBlock_append rec_1_10_2369_0_part4 rec_1_10_2369_0_part5 rfl rfl rfl
private theorem rec_1_10_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 768 157 = 1021010492877523359060573390 :=
  phaseBlock_append rec_1_10_2369_0_part6 rec_1_10_2369_0_part7 rfl rfl rfl
private theorem rec_1_10_2369_0_join5 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 512 413 = 7451201944930633013191926396 :=
  phaseBlock_append rec_1_10_2369_0_join3 rec_1_10_2369_0_join4 rfl rfl rfl
private theorem rec_1_10_2369_0_join6 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 0) 0 925 = 41729930832131000340937432837 :=
  phaseBlock_append rec_1_10_2369_0_join2 rec_1_10_2369_0_join5 rfl rfl rfl

private theorem rec_1_10_2369_0 : fastPhase (bank 1 10).shape 179798 2369 20 1 0 2 0 = 41729930832131000340937432837 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_1_10_2369_0_join6

private theorem rec_1_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 0 128 = 11569091813675348198078306208 := by decide +kernel
private theorem rec_1_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 128 128 = 9465704976261857516435818400 := by decide +kernel
private theorem rec_1_10_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 256 128 = 7504056939684548600226658208 := by decide +kernel
private theorem rec_1_10_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 384 128 = 5679160752147533793060831697 := by decide +kernel
private theorem rec_1_10_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 512 128 = 3986054834398964465501260471 := by decide +kernel
private theorem rec_1_10_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 640 128 = 2419788986633092014156522435 := by decide +kernel
private theorem rec_1_10_2369_1_part6 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 768 128 = 975418747381075411932393765 := by decide +kernel
private theorem rec_1_10_2369_1_part7 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 896 29 = 32463502108492753459120148 := by decide +kernel
private theorem rec_1_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 0 256 = 21034796789937205714514124608 :=
  phaseBlock_append rec_1_10_2369_1_part0 rec_1_10_2369_1_part1 rfl rfl rfl
private theorem rec_1_10_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 256 256 = 13183217691832082393287489905 :=
  phaseBlock_append rec_1_10_2369_1_part2 rec_1_10_2369_1_part3 rfl rfl rfl
private theorem rec_1_10_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 0 512 = 34218014481769288107801614513 :=
  phaseBlock_append rec_1_10_2369_1_join0 rec_1_10_2369_1_join1 rfl rfl rfl
private theorem rec_1_10_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 512 256 = 6405843821032056479657782906 :=
  phaseBlock_append rec_1_10_2369_1_part4 rec_1_10_2369_1_part5 rfl rfl rfl
private theorem rec_1_10_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 768 157 = 1007882249489568165391513913 :=
  phaseBlock_append rec_1_10_2369_1_part6 rec_1_10_2369_1_part7 rfl rfl rfl
private theorem rec_1_10_2369_1_join5 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 512 413 = 7413726070521624645049296819 :=
  phaseBlock_append rec_1_10_2369_1_join3 rec_1_10_2369_1_join4 rfl rfl rfl
private theorem rec_1_10_2369_1_join6 :
    phaseBlock (fastLayerG (bank 1 10).shape 179798 2369 20 1 0 2 1) 0 925 = 41631740552290912752850911332 :=
  phaseBlock_append rec_1_10_2369_1_join2 rec_1_10_2369_1_join5 rfl rfl rfl

private theorem rec_1_10_2369_1 : fastPhase (bank 1 10).shape 179798 2369 20 1 0 2 1 = 41631740552290912752850911332 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_1_10_2369_1_join6

theorem receipt_1_10 : Checked (bank 1 10) 20 0 2 := by
  refine checked_from_values (bank 1 10) 20 0 2
    (P3_7_1.checked (bank 1 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_10_2368_0 rec_1_10_2368_1 rec_1_10_2369_0 rec_1_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 0 128 = 60400079129588755679634923936 := by decide +kernel
private theorem rec_1_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 128 128 = 52610863157358959194727231904 := by decide +kernel
private theorem rec_1_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 256 128 = 45195133549959260616569471392 := by decide +kernel
private theorem rec_1_11_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 384 128 = 38143608392761022844486996384 := by decide +kernel
private theorem rec_1_11_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 512 128 = 31447032466902378414089200032 := by decide +kernel
private theorem rec_1_11_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 640 128 = 25096183703023905536119818743 := by decide +kernel
private theorem rec_1_11_2368_0_part6 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 768 128 = 19081880444931267385001972101 := by decide +kernel
private theorem rec_1_11_2368_0_part7 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 896 128 = 13394927768316933580572536085 := by decide +kernel
private theorem rec_1_11_2368_0_part8 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 1024 128 = 8026146237773659157296109751 := by decide +kernel
private theorem rec_1_11_2368_0_part9 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 1152 128 = 2966383059442119821619735863 := by decide +kernel
private theorem rec_1_11_2368_0_part10 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 1280 14 = 30356932047697836240117229 := by decide +kernel
private theorem rec_1_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 0 256 = 113010942286947714874362155840 :=
  phaseBlock_append rec_1_11_2368_0_part0 rec_1_11_2368_0_part1 rfl rfl rfl
private theorem rec_1_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 384 256 = 69590640859663401258576196416 :=
  phaseBlock_append rec_1_11_2368_0_part3 rec_1_11_2368_0_part4 rfl rfl rfl
private theorem rec_1_11_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 256 384 = 114785774409622661875145667808 :=
  phaseBlock_append rec_1_11_2368_0_part2 rec_1_11_2368_0_join1 rfl rfl rfl
private theorem rec_1_11_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 0 640 = 227796716696570376749507823648 :=
  phaseBlock_append rec_1_11_2368_0_join0 rec_1_11_2368_0_join2 rfl rfl rfl
private theorem rec_1_11_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 768 256 = 32476808213248200965574508186 :=
  phaseBlock_append rec_1_11_2368_0_part6 rec_1_11_2368_0_part7 rfl rfl rfl
private theorem rec_1_11_2368_0_join5 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 640 384 = 57572991916272106501694326929 :=
  phaseBlock_append rec_1_11_2368_0_part5 rec_1_11_2368_0_join4 rfl rfl rfl
private theorem rec_1_11_2368_0_join6 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 1152 142 = 2996739991489817657859853092 :=
  phaseBlock_append rec_1_11_2368_0_part9 rec_1_11_2368_0_part10 rfl rfl rfl
private theorem rec_1_11_2368_0_join7 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 1024 270 = 11022886229263476815155962843 :=
  phaseBlock_append rec_1_11_2368_0_part8 rec_1_11_2368_0_join6 rfl rfl rfl
private theorem rec_1_11_2368_0_join8 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 640 654 = 68595878145535583316850289772 :=
  phaseBlock_append rec_1_11_2368_0_join5 rec_1_11_2368_0_join7 rfl rfl rfl
private theorem rec_1_11_2368_0_join9 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 0) 0 1294 = 296392594842105960066358113420 :=
  phaseBlock_append rec_1_11_2368_0_join3 rec_1_11_2368_0_join8 rfl rfl rfl

private theorem rec_1_11_2368_0 : fastPhase (bank 1 11).shape 179798 2368 32 1 0 2 0 = 296392594842105960066358113420 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_1_11_2368_0_join9

private theorem rec_1_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 0 128 = 60338603125024460240982577568 := by decide +kernel
private theorem rec_1_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 128 128 = 52552242709229400580597293472 := by decide +kernel
private theorem rec_1_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 256 128 = 45139298377102558425648935328 := by decide +kernel
private theorem rec_1_11_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 384 128 = 38090488417525915027277431200 := by decide +kernel
private theorem rec_1_11_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 512 128 = 31396557814955714104191308192 := by decide +kernel
private theorem rec_1_11_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 640 128 = 25048284691466322861834639246 := by decide +kernel
private theorem rec_1_11_2368_1_part6 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 768 128 = 19036487540090812757452226782 := by decide +kernel
private theorem rec_1_11_2368_1_part7 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 896 128 = 13351971624642316729707707688 := by decide +kernel
private theorem rec_1_11_2368_1_part8 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 1024 128 = 7985557712596852420998323382 := by decide +kernel
private theorem rec_1_11_2368_1_part9 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 1152 128 = 2928093212830083136417145483 := by decide +kernel
private theorem rec_1_11_2368_1_part10 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 1280 14 = 26305504378395827749902769 := by decide +kernel
private theorem rec_1_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 0 256 = 112890845834253860821579871040 :=
  phaseBlock_append rec_1_11_2368_1_part0 rec_1_11_2368_1_part1 rfl rfl rfl
private theorem rec_1_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 384 256 = 69487046232481629131468739392 :=
  phaseBlock_append rec_1_11_2368_1_part3 rec_1_11_2368_1_part4 rfl rfl rfl
private theorem rec_1_11_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 256 384 = 114626344609584187557117674720 :=
  phaseBlock_append rec_1_11_2368_1_part2 rec_1_11_2368_1_join1 rfl rfl rfl
private theorem rec_1_11_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 0 640 = 227517190443838048378697545760 :=
  phaseBlock_append rec_1_11_2368_1_join0 rec_1_11_2368_1_join2 rfl rfl rfl
private theorem rec_1_11_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 768 256 = 32388459164733129487159934470 :=
  phaseBlock_append rec_1_11_2368_1_part6 rec_1_11_2368_1_part7 rfl rfl rfl
private theorem rec_1_11_2368_1_join5 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 640 384 = 57436743856199452348994573716 :=
  phaseBlock_append rec_1_11_2368_1_part5 rec_1_11_2368_1_join4 rfl rfl rfl
private theorem rec_1_11_2368_1_join6 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 1152 142 = 2954398717208478964167048252 :=
  phaseBlock_append rec_1_11_2368_1_part9 rec_1_11_2368_1_part10 rfl rfl rfl
private theorem rec_1_11_2368_1_join7 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 1024 270 = 10939956429805331385165371634 :=
  phaseBlock_append rec_1_11_2368_1_part8 rec_1_11_2368_1_join6 rfl rfl rfl
private theorem rec_1_11_2368_1_join8 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 640 654 = 68376700286004783734159945350 :=
  phaseBlock_append rec_1_11_2368_1_join5 rec_1_11_2368_1_join7 rfl rfl rfl
private theorem rec_1_11_2368_1_join9 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2368 32 1 0 2 1) 0 1294 = 295893890729842832112857491110 :=
  phaseBlock_append rec_1_11_2368_1_join3 rec_1_11_2368_1_join8 rfl rfl rfl

private theorem rec_1_11_2368_1 : fastPhase (bank 1 11).shape 179798 2368 32 1 0 2 1 = 295893890729842832112857491110 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_1_11_2368_1_join9

private theorem rec_1_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 0 128 = 60400627834224166407080813952 := by decide +kernel
private theorem rec_1_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 128 128 = 52611313197310259224830109056 := by decide +kernel
private theorem rec_1_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 256 128 = 45195495395651532185685599616 := by decide +kernel
private theorem rec_1_11_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 384 128 = 38143892195417189040204998016 := by decide +kernel
private theorem rec_1_11_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 512 128 = 31447248059473053836648359296 := by decide +kernel
private theorem rec_1_11_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 640 128 = 25096340454799165236653112117 := by decide +kernel
private theorem rec_1_11_2369_0_part6 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 768 128 = 19081987486875366687806650905 := by decide +kernel
private theorem rec_1_11_2369_0_part7 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 896 128 = 13394994146557163842398685401 := by decide +kernel
private theorem rec_1_11_2369_0_part8 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 1024 128 = 8026180652353951576182253779 := by decide +kernel
private theorem rec_1_11_2369_0_part9 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 1152 128 = 2966393870444080414723995393 := by decide +kernel
private theorem rec_1_11_2369_0_part10 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 1280 14 = 30357027932023333926278481 := by decide +kernel
private theorem rec_1_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 0 256 = 113011941031534425631910923008 :=
  phaseBlock_append rec_1_11_2369_0_part0 rec_1_11_2369_0_part1 rfl rfl rfl
private theorem rec_1_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 384 256 = 69591140254890242876853357312 :=
  phaseBlock_append rec_1_11_2369_0_part3 rec_1_11_2369_0_part4 rfl rfl rfl
private theorem rec_1_11_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 256 384 = 114786635650541775062538956928 :=
  phaseBlock_append rec_1_11_2369_0_part2 rec_1_11_2369_0_join1 rfl rfl rfl
private theorem rec_1_11_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 0 640 = 227798576682076200694449879936 :=
  phaseBlock_append rec_1_11_2369_0_join0 rec_1_11_2369_0_join2 rfl rfl rfl
private theorem rec_1_11_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 768 256 = 32476981633432530530205336306 :=
  phaseBlock_append rec_1_11_2369_0_part6 rec_1_11_2369_0_part7 rfl rfl rfl
private theorem rec_1_11_2369_0_join5 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 640 384 = 57573322088231695766858448423 :=
  phaseBlock_append rec_1_11_2369_0_part5 rec_1_11_2369_0_join4 rfl rfl rfl
private theorem rec_1_11_2369_0_join6 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 1152 142 = 2996750898376103748650273874 :=
  phaseBlock_append rec_1_11_2369_0_part9 rec_1_11_2369_0_part10 rfl rfl rfl
private theorem rec_1_11_2369_0_join7 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 1024 270 = 11022931550730055324832527653 :=
  phaseBlock_append rec_1_11_2369_0_part8 rec_1_11_2369_0_join6 rfl rfl rfl
private theorem rec_1_11_2369_0_join8 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 640 654 = 68596253638961751091690976076 :=
  phaseBlock_append rec_1_11_2369_0_join5 rec_1_11_2369_0_join7 rfl rfl rfl
private theorem rec_1_11_2369_0_join9 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 0) 0 1294 = 296394830321037951786140856012 :=
  phaseBlock_append rec_1_11_2369_0_join3 rec_1_11_2369_0_join8 rfl rfl rfl

private theorem rec_1_11_2369_0 : fastPhase (bank 1 11).shape 179798 2369 32 1 0 2 0 = 296394830321037951786140856012 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_1_11_2369_0_join9

private theorem rec_1_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 0 128 = 60339151375849867300423124544 := by decide +kernel
private theorem rec_1_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 128 128 = 52552692336878012692743005760 := by decide +kernel
private theorem rec_1_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 256 128 = 45139659850489131510459369024 := by decide +kernel
private theorem rec_1_11_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 384 128 = 38090771886368139948613690944 := by decide +kernel
private theorem rec_1_11_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 512 128 = 31396773110704062108554118720 := by decide +kernel
private theorem rec_1_11_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 640 128 = 25048441182174722991642499530 := by decide +kernel
private theorem rec_1_11_2369_1_part6 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 768 128 = 19036594355509481865595747273 := by decide +kernel
private theorem rec_1_11_2369_1_part7 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 896 128 = 13352037809336092011713473440 := by decide +kernel
private theorem rec_1_11_2369_1_part8 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 1024 128 = 7985591965060444017687983799 := by decide +kernel
private theorem rec_1_11_2369_1_part9 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 1152 128 = 2928103891604232137014320078 := by decide +kernel
private theorem rec_1_11_2369_1_part10 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 1280 14 = 26305587548781317403779232 := by decide +kernel
private theorem rec_1_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 0 256 = 112891843712727879993166130304 :=
  phaseBlock_append rec_1_11_2369_1_part0 rec_1_11_2369_1_part1 rfl rfl rfl
private theorem rec_1_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 384 256 = 69487544997072202057167809664 :=
  phaseBlock_append rec_1_11_2369_1_part3 rec_1_11_2369_1_part4 rfl rfl rfl
private theorem rec_1_11_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 256 384 = 114627204847561333567627178688 :=
  phaseBlock_append rec_1_11_2369_1_part2 rec_1_11_2369_1_join1 rfl rfl rfl
private theorem rec_1_11_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 0 640 = 227519048560289213560793308992 :=
  phaseBlock_append rec_1_11_2369_1_join0 rec_1_11_2369_1_join2 rfl rfl rfl
private theorem rec_1_11_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 768 256 = 32388632164845573877309220713 :=
  phaseBlock_append rec_1_11_2369_1_part6 rec_1_11_2369_1_part7 rfl rfl rfl
private theorem rec_1_11_2369_1_join5 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 640 384 = 57437073347020296868951720243 :=
  phaseBlock_append rec_1_11_2369_1_part5 rec_1_11_2369_1_join4 rfl rfl rfl
private theorem rec_1_11_2369_1_join6 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 1152 142 = 2954409479153013454418099310 :=
  phaseBlock_append rec_1_11_2369_1_part9 rec_1_11_2369_1_part10 rfl rfl rfl
private theorem rec_1_11_2369_1_join7 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 1024 270 = 10940001444213457472106083109 :=
  phaseBlock_append rec_1_11_2369_1_part8 rec_1_11_2369_1_join6 rfl rfl rfl
private theorem rec_1_11_2369_1_join8 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 640 654 = 68377074791233754341057803352 :=
  phaseBlock_append rec_1_11_2369_1_join5 rec_1_11_2369_1_join7 rfl rfl rfl
private theorem rec_1_11_2369_1_join9 :
    phaseBlock (fastLayerG (bank 1 11).shape 179798 2369 32 1 0 2 1) 0 1294 = 295896123351522967901851112344 :=
  phaseBlock_append rec_1_11_2369_1_join3 rec_1_11_2369_1_join8 rfl rfl rfl

private theorem rec_1_11_2369_1 : fastPhase (bank 1 11).shape 179798 2369 32 1 0 2 1 = 295896123351522967901851112344 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_1_11_2369_1_join9

theorem receipt_1_11 : Checked (bank 1 11) 32 0 2 := by
  refine checked_from_values (bank 1 11) 32 0 2
    (P3_7_1.checked (bank 1 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_11_2368_0 rec_1_11_2368_1 rec_1_11_2369_0 rec_1_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 0 128 = 52080335951155974891387501856 := by decide +kernel
private theorem rec_1_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 128 128 = 45361357902821634584725589280 := by decide +kernel
private theorem rec_1_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 256 128 = 38965175127303461777383677216 := by decide +kernel
private theorem rec_1_12_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 384 128 = 32883729253726645816908262688 := by decide +kernel
private theorem rec_1_12_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 512 128 = 27108986743738239810712468768 := by decide +kernel
private theorem rec_1_12_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 640 128 = 21632944312981577174068621878 := by decide +kernel
private theorem rec_1_12_2368_0_part6 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 768 128 = 16447635518227324112391771806 := by decide +kernel
private theorem rec_1_12_2368_0_part7 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 896 128 = 11545084459926989486703274608 := by decide +kernel
private theorem rec_1_12_2368_0_part8 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 1024 128 = 6917330172544414900993250746 := by decide +kernel
private theorem rec_1_12_2368_0_part9 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 1152 128 = 2556436469849491073378512839 := by decide +kernel
private theorem rec_1_12_2368_0_part10 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 1280 14 = 26160629576421654264843049 := by decide +kernel
private theorem rec_1_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 0 256 = 97441693853977609476113091136 :=
  phaseBlock_append rec_1_12_2368_0_part0 rec_1_12_2368_0_part1 rfl rfl rfl
private theorem rec_1_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 384 256 = 59992715997464885627620731456 :=
  phaseBlock_append rec_1_12_2368_0_part3 rec_1_12_2368_0_part4 rfl rfl rfl
private theorem rec_1_12_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 256 384 = 98957891124768347405004408672 :=
  phaseBlock_append rec_1_12_2368_0_part2 rec_1_12_2368_0_join1 rfl rfl rfl
private theorem rec_1_12_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 0 640 = 196399584978745956881117499808 :=
  phaseBlock_append rec_1_12_2368_0_join0 rec_1_12_2368_0_join2 rfl rfl rfl
private theorem rec_1_12_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 768 256 = 27992719978154313599095046414 :=
  phaseBlock_append rec_1_12_2368_0_part6 rec_1_12_2368_0_part7 rfl rfl rfl
private theorem rec_1_12_2368_0_join5 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 640 384 = 49625664291135890773163668292 :=
  phaseBlock_append rec_1_12_2368_0_part5 rec_1_12_2368_0_join4 rfl rfl rfl
private theorem rec_1_12_2368_0_join6 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 1152 142 = 2582597099425912727643355888 :=
  phaseBlock_append rec_1_12_2368_0_part9 rec_1_12_2368_0_part10 rfl rfl rfl
private theorem rec_1_12_2368_0_join7 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 1024 270 = 9499927271970327628636606634 :=
  phaseBlock_append rec_1_12_2368_0_part8 rec_1_12_2368_0_join6 rfl rfl rfl
private theorem rec_1_12_2368_0_join8 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 640 654 = 59125591563106218401800274926 :=
  phaseBlock_append rec_1_12_2368_0_join5 rec_1_12_2368_0_join7 rfl rfl rfl
private theorem rec_1_12_2368_0_join9 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 0) 0 1294 = 255525176541852175282917774734 :=
  phaseBlock_append rec_1_12_2368_0_join3 rec_1_12_2368_0_join8 rfl rfl rfl

private theorem rec_1_12_2368_0 : fastPhase (bank 1 12).shape 179798 2368 31 1 0 2 0 = 255525176541852175282917774734 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_1_12_2368_0_join9

private theorem rec_1_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 0 128 = 52027303881577854955601214240 := by decide +kernel
private theorem rec_1_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 128 128 = 45310794128430409078086896416 := by decide +kernel
private theorem rec_1_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 256 128 = 38917018620910239389020248864 := by decide +kernel
private theorem rec_1_12_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 384 128 = 32837919177458357507082988320 := by decide +kernel
private theorem rec_1_12_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 512 128 = 27065462448845131642108017440 := by decide +kernel
private theorem rec_1_12_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 640 128 = 21591645329808492272425149727 := by decide +kernel
private theorem rec_1_12_2368_1_part6 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 768 128 = 16408501519617632887201338108 := by decide +kernel
private theorem rec_1_12_2368_1_part7 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 896 128 = 11508055294376275930778751300 := by decide +kernel
private theorem rec_1_12_2368_1_part8 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 1024 128 = 6882345877222211277597055433 := by decide +kernel
private theorem rec_1_12_2368_1_part9 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 1152 128 = 2523437270441767100599124370 := by decide +kernel
private theorem rec_1_12_2368_1_part10 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 1280 14 = 22669232229561415446447301 := by decide +kernel
private theorem rec_1_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 0 256 = 97338098010008264033688110656 :=
  phaseBlock_append rec_1_12_2368_1_part0 rec_1_12_2368_1_part1 rfl rfl rfl
private theorem rec_1_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 384 256 = 59903381626303489149191005760 :=
  phaseBlock_append rec_1_12_2368_1_part3 rec_1_12_2368_1_part4 rfl rfl rfl
private theorem rec_1_12_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 256 384 = 98820400247213728538211254624 :=
  phaseBlock_append rec_1_12_2368_1_part2 rec_1_12_2368_1_join1 rfl rfl rfl
private theorem rec_1_12_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 0 640 = 196158498257221992571899365280 :=
  phaseBlock_append rec_1_12_2368_1_join0 rec_1_12_2368_1_join2 rfl rfl rfl
private theorem rec_1_12_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 768 256 = 27916556813993908817980089408 :=
  phaseBlock_append rec_1_12_2368_1_part6 rec_1_12_2368_1_part7 rfl rfl rfl
private theorem rec_1_12_2368_1_join5 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 640 384 = 49508202143802401090405239135 :=
  phaseBlock_append rec_1_12_2368_1_part5 rec_1_12_2368_1_join4 rfl rfl rfl
private theorem rec_1_12_2368_1_join6 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 1152 142 = 2546106502671328516045571671 :=
  phaseBlock_append rec_1_12_2368_1_part9 rec_1_12_2368_1_part10 rfl rfl rfl
private theorem rec_1_12_2368_1_join7 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 1024 270 = 9428452379893539793642627104 :=
  phaseBlock_append rec_1_12_2368_1_part8 rec_1_12_2368_1_join6 rfl rfl rfl
private theorem rec_1_12_2368_1_join8 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 640 654 = 58936654523695940884047866239 :=
  phaseBlock_append rec_1_12_2368_1_join5 rec_1_12_2368_1_join7 rfl rfl rfl
private theorem rec_1_12_2368_1_join9 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2368 31 1 0 2 1) 0 1294 = 255095152780917933455947231519 :=
  phaseBlock_append rec_1_12_2368_1_join3 rec_1_12_2368_1_join8 rfl rfl rfl

private theorem rec_1_12_2368_1 : fastPhase (bank 1 12).shape 179798 2368 31 1 0 2 1 = 255095152780917933455947231519 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_1_12_2368_1_join9

private theorem rec_1_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 0 128 = 52080809377870042606860541760 := by decide +kernel
private theorem rec_1_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 128 128 = 45361746197660330658603302720 := by decide +kernel
private theorem rec_1_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 256 128 = 38965487328188468569178529600 := by decide +kernel
private theorem rec_1_12_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 384 128 = 32883974121798542659420110656 := by decide +kernel
private theorem rec_1_12_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 512 128 = 27109172764221165276303466304 := by decide +kernel
private theorem rec_1_12_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 640 128 = 21633079571837104210908615774 := by decide +kernel
private theorem rec_1_12_2369_0_part6 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 768 128 = 16447727890510893816587312465 := by decide +kernel
private theorem rec_1_12_2369_0_part7 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 896 128 = 11545141747871072229889134624 := by decide +kernel
private theorem rec_1_12_2369_0_part8 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 1024 128 = 6917359879287308387677973931 := by decide +kernel
private theorem rec_1_12_2369_0_part9 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 1152 128 = 2556445804209474133325038674 := by decide +kernel
private theorem rec_1_12_2369_0_part10 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 1280 14 = 26160712390437066468597420 := by decide +kernel
private theorem rec_1_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 0 256 = 97442555575530373265463844480 :=
  phaseBlock_append rec_1_12_2369_0_part0 rec_1_12_2369_0_part1 rfl rfl rfl
private theorem rec_1_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 384 256 = 59993146886019707935723576960 :=
  phaseBlock_append rec_1_12_2369_0_part3 rec_1_12_2369_0_part4 rfl rfl rfl
private theorem rec_1_12_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 256 384 = 98958634214208176504902106560 :=
  phaseBlock_append rec_1_12_2369_0_part2 rec_1_12_2369_0_join1 rfl rfl rfl
private theorem rec_1_12_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 0 640 = 196401189789738549770365951040 :=
  phaseBlock_append rec_1_12_2369_0_join0 rec_1_12_2369_0_join2 rfl rfl rfl
private theorem rec_1_12_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 768 256 = 27992869638381966046476447089 :=
  phaseBlock_append rec_1_12_2369_0_part6 rec_1_12_2369_0_part7 rfl rfl rfl
private theorem rec_1_12_2369_0_join5 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 640 384 = 49625949210219070257385062863 :=
  phaseBlock_append rec_1_12_2369_0_part5 rec_1_12_2369_0_join4 rfl rfl rfl
private theorem rec_1_12_2369_0_join6 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 1152 142 = 2582606516599911199793636094 :=
  phaseBlock_append rec_1_12_2369_0_part9 rec_1_12_2369_0_part10 rfl rfl rfl
private theorem rec_1_12_2369_0_join7 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 1024 270 = 9499966395887219587471610025 :=
  phaseBlock_append rec_1_12_2369_0_part8 rec_1_12_2369_0_join6 rfl rfl rfl
private theorem rec_1_12_2369_0_join8 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 640 654 = 59125915606106289844856672888 :=
  phaseBlock_append rec_1_12_2369_0_join5 rec_1_12_2369_0_join7 rfl rfl rfl
private theorem rec_1_12_2369_0_join9 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 0) 0 1294 = 255527105395844839615222623928 :=
  phaseBlock_append rec_1_12_2369_0_join3 rec_1_12_2369_0_join8 rfl rfl rfl

private theorem rec_1_12_2369_0 : fastPhase (bank 1 12).shape 179798 2369 31 1 0 2 0 = 255527105395844839615222623928 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_1_12_2369_0_join9

private theorem rec_1_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 0 128 = 52027776916494745711545076992 := by decide +kernel
private theorem rec_1_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 128 128 = 45311182067328396315856456960 := by decide +kernel
private theorem rec_1_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 256 128 = 38917330500400511834865847552 := by decide +kernel
private theorem rec_1_12_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 384 128 = 32838163757375738458041076992 := by decide +kernel
private theorem rec_1_12_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 512 128 = 27065648213112736009595833600 := by decide +kernel
private theorem rec_1_12_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 640 128 = 21591780363311607067241654137 := by decide +kernel
private theorem rec_1_12_2369_1_part6 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 768 128 = 16408593696360840497302427646 := by decide +kernel
private theorem rec_1_12_2369_1_part7 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 896 128 = 11508112415239087429509566703 := by decide +kernel
private theorem rec_1_12_2369_1_part8 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 1024 128 = 6882375444000882173315297217 := by decide +kernel
private theorem rec_1_12_2369_1_part9 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 1152 128 = 2523446490620702288829017541 := by decide +kernel
private theorem rec_1_12_2369_1_part10 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 1280 14 = 22669304062727751752046864 := by decide +kernel
private theorem rec_1_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 0 256 = 97338958983823142027401533952 :=
  phaseBlock_append rec_1_12_2369_1_part0 rec_1_12_2369_1_part1 rfl rfl rfl
private theorem rec_1_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 384 256 = 59903811970488474467636910592 :=
  phaseBlock_append rec_1_12_2369_1_part3 rec_1_12_2369_1_part4 rfl rfl rfl
private theorem rec_1_12_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 256 384 = 98821142470888986302502758144 :=
  phaseBlock_append rec_1_12_2369_1_part2 rec_1_12_2369_1_join1 rfl rfl rfl
private theorem rec_1_12_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 0 640 = 196160101454712128329904292096 :=
  phaseBlock_append rec_1_12_2369_1_join0 rec_1_12_2369_1_join2 rfl rfl rfl
private theorem rec_1_12_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 768 256 = 27916706111599927926811994349 :=
  phaseBlock_append rec_1_12_2369_1_part6 rec_1_12_2369_1_part7 rfl rfl rfl
private theorem rec_1_12_2369_1_join5 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 640 384 = 49508486474911534994053648486 :=
  phaseBlock_append rec_1_12_2369_1_part5 rec_1_12_2369_1_join4 rfl rfl rfl
private theorem rec_1_12_2369_1_join6 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 1152 142 = 2546115794683430040581064405 :=
  phaseBlock_append rec_1_12_2369_1_part9 rec_1_12_2369_1_part10 rfl rfl rfl
private theorem rec_1_12_2369_1_join7 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 1024 270 = 9428491238684312213896361622 :=
  phaseBlock_append rec_1_12_2369_1_part8 rec_1_12_2369_1_join6 rfl rfl rfl
private theorem rec_1_12_2369_1_join8 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 640 654 = 58936977713595847207950010108 :=
  phaseBlock_append rec_1_12_2369_1_join5 rec_1_12_2369_1_join7 rfl rfl rfl
private theorem rec_1_12_2369_1_join9 :
    phaseBlock (fastLayerG (bank 1 12).shape 179798 2369 31 1 0 2 1) 0 1294 = 255097079168307975537854302204 :=
  phaseBlock_append rec_1_12_2369_1_join3 rec_1_12_2369_1_join8 rfl rfl rfl

private theorem rec_1_12_2369_1 : fastPhase (bank 1 12).shape 179798 2369 31 1 0 2 1 = 255097079168307975537854302204 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_1_12_2369_1_join9

theorem receipt_1_12 : Checked (bank 1 12) 31 0 2 := by
  refine checked_from_values (bank 1 12) 31 0 2
    (P3_7_1.checked (bank 1 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_12_2368_0 rec_1_12_2368_1 rec_1_12_2369_0 rec_1_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 0 128 = 205660424680293869508576399648 := by decide +kernel
private theorem rec_1_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 128 128 = 186519761820331664916516487456 := by decide +kernel
private theorem rec_1_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 256 128 = 168045535512701703878831616288 := by decide +kernel
private theorem rec_1_13_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 384 128 = 150225695539762611940677820704 := by decide +kernel
private theorem rec_1_13_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 512 128 = 133048221948975853720538943776 := by decide +kernel
private theorem rec_1_13_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 640 128 = 116501125027764915756012175648 := by decide +kernel
private theorem rec_1_13_2368_0_part6 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 768 128 = 100572445278374489349593592096 := by decide +kernel
private theorem rec_1_13_2368_0_part7 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 896 128 = 85250262620124794058139635027 := by decide +kernel
private theorem rec_1_13_2368_0_part8 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 1024 128 = 70522719970511554461400682429 := by decide +kernel
private theorem rec_1_13_2368_0_part9 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 1152 128 = 56377932018579404883726976536 := by decide +kernel
private theorem rec_1_13_2368_0_part10 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 1280 128 = 42804020753904212605363086196 := by decide +kernel
private theorem rec_1_13_2368_0_part11 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 1408 128 = 29789138368694941193813694477 := by decide +kernel
private theorem rec_1_13_2368_0_part12 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 1536 128 = 17321467263882258867946265838 := by decide +kernel
private theorem rec_1_13_2368_0_part13 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 1664 123 = 5396190009004761149606598405 := by decide +kernel
private theorem rec_1_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 128 256 = 354565297333033368795348103744 :=
  phaseBlock_append rec_1_13_2368_0_part1 rec_1_13_2368_0_part2 rfl rfl rfl
private theorem rec_1_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 0 384 = 560225722013327238303924503392 :=
  phaseBlock_append rec_1_13_2368_0_part0 rec_1_13_2368_0_join0 rfl rfl rfl
private theorem rec_1_13_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 384 256 = 283273917488738465661216764480 :=
  phaseBlock_append rec_1_13_2368_0_part3 rec_1_13_2368_0_part4 rfl rfl rfl
private theorem rec_1_13_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 640 256 = 217073570306139405105605767744 :=
  phaseBlock_append rec_1_13_2368_0_part5 rec_1_13_2368_0_part6 rfl rfl rfl
private theorem rec_1_13_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 384 512 = 500347487794877870766822532224 :=
  phaseBlock_append rec_1_13_2368_0_join2 rec_1_13_2368_0_join3 rfl rfl rfl
private theorem rec_1_13_2368_0_join5 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 0 896 = 1060573209808205109070747035616 :=
  phaseBlock_append rec_1_13_2368_0_join1 rec_1_13_2368_0_join4 rfl rfl rfl
private theorem rec_1_13_2368_0_join6 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 1024 256 = 126900651989090959345127658965 :=
  phaseBlock_append rec_1_13_2368_0_part8 rec_1_13_2368_0_part9 rfl rfl rfl
private theorem rec_1_13_2368_0_join7 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 896 384 = 212150914609215753403267293992 :=
  phaseBlock_append rec_1_13_2368_0_part7 rec_1_13_2368_0_join6 rfl rfl rfl
private theorem rec_1_13_2368_0_join8 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 1280 256 = 72593159122599153799176780673 :=
  phaseBlock_append rec_1_13_2368_0_part10 rec_1_13_2368_0_part11 rfl rfl rfl
private theorem rec_1_13_2368_0_join9 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 1536 251 = 22717657272887020017552864243 :=
  phaseBlock_append rec_1_13_2368_0_part12 rec_1_13_2368_0_part13 rfl rfl rfl
private theorem rec_1_13_2368_0_join10 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 1280 507 = 95310816395486173816729644916 :=
  phaseBlock_append rec_1_13_2368_0_join8 rec_1_13_2368_0_join9 rfl rfl rfl
private theorem rec_1_13_2368_0_join11 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 896 891 = 307461731004701927219996938908 :=
  phaseBlock_append rec_1_13_2368_0_join7 rec_1_13_2368_0_join10 rfl rfl rfl
private theorem rec_1_13_2368_0_join12 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 0) 0 1787 = 1368034940812907036290743974524 :=
  phaseBlock_append rec_1_13_2368_0_join5 rec_1_13_2368_0_join11 rfl rfl rfl

private theorem rec_1_13_2368_0 : fastPhase (bank 1 13).shape 179798 2368 44 1 0 2 0 = 1368034940812907036290743974524 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_1_13_2368_0_join12

private theorem rec_1_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 0 128 = 205510363233195930474607135840 := by decide +kernel
private theorem rec_1_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 128 128 = 186374779829307986046225349728 := by decide +kernel
private theorem rec_1_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 256 128 = 167905541732371476044371602528 := by decide +kernel
private theorem rec_1_13_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 384 128 = 150090598955463476550758718560 := by decide +kernel
private theorem rec_1_13_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 512 128 = 132917931776571395551711890528 := by decide +kernel
private theorem rec_1_13_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 640 128 = 116375550713452155783954218080 := by decide +kernel
private theorem rec_1_13_2368_1_part6 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 768 128 = 100451496498491377580392246368 := by decide +kernel
private theorem rec_1_13_2368_1_part7 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 896 128 = 85133849269222998650904344058 := by decide +kernel
private theorem rec_1_13_2368_1_part8 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 1024 128 = 70410752105793945405291713159 := by decide +kernel
private theorem rec_1_13_2368_1_part9 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 1152 128 = 56270319903877135352840618512 := by decide +kernel
private theorem rec_1_13_2368_1_part10 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 1280 128 = 42700674882856263092028614049 := by decide +kernel
private theorem rec_1_13_2368_1_part11 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 1408 128 = 29689969464578141987737840464 := by decide +kernel
private theorem rec_1_13_2368_1_part12 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 1536 128 = 17226386279321896579722170984 := by decide +kernel
private theorem rec_1_13_2368_1_part13 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 1664 123 = 5308592043041005587775250614 := by decide +kernel
private theorem rec_1_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 128 256 = 354280321561679462090596952256 :=
  phaseBlock_append rec_1_13_2368_1_part1 rec_1_13_2368_1_part2 rfl rfl rfl
private theorem rec_1_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 0 384 = 559790684794875392565204088096 :=
  phaseBlock_append rec_1_13_2368_1_part0 rec_1_13_2368_1_join0 rfl rfl rfl
private theorem rec_1_13_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 384 256 = 283008530732034872102470609088 :=
  phaseBlock_append rec_1_13_2368_1_part3 rec_1_13_2368_1_part4 rfl rfl rfl
private theorem rec_1_13_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 640 256 = 216827047211943533364346464448 :=
  phaseBlock_append rec_1_13_2368_1_part5 rec_1_13_2368_1_part6 rfl rfl rfl
private theorem rec_1_13_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 384 512 = 499835577943978405466817073536 :=
  phaseBlock_append rec_1_13_2368_1_join2 rec_1_13_2368_1_join3 rfl rfl rfl
private theorem rec_1_13_2368_1_join5 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 0 896 = 1059626262738853798032021161632 :=
  phaseBlock_append rec_1_13_2368_1_join1 rec_1_13_2368_1_join4 rfl rfl rfl
private theorem rec_1_13_2368_1_join6 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 1024 256 = 126681072009671080758132331671 :=
  phaseBlock_append rec_1_13_2368_1_part8 rec_1_13_2368_1_part9 rfl rfl rfl
private theorem rec_1_13_2368_1_join7 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 896 384 = 211814921278894079409036675729 :=
  phaseBlock_append rec_1_13_2368_1_part7 rec_1_13_2368_1_join6 rfl rfl rfl
private theorem rec_1_13_2368_1_join8 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 1280 256 = 72390644347434405079766454513 :=
  phaseBlock_append rec_1_13_2368_1_part10 rec_1_13_2368_1_part11 rfl rfl rfl
private theorem rec_1_13_2368_1_join9 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 1536 251 = 22534978322362902167497421598 :=
  phaseBlock_append rec_1_13_2368_1_part12 rec_1_13_2368_1_part13 rfl rfl rfl
private theorem rec_1_13_2368_1_join10 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 1280 507 = 94925622669797307247263876111 :=
  phaseBlock_append rec_1_13_2368_1_join8 rec_1_13_2368_1_join9 rfl rfl rfl
private theorem rec_1_13_2368_1_join11 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 896 891 = 306740543948691386656300551840 :=
  phaseBlock_append rec_1_13_2368_1_join7 rec_1_13_2368_1_join10 rfl rfl rfl
private theorem rec_1_13_2368_1_join12 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2368 44 1 0 2 1) 0 1787 = 1366366806687545184688321713472 :=
  phaseBlock_append rec_1_13_2368_1_join5 rec_1_13_2368_1_join11 rfl rfl rfl

private theorem rec_1_13_2368_1 : fastPhase (bank 1 13).shape 179798 2368 44 1 0 2 1 = 1366366806687545184688321713472 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_1_13_2368_1_join12

private theorem rec_1_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 0 128 = 205662307186557566486990855136 := by decide +kernel
private theorem rec_1_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 128 128 = 186521398081929542681077713888 := by decide +kernel
private theorem rec_1_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 256 128 = 168046944181596725465373375456 := by decide +kernel
private theorem rec_1_13_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 384 128 = 150226894855004563301600685024 := by decide +kernel
private theorem rec_1_13_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 512 128 = 133049229737754488947242982368 := by decide +kernel
private theorem rec_1_13_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 640 128 = 116501958706462222692027419616 := by decide +kernel
private theorem rec_1_13_2369_0_part6 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 768 128 = 100573121853616075594408279008 := by decide +kernel
private theorem rec_1_13_2369_0_part7 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 896 128 = 85250798376331209074882882544 := by decide +kernel
private theorem rec_1_13_2369_0_part8 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 1024 128 = 70523130795927958519009150536 := by decide +kernel
private theorem rec_1_13_2369_0_part9 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 1152 128 = 56378233988095375857629073462 := by decide +kernel
private theorem rec_1_13_2369_0_part10 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 1280 128 = 42804229502500606499288021922 := by decide +kernel
private theorem rec_1_13_2369_0_part11 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 1408 128 = 29789269101314314664950974846 := by decide +kernel
private theorem rec_1_13_2369_0_part12 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 1536 128 = 17321534744758423369316195064 := by decide +kernel
private theorem rec_1_13_2369_0_part13 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 1664 123 = 5396208586667277199653754185 := by decide +kernel
private theorem rec_1_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 128 256 = 354568342263526268146451089344 :=
  phaseBlock_append rec_1_13_2369_0_part1 rec_1_13_2369_0_part2 rfl rfl rfl
private theorem rec_1_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 0 384 = 560230649450083834633441944480 :=
  phaseBlock_append rec_1_13_2369_0_part0 rec_1_13_2369_0_join0 rfl rfl rfl
private theorem rec_1_13_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 384 256 = 283276124592759052248843667392 :=
  phaseBlock_append rec_1_13_2369_0_part3 rec_1_13_2369_0_part4 rfl rfl rfl
private theorem rec_1_13_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 640 256 = 217075080560078298286435698624 :=
  phaseBlock_append rec_1_13_2369_0_part5 rec_1_13_2369_0_part6 rfl rfl rfl
private theorem rec_1_13_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 384 512 = 500351205152837350535279366016 :=
  phaseBlock_append rec_1_13_2369_0_join2 rec_1_13_2369_0_join3 rfl rfl rfl
private theorem rec_1_13_2369_0_join5 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 0 896 = 1060581854602921185168721310496 :=
  phaseBlock_append rec_1_13_2369_0_join1 rec_1_13_2369_0_join4 rfl rfl rfl
private theorem rec_1_13_2369_0_join6 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 1024 256 = 126901364784023334376638223998 :=
  phaseBlock_append rec_1_13_2369_0_part8 rec_1_13_2369_0_part9 rfl rfl rfl
private theorem rec_1_13_2369_0_join7 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 896 384 = 212152163160354543451521106542 :=
  phaseBlock_append rec_1_13_2369_0_part7 rec_1_13_2369_0_join6 rfl rfl rfl
private theorem rec_1_13_2369_0_join8 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 1280 256 = 72593498603814921164238996768 :=
  phaseBlock_append rec_1_13_2369_0_part10 rec_1_13_2369_0_part11 rfl rfl rfl
private theorem rec_1_13_2369_0_join9 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 1536 251 = 22717743331425700568969949249 :=
  phaseBlock_append rec_1_13_2369_0_part12 rec_1_13_2369_0_part13 rfl rfl rfl
private theorem rec_1_13_2369_0_join10 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 1280 507 = 95311241935240621733208946017 :=
  phaseBlock_append rec_1_13_2369_0_join8 rec_1_13_2369_0_join9 rfl rfl rfl
private theorem rec_1_13_2369_0_join11 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 896 891 = 307463405095595165184730052559 :=
  phaseBlock_append rec_1_13_2369_0_join7 rec_1_13_2369_0_join10 rfl rfl rfl
private theorem rec_1_13_2369_0_join12 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 0) 0 1787 = 1368045259698516350353451363055 :=
  phaseBlock_append rec_1_13_2369_0_join5 rec_1_13_2369_0_join11 rfl rfl rfl

private theorem rec_1_13_2369_0 : fastPhase (bank 1 13).shape 179798 2369 44 1 0 2 0 = 1368045259698516350353451363055 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_1_13_2369_0_join12

private theorem rec_1_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 0 128 = 205512244624490507908701797472 := by decide +kernel
private theorem rec_1_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 128 128 = 186376415049837289947135052896 := by decide +kernel
private theorem rec_1_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 256 128 = 167906949432141435679375776864 := by decide +kernel
private theorem rec_1_13_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 384 128 = 150091797371572615284008365152 := by decide +kernel
private theorem rec_1_13_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 512 128 = 132918938734263970843982036064 := by decide +kernel
private theorem rec_1_13_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 640 128 = 116376383627170419583094148192 := by decide +kernel
private theorem rec_1_13_2369_1_part6 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 768 128 = 100452172372926957102473518176 := by decide +kernel
private theorem rec_1_13_2369_1_part7 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 896 128 = 85134384387261994280731164492 := by decide +kernel
private theorem rec_1_13_2369_1_part8 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 1024 128 = 70411162354319352611797140747 := by decide +kernel
private theorem rec_1_13_2369_1_part9 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 1152 128 = 56270621355775314840927980520 := by decide +kernel
private theorem rec_1_13_2369_1_part10 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 1280 128 = 42700883171116569929276061093 := by decide +kernel
private theorem rec_1_13_2369_1_part11 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 1408 128 = 29690099792143197501770017560 := by decide +kernel
private theorem rec_1_13_2369_1_part12 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 1536 128 = 17226453408434820191140612590 := by decide +kernel
private theorem rec_1_13_2369_1_part13 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 1664 123 = 5308610331052065583129885680 := by decide +kernel
private theorem rec_1_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 128 256 = 354283364481978725626510829760 :=
  phaseBlock_append rec_1_13_2369_1_part1 rec_1_13_2369_1_part2 rfl rfl rfl
private theorem rec_1_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 0 384 = 559795609106469233535212627232 :=
  phaseBlock_append rec_1_13_2369_1_part0 rec_1_13_2369_1_join0 rfl rfl rfl
private theorem rec_1_13_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 384 256 = 283010736105836586127990401216 :=
  phaseBlock_append rec_1_13_2369_1_part3 rec_1_13_2369_1_part4 rfl rfl rfl
private theorem rec_1_13_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 640 256 = 216828556000097376685567666368 :=
  phaseBlock_append rec_1_13_2369_1_part5 rec_1_13_2369_1_part6 rfl rfl rfl
private theorem rec_1_13_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 384 512 = 499839292105933962813558067584 :=
  phaseBlock_append rec_1_13_2369_1_join2 rec_1_13_2369_1_join3 rfl rfl rfl
private theorem rec_1_13_2369_1_join5 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 0 896 = 1059634901212403196348770694816 :=
  phaseBlock_append rec_1_13_2369_1_join1 rec_1_13_2369_1_join4 rfl rfl rfl
private theorem rec_1_13_2369_1_join6 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 1024 256 = 126681783710094667452725121267 :=
  phaseBlock_append rec_1_13_2369_1_part8 rec_1_13_2369_1_part9 rfl rfl rfl
private theorem rec_1_13_2369_1_join7 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 896 384 = 211816168097356661733456285759 :=
  phaseBlock_append rec_1_13_2369_1_part7 rec_1_13_2369_1_join6 rfl rfl rfl
private theorem rec_1_13_2369_1_join8 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 1280 256 = 72390982963259767431046078653 :=
  phaseBlock_append rec_1_13_2369_1_part10 rec_1_13_2369_1_part11 rfl rfl rfl
private theorem rec_1_13_2369_1_join9 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 1536 251 = 22535063739486885774270498270 :=
  phaseBlock_append rec_1_13_2369_1_part12 rec_1_13_2369_1_part13 rfl rfl rfl
private theorem rec_1_13_2369_1_join10 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 1280 507 = 94926046702746653205316576923 :=
  phaseBlock_append rec_1_13_2369_1_join8 rec_1_13_2369_1_join9 rfl rfl rfl
private theorem rec_1_13_2369_1_join11 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 896 891 = 306742214800103314938772862682 :=
  phaseBlock_append rec_1_13_2369_1_join7 rec_1_13_2369_1_join10 rfl rfl rfl
private theorem rec_1_13_2369_1_join12 :
    phaseBlock (fastLayerG (bank 1 13).shape 179798 2369 44 1 0 2 1) 0 1787 = 1366377116012506511287543557498 :=
  phaseBlock_append rec_1_13_2369_1_join5 rec_1_13_2369_1_join11 rfl rfl rfl

private theorem rec_1_13_2369_1 : fastPhase (bank 1 13).shape 179798 2369 44 1 0 2 1 = 1366377116012506511287543557498 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_1_13_2369_1_join12

theorem receipt_1_13 : Checked (bank 1 13) 44 0 2 := by
  refine checked_from_values (bank 1 13) 44 0 2
    (P3_7_1.checked (bank 1 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_13_2368_0 rec_1_13_2368_1 rec_1_13_2369_0 rec_1_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 0 128 = 2414542206200732297187031544608 := by decide +kernel
private theorem rec_1_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 128 128 = 2290794945976042649556894122784 := by decide +kernel
private theorem rec_1_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 256 128 = 2169441876671878893153781584672 := by decide +kernel
private theorem rec_1_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 384 128 = 2050458804083941130836146955040 := by decide +kernel
private theorem rec_1_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 512 128 = 1933821576555433933400879706912 := by decide +kernel
private theorem rec_1_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 640 128 = 1819506084951925522429091300128 := by decide +kernel
private theorem rec_1_14_2368_0_part6 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 768 128 = 1707488262636206953131900719904 := by decide +kernel
private theorem rec_1_14_2368_0_part7 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 896 128 = 1597744085443151297196220015392 := by decide +kernel
private theorem rec_1_14_2368_0_part8 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1024 128 = 1490249571654572825630539838240 := by decide +kernel
private theorem rec_1_14_2368_0_part9 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1152 128 = 1384980781974086191610714981152 := by decide +kernel
private theorem rec_1_14_2368_0_part10 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1280 128 = 1281913819501965613325749916448 := by decide +kernel
private theorem rec_1_14_2368_0_part11 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1408 128 = 1181024829710004056823584334624 := by decide +kernel
private theorem rec_1_14_2368_0_part12 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1536 128 = 1082290000785437484646187905388 := by decide +kernel
private theorem rec_1_14_2368_0_part13 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1664 128 = 985685647376355804171330944829 := by decide +kernel
private theorem rec_1_14_2368_0_part14 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1792 128 = 891188191720962705108042579619 := by decide +kernel
private theorem rec_1_14_2368_0_part15 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1920 128 = 798773898798867107618082090837 := by decide +kernel
private theorem rec_1_14_2368_0_part16 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2048 128 = 708419049813273005345087199516 := by decide +kernel
private theorem rec_1_14_2368_0_part17 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2176 128 = 620099968262003921345484128783 := by decide +kernel
private theorem rec_1_14_2368_0_part18 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2304 128 = 533793019884249226883015753113 := by decide +kernel
private theorem rec_1_14_2368_0_part19 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2432 128 = 449474612782325790762067840173 := by decide +kernel
private theorem rec_1_14_2368_0_part20 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2560 128 = 367121197460027131579532970873 := by decide +kernel
private theorem rec_1_14_2368_0_part21 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2688 128 = 286709266580721077950214690144 := by decide +kernel
private theorem rec_1_14_2368_0_part22 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2816 128 = 208215355031152671140947761606 := by decide +kernel
private theorem rec_1_14_2368_0_part23 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2944 128 = 131616040015464609117635785651 := by decide +kernel
private theorem rec_1_14_2368_0_part24 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 3072 128 = 56887940871726299563680403062 := by decide +kernel
private theorem rec_1_14_2368_0_part25 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 3200 35 = 2789288823547358338299398337 := by decide +kernel
private theorem rec_1_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 128 256 = 4460236822647921542710675707456 :=
  phaseBlock_append rec_1_14_2368_0_part1 rec_1_14_2368_0_part2 rfl rfl rfl
private theorem rec_1_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 0 384 = 6874779028848653839897707252064 :=
  phaseBlock_append rec_1_14_2368_0_part0 rec_1_14_2368_0_join0 rfl rfl rfl
private theorem rec_1_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 512 256 = 3753327661507359455829971007040 :=
  phaseBlock_append rec_1_14_2368_0_part4 rec_1_14_2368_0_part5 rfl rfl rfl
private theorem rec_1_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 384 384 = 5803786465591300586666117962080 :=
  phaseBlock_append rec_1_14_2368_0_part3 rec_1_14_2368_0_join2 rfl rfl rfl
private theorem rec_1_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 0 768 = 12678565494439954426563825214144 :=
  phaseBlock_append rec_1_14_2368_0_join1 rec_1_14_2368_0_join3 rfl rfl rfl
private theorem rec_1_14_2368_0_join5 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 896 256 = 3087993657097724122826759853632 :=
  phaseBlock_append rec_1_14_2368_0_part7 rec_1_14_2368_0_part8 rfl rfl rfl
private theorem rec_1_14_2368_0_join6 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 768 384 = 4795481919733931075958660573536 :=
  phaseBlock_append rec_1_14_2368_0_part6 rec_1_14_2368_0_join5 rfl rfl rfl
private theorem rec_1_14_2368_0_join7 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1152 256 = 2666894601476051804936464897600 :=
  phaseBlock_append rec_1_14_2368_0_part9 rec_1_14_2368_0_part10 rfl rfl rfl
private theorem rec_1_14_2368_0_join8 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1408 256 = 2263314830495441541469772240012 :=
  phaseBlock_append rec_1_14_2368_0_part11 rec_1_14_2368_0_part12 rfl rfl rfl
private theorem rec_1_14_2368_0_join9 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1152 512 = 4930209431971493346406237137612 :=
  phaseBlock_append rec_1_14_2368_0_join7 rec_1_14_2368_0_join8 rfl rfl rfl
private theorem rec_1_14_2368_0_join10 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 768 896 = 9725691351705424422364897711148 :=
  phaseBlock_append rec_1_14_2368_0_join6 rec_1_14_2368_0_join9 rfl rfl rfl
private theorem rec_1_14_2368_0_join11 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 0 1664 = 22404256846145378848928722925292 :=
  phaseBlock_append rec_1_14_2368_0_join4 rec_1_14_2368_0_join10 rfl rfl rfl
private theorem rec_1_14_2368_0_join12 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1792 256 = 1689962090519829812726124670456 :=
  phaseBlock_append rec_1_14_2368_0_part14 rec_1_14_2368_0_part15 rfl rfl rfl
private theorem rec_1_14_2368_0_join13 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1664 384 = 2675647737896185616897455615285 :=
  phaseBlock_append rec_1_14_2368_0_part13 rec_1_14_2368_0_join12 rfl rfl rfl
private theorem rec_1_14_2368_0_join14 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2176 256 = 1153892988146253148228499881896 :=
  phaseBlock_append rec_1_14_2368_0_part17 rec_1_14_2368_0_part18 rfl rfl rfl
private theorem rec_1_14_2368_0_join15 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2048 384 = 1862312037959526153573587081412 :=
  phaseBlock_append rec_1_14_2368_0_part16 rec_1_14_2368_0_join14 rfl rfl rfl
private theorem rec_1_14_2368_0_join16 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1664 768 = 4537959775855711770471042696697 :=
  phaseBlock_append rec_1_14_2368_0_join13 rec_1_14_2368_0_join15 rfl rfl rfl
private theorem rec_1_14_2368_0_join17 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2560 256 = 653830464040748209529747661017 :=
  phaseBlock_append rec_1_14_2368_0_part20 rec_1_14_2368_0_part21 rfl rfl rfl
private theorem rec_1_14_2368_0_join18 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2432 384 = 1103305076823074000291815501190 :=
  phaseBlock_append rec_1_14_2368_0_part19 rec_1_14_2368_0_join17 rfl rfl rfl
private theorem rec_1_14_2368_0_join19 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2816 256 = 339831395046617280258583547257 :=
  phaseBlock_append rec_1_14_2368_0_part22 rec_1_14_2368_0_part23 rfl rfl rfl
private theorem rec_1_14_2368_0_join20 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 3072 163 = 59677229695273657901979801399 :=
  phaseBlock_append rec_1_14_2368_0_part24 rec_1_14_2368_0_part25 rfl rfl rfl
private theorem rec_1_14_2368_0_join21 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2816 419 = 399508624741890938160563348656 :=
  phaseBlock_append rec_1_14_2368_0_join19 rec_1_14_2368_0_join20 rfl rfl rfl
private theorem rec_1_14_2368_0_join22 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 2432 803 = 1502813701564964938452378849846 :=
  phaseBlock_append rec_1_14_2368_0_join18 rec_1_14_2368_0_join21 rfl rfl rfl
private theorem rec_1_14_2368_0_join23 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 1664 1571 = 6040773477420676708923421546543 :=
  phaseBlock_append rec_1_14_2368_0_join16 rec_1_14_2368_0_join22 rfl rfl rfl
private theorem rec_1_14_2368_0_join24 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 0) 0 3235 = 28445030323566055557852144471835 :=
  phaseBlock_append rec_1_14_2368_0_join11 rec_1_14_2368_0_join23 rfl rfl rfl

private theorem rec_1_14_2368_0 : fastPhase (bank 1 14).shape 179798 2368 76 1 0 2 0 = 28445030323566055557852144471835 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_1_14_2368_0_join24

private theorem rec_1_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 0 128 = 2413579609972115746770529625056 := by decide +kernel
private theorem rec_1_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 128 128 = 2289850531956372191569302582240 := by decide +kernel
private theorem rec_1_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 256 128 = 2168515461666975112695061726176 := by decide +kernel
private theorem rec_1_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 384 128 = 2049550205223959799995272827872 := by decide +kernel
private theorem rec_1_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 512 128 = 1932930611294673504087122666464 := by decide +kernel
private theorem rec_1_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 640 128 = 1818632571068634619203304567776 := by decide +kernel
private theorem rec_1_14_2368_1_part6 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 768 128 = 1706632018232391866037803942880 := by decide +kernel
private theorem rec_1_14_2368_1_part7 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 896 128 = 1596904928944383474591683826656 := by decide +kernel
private theorem rec_1_14_2368_1_part8 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1024 128 = 1489427321809796367018870416352 := by decide +kernel
private theorem rec_1_14_2368_1_part9 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1152 128 = 1384175257855425340471938610144 := by decide +kernel
private theorem rec_1_14_2368_1_part10 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1280 128 = 1281124840504532249947897545696 := by decide +kernel
private theorem rec_1_14_2368_1_part11 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1408 128 = 1180252215551705191133976138720 := by decide +kernel
private theorem rec_1_14_2368_1_part12 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1536 128 = 1081533571506541252587297567579 := by decide +kernel
private theorem rec_1_14_2368_1_part13 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1664 128 = 984945223281977857214327384573 := by decide +kernel
private theorem rec_1_14_2368_1_part14 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1792 128 = 890463593314045836935420700690 := by decide +kernel
private theorem rec_1_14_2368_1_part15 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1920 128 = 798064946889270398920916791923 := by decide +kernel
private theorem rec_1_14_2368_1_part16 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2048 128 = 707725565533202599469373898101 := by decide +kernel
private theorem rec_1_14_2368_1_part17 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2176 128 = 619421773065845604191710367442 := by decide +kernel
private theorem rec_1_14_2368_1_part18 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2304 128 = 533129935548473095492547352742 := by decide +kernel
private theorem rec_1_14_2368_1_part19 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2432 128 = 448826461405287350121957356751 := by decide +kernel
private theorem rec_1_14_2368_1_part20 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2560 128 = 366487801461624708711384247912 := by decide +kernel
private theorem rec_1_14_2368_1_part21 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2688 128 = 286090448702313959821103073407 := by decide +kernel
private theorem rec_1_14_2368_1_part22 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2816 128 = 207610938335463527377684096630 := by decide +kernel
private theorem rec_1_14_2368_1_part23 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2944 128 = 131025847886193160200872522313 := by decide +kernel
private theorem rec_1_14_2368_1_part24 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 3072 128 = 56311797013414795095149643855 := by decide +kernel
private theorem rec_1_14_2368_1_part25 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 3200 35 = 2634172105075787890403286105 := by decide +kernel
private theorem rec_1_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 128 256 = 4458365993623347304264364308416 :=
  phaseBlock_append rec_1_14_2368_1_part1 rec_1_14_2368_1_part2 rfl rfl rfl
private theorem rec_1_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 0 384 = 6871945603595463051034893933472 :=
  phaseBlock_append rec_1_14_2368_1_part0 rec_1_14_2368_1_join0 rfl rfl rfl
private theorem rec_1_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 512 256 = 3751563182363308123290427234240 :=
  phaseBlock_append rec_1_14_2368_1_part4 rec_1_14_2368_1_part5 rfl rfl rfl
private theorem rec_1_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 384 384 = 5801113387587267923285700062112 :=
  phaseBlock_append rec_1_14_2368_1_part3 rec_1_14_2368_1_join2 rfl rfl rfl
private theorem rec_1_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 0 768 = 12673058991182730974320593995584 :=
  phaseBlock_append rec_1_14_2368_1_join1 rec_1_14_2368_1_join3 rfl rfl rfl
private theorem rec_1_14_2368_1_join5 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 896 256 = 3086332250754179841610554243008 :=
  phaseBlock_append rec_1_14_2368_1_part7 rec_1_14_2368_1_part8 rfl rfl rfl
private theorem rec_1_14_2368_1_join6 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 768 384 = 4792964268986571707648358185888 :=
  phaseBlock_append rec_1_14_2368_1_part6 rec_1_14_2368_1_join5 rfl rfl rfl
private theorem rec_1_14_2368_1_join7 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1152 256 = 2665300098359957590419836155840 :=
  phaseBlock_append rec_1_14_2368_1_part9 rec_1_14_2368_1_part10 rfl rfl rfl
private theorem rec_1_14_2368_1_join8 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1408 256 = 2261785787058246443721273706299 :=
  phaseBlock_append rec_1_14_2368_1_part11 rec_1_14_2368_1_part12 rfl rfl rfl
private theorem rec_1_14_2368_1_join9 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1152 512 = 4927085885418204034141109862139 :=
  phaseBlock_append rec_1_14_2368_1_join7 rec_1_14_2368_1_join8 rfl rfl rfl
private theorem rec_1_14_2368_1_join10 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 768 896 = 9720050154404775741789468048027 :=
  phaseBlock_append rec_1_14_2368_1_join6 rec_1_14_2368_1_join9 rfl rfl rfl
private theorem rec_1_14_2368_1_join11 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 0 1664 = 22393109145587506716110062043611 :=
  phaseBlock_append rec_1_14_2368_1_join4 rec_1_14_2368_1_join10 rfl rfl rfl
private theorem rec_1_14_2368_1_join12 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1792 256 = 1688528540203316235856337492613 :=
  phaseBlock_append rec_1_14_2368_1_part14 rec_1_14_2368_1_part15 rfl rfl rfl
private theorem rec_1_14_2368_1_join13 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1664 384 = 2673473763485294093070664877186 :=
  phaseBlock_append rec_1_14_2368_1_part13 rec_1_14_2368_1_join12 rfl rfl rfl
private theorem rec_1_14_2368_1_join14 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2176 256 = 1152551708614318699684257720184 :=
  phaseBlock_append rec_1_14_2368_1_part17 rec_1_14_2368_1_part18 rfl rfl rfl
private theorem rec_1_14_2368_1_join15 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2048 384 = 1860277274147521299153631618285 :=
  phaseBlock_append rec_1_14_2368_1_part16 rec_1_14_2368_1_join14 rfl rfl rfl
private theorem rec_1_14_2368_1_join16 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1664 768 = 4533751037632815392224296495471 :=
  phaseBlock_append rec_1_14_2368_1_join13 rec_1_14_2368_1_join15 rfl rfl rfl
private theorem rec_1_14_2368_1_join17 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2560 256 = 652578250163938668532487321319 :=
  phaseBlock_append rec_1_14_2368_1_part20 rec_1_14_2368_1_part21 rfl rfl rfl
private theorem rec_1_14_2368_1_join18 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2432 384 = 1101404711569226018654444678070 :=
  phaseBlock_append rec_1_14_2368_1_part19 rec_1_14_2368_1_join17 rfl rfl rfl
private theorem rec_1_14_2368_1_join19 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2816 256 = 338636786221656687578556618943 :=
  phaseBlock_append rec_1_14_2368_1_part22 rec_1_14_2368_1_part23 rfl rfl rfl
private theorem rec_1_14_2368_1_join20 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 3072 163 = 58945969118490582985552929960 :=
  phaseBlock_append rec_1_14_2368_1_part24 rec_1_14_2368_1_part25 rfl rfl rfl
private theorem rec_1_14_2368_1_join21 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2816 419 = 397582755340147270564109548903 :=
  phaseBlock_append rec_1_14_2368_1_join19 rec_1_14_2368_1_join20 rfl rfl rfl
private theorem rec_1_14_2368_1_join22 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 2432 803 = 1498987466909373289218554226973 :=
  phaseBlock_append rec_1_14_2368_1_join18 rec_1_14_2368_1_join21 rfl rfl rfl
private theorem rec_1_14_2368_1_join23 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 1664 1571 = 6032738504542188681442850722444 :=
  phaseBlock_append rec_1_14_2368_1_join16 rec_1_14_2368_1_join22 rfl rfl rfl
private theorem rec_1_14_2368_1_join24 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2368 76 1 0 2 1) 0 3235 = 28425847650129695397552912766055 :=
  phaseBlock_append rec_1_14_2368_1_join11 rec_1_14_2368_1_join23 rfl rfl rfl

private theorem rec_1_14_2368_1 : fastPhase (bank 1 14).shape 179798 2368 76 1 0 2 1 = 28425847650129695397552912766055 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_1_14_2368_1_join24

private theorem rec_1_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 0 128 = 2414564529196405318149517854624 := by decide +kernel
private theorem rec_1_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 128 128 = 2290815647844004335100920354720 := by decide +kernel
private theorem rec_1_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 256 128 = 2169461024194190670150430156704 := by decide +kernel
private theorem rec_1_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 384 128 = 2050476463218297020235960907680 := by decide +kernel
private theorem rec_1_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 512 128 = 1933837812436638773248663357344 := by decide +kernel
private theorem rec_1_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 640 128 = 1819520961893372311269408675744 := by decide +kernel
private theorem rec_1_14_2369_0_part6 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 768 128 = 1707501844131353313805271771040 := by decide +kernel
private theorem rec_1_14_2369_0_part7 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 896 128 = 1597756434166995061026014607264 := by decide +kernel
private theorem rec_1_14_2369_0_part8 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1024 128 = 1490260749465126737000569522080 := by decide +kernel
private theorem rec_1_14_2369_0_part9 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1152 128 = 1384990849913851732933522544544 := by decide +kernel
private theorem rec_1_14_2369_0_part10 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1280 128 = 1281922837799405950401596712864 := by decide +kernel
private theorem rec_1_14_2369_0_part11 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1408 128 = 1181032857781016104590135392160 := by decide +kernel
private theorem rec_1_14_2369_0_part12 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1536 128 = 1082297097117805363697176145946 := by decide +kernel
private theorem rec_1_14_2369_0_part13 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1664 128 = 985691866271497171599011208870 := by decide +kernel
private theorem rec_1_14_2369_0_part14 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1792 128 = 891193589351838508413415940808 := by decide +kernel
private theorem rec_1_14_2369_0_part15 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1920 128 = 798778532433721477711911334855 := by decide +kernel
private theorem rec_1_14_2369_0_part16 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2048 128 = 708422975885589020687075238453 := by decide +kernel
private theorem rec_1_14_2369_0_part17 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2176 128 = 620103242297289322564600769232 := by decide +kernel
private theorem rec_1_14_2369_0_part18 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2304 128 = 533795696511940916216918498131 := by decide +kernel
private theorem rec_1_14_2369_0_part19 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2432 128 = 449476745835361018884577295061 := by decide +kernel
private theorem rec_1_14_2369_0_part20 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2560 128 = 367122839867428932011896249524 := by decide +kernel
private theorem rec_1_14_2369_0_part21 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2688 128 = 286710470399052782238743803374 := by decide +kernel
private theorem rec_1_14_2369_0_part22 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2816 128 = 208216171472179707066156704668 := by decide +kernel
private theorem rec_1_14_2369_0_part23 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2944 128 = 131616519432085442919855343968 := by decide +kernel
private theorem rec_1_14_2369_0_part24 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 3072 128 = 56888132748574066770839936769 := by decide +kernel
private theorem rec_1_14_2369_0_part25 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 3200 35 = 2789297664939360001991043018 := by decide +kernel
private theorem rec_1_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 128 256 = 4460276672038195005251350511424 :=
  phaseBlock_append rec_1_14_2369_0_part1 rec_1_14_2369_0_part2 rfl rfl rfl
private theorem rec_1_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 0 384 = 6874841201234600323400868366048 :=
  phaseBlock_append rec_1_14_2369_0_part0 rec_1_14_2369_0_join0 rfl rfl rfl
private theorem rec_1_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 512 256 = 3753358774330011084518072033088 :=
  phaseBlock_append rec_1_14_2369_0_part4 rec_1_14_2369_0_part5 rfl rfl rfl
private theorem rec_1_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 384 384 = 5803835237548308104754032940768 :=
  phaseBlock_append rec_1_14_2369_0_part3 rec_1_14_2369_0_join2 rfl rfl rfl
private theorem rec_1_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 0 768 = 12678676438782908428154901306816 :=
  phaseBlock_append rec_1_14_2369_0_join1 rec_1_14_2369_0_join3 rfl rfl rfl
private theorem rec_1_14_2369_0_join5 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 896 256 = 3088017183632121798026584129344 :=
  phaseBlock_append rec_1_14_2369_0_part7 rec_1_14_2369_0_part8 rfl rfl rfl
private theorem rec_1_14_2369_0_join6 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 768 384 = 4795519027763475111831855900384 :=
  phaseBlock_append rec_1_14_2369_0_part6 rec_1_14_2369_0_join5 rfl rfl rfl
private theorem rec_1_14_2369_0_join7 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1152 256 = 2666913687713257683335119257408 :=
  phaseBlock_append rec_1_14_2369_0_part9 rec_1_14_2369_0_part10 rfl rfl rfl
private theorem rec_1_14_2369_0_join8 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1408 256 = 2263329954898821468287311538106 :=
  phaseBlock_append rec_1_14_2369_0_part11 rec_1_14_2369_0_part12 rfl rfl rfl
private theorem rec_1_14_2369_0_join9 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1152 512 = 4930243642612079151622430795514 :=
  phaseBlock_append rec_1_14_2369_0_join7 rec_1_14_2369_0_join8 rfl rfl rfl
private theorem rec_1_14_2369_0_join10 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 768 896 = 9725762670375554263454286695898 :=
  phaseBlock_append rec_1_14_2369_0_join6 rec_1_14_2369_0_join9 rfl rfl rfl
private theorem rec_1_14_2369_0_join11 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 0 1664 = 22404439109158462691609188002714 :=
  phaseBlock_append rec_1_14_2369_0_join4 rec_1_14_2369_0_join10 rfl rfl rfl
private theorem rec_1_14_2369_0_join12 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1792 256 = 1689972121785559986125327275663 :=
  phaseBlock_append rec_1_14_2369_0_part14 rec_1_14_2369_0_part15 rfl rfl rfl
private theorem rec_1_14_2369_0_join13 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1664 384 = 2675663988057057157724338484533 :=
  phaseBlock_append rec_1_14_2369_0_part13 rec_1_14_2369_0_join12 rfl rfl rfl
private theorem rec_1_14_2369_0_join14 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2176 256 = 1153898938809230238781519267363 :=
  phaseBlock_append rec_1_14_2369_0_part17 rec_1_14_2369_0_part18 rfl rfl rfl
private theorem rec_1_14_2369_0_join15 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2048 384 = 1862321914694819259468594505816 :=
  phaseBlock_append rec_1_14_2369_0_part16 rec_1_14_2369_0_join14 rfl rfl rfl
private theorem rec_1_14_2369_0_join16 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1664 768 = 4537985902751876417192932990349 :=
  phaseBlock_append rec_1_14_2369_0_join13 rec_1_14_2369_0_join15 rfl rfl rfl
private theorem rec_1_14_2369_0_join17 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2560 256 = 653833310266481714250640052898 :=
  phaseBlock_append rec_1_14_2369_0_part20 rec_1_14_2369_0_part21 rfl rfl rfl
private theorem rec_1_14_2369_0_join18 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2432 384 = 1103310056101842733135217347959 :=
  phaseBlock_append rec_1_14_2369_0_part19 rec_1_14_2369_0_join17 rfl rfl rfl
private theorem rec_1_14_2369_0_join19 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2816 256 = 339832690904265149986012048636 :=
  phaseBlock_append rec_1_14_2369_0_part22 rec_1_14_2369_0_part23 rfl rfl rfl
private theorem rec_1_14_2369_0_join20 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 3072 163 = 59677430413513426772830979787 :=
  phaseBlock_append rec_1_14_2369_0_part24 rec_1_14_2369_0_part25 rfl rfl rfl
private theorem rec_1_14_2369_0_join21 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2816 419 = 399510121317778576758843028423 :=
  phaseBlock_append rec_1_14_2369_0_join19 rec_1_14_2369_0_join20 rfl rfl rfl
private theorem rec_1_14_2369_0_join22 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 2432 803 = 1502820177419621309894060376382 :=
  phaseBlock_append rec_1_14_2369_0_join18 rec_1_14_2369_0_join21 rfl rfl rfl
private theorem rec_1_14_2369_0_join23 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 1664 1571 = 6040806080171497727086993366731 :=
  phaseBlock_append rec_1_14_2369_0_join16 rec_1_14_2369_0_join22 rfl rfl rfl
private theorem rec_1_14_2369_0_join24 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 0) 0 3235 = 28445245189329960418696181369445 :=
  phaseBlock_append rec_1_14_2369_0_join11 rec_1_14_2369_0_join23 rfl rfl rfl

private theorem rec_1_14_2369_0 : fastPhase (bank 1 14).shape 179798 2369 76 1 0 2 0 = 28445245189329960418696181369445 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_1_14_2369_0_join24

private theorem rec_1_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 0 128 = 2413601925751587301803714492576 := by decide +kernel
private theorem rec_1_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 128 128 = 2289871226872809580937115576480 := by decide +kernel
private theorem rec_1_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 256 128 = 2168534602498522381519285262496 := by decide +kernel
private theorem rec_1_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 384 128 = 2049567857924401691602085513376 := by decide +kernel
private theorem rec_1_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 512 128 = 1932946840994913677799219722400 := by decide +kernel
private theorem rec_1_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 640 128 = 1818647442078172988522716031136 := by decide +kernel
private theorem rec_1_14_2369_1_part6 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 768 128 = 1706645594040801057219410647200 := by decide +kernel
private theorem rec_1_14_2369_1_part7 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 896 128 = 1596917272222784405607431162016 := by decide +kernel
private theorem rec_1_14_2369_1_part8 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1024 128 = 1489438494412332946912679868576 := by decide +kernel
private theorem rec_1_14_2369_1_part9 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1152 128 = 1384185320820738289105317079200 := by decide +kernel
private theorem rec_1_14_2369_1_part10 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1280 128 = 1281133854057232038136244443296 := by decide +kernel
private theorem rec_1_14_2369_1_part11 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1408 128 = 1180260239103844101173588265120 := by decide +kernel
private theorem rec_1_14_2369_1_part12 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1536 128 = 1081540663542142673310460589631 := by decide +kernel
private theorem rec_1_14_2369_1_part13 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1664 128 = 984951438100996066105289016979 := by decide +kernel
private theorem rec_1_14_2369_1_part14 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1792 128 = 890468987086633449948133874781 := by decide +kernel
private theorem rec_1_14_2369_1_part15 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1920 128 = 798069576879691862088886916898 := by decide +kernel
private theorem rec_1_14_2369_1_part16 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2048 128 = 707729488170934892670443956794 := by decide +kernel
private theorem rec_1_14_2369_1_part17 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2176 128 = 619425043872427138183827375051 := by decide +kernel
private theorem rec_1_14_2369_1_part18 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2304 128 = 533132609149416764654844304752 := by decide +kernel
private theorem rec_1_14_2369_1_part19 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2432 128 = 448828591629539634100992624573 := by decide +kernel
private theorem rec_1_14_2369_1_part20 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2560 128 = 366489441234262245344752373277 := by decide +kernel
private theorem rec_1_14_2369_1_part21 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2688 128 = 286091650075983190158296124192 := by decide +kernel
private theorem rec_1_14_2369_1_part22 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2816 128 = 207611752518000117065279794056 := by decide +kernel
private theorem rec_1_14_2369_1_part23 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2944 128 = 131026325226557926258909109814 := by decide +kernel
private theorem rec_1_14_2369_1_part24 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 3072 128 = 56311986992332715643391845162 := by decide +kernel
private theorem rec_1_14_2369_1_part25 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 3200 35 = 2634180458049504211805971437 := by decide +kernel
private theorem rec_1_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 128 256 = 4458405829371331962456400838976 :=
  phaseBlock_append rec_1_14_2369_1_part1 rec_1_14_2369_1_part2 rfl rfl rfl
private theorem rec_1_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 0 384 = 6872007755122919264260115331552 :=
  phaseBlock_append rec_1_14_2369_1_part0 rec_1_14_2369_1_join0 rfl rfl rfl
private theorem rec_1_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 512 256 = 3751594283073086666321935753536 :=
  phaseBlock_append rec_1_14_2369_1_part4 rec_1_14_2369_1_part5 rfl rfl rfl
private theorem rec_1_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 384 384 = 5801162140997488357924021266912 :=
  phaseBlock_append rec_1_14_2369_1_part3 rec_1_14_2369_1_join2 rfl rfl rfl
private theorem rec_1_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 0 768 = 12673169896120407622184136598464 :=
  phaseBlock_append rec_1_14_2369_1_join1 rec_1_14_2369_1_join3 rfl rfl rfl
private theorem rec_1_14_2369_1_join5 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 896 256 = 3086355766635117352520111030592 :=
  phaseBlock_append rec_1_14_2369_1_part7 rec_1_14_2369_1_part8 rfl rfl rfl
private theorem rec_1_14_2369_1_join6 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 768 384 = 4793001360675918409739521677792 :=
  phaseBlock_append rec_1_14_2369_1_part6 rec_1_14_2369_1_join5 rfl rfl rfl
private theorem rec_1_14_2369_1_join7 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1152 256 = 2665319174877970327241561522496 :=
  phaseBlock_append rec_1_14_2369_1_part9 rec_1_14_2369_1_part10 rfl rfl rfl
private theorem rec_1_14_2369_1_join8 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1408 256 = 2261800902645986774484048854751 :=
  phaseBlock_append rec_1_14_2369_1_part11 rec_1_14_2369_1_part12 rfl rfl rfl
private theorem rec_1_14_2369_1_join9 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1152 512 = 4927120077523957101725610377247 :=
  phaseBlock_append rec_1_14_2369_1_join7 rec_1_14_2369_1_join8 rfl rfl rfl
private theorem rec_1_14_2369_1_join10 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 768 896 = 9720121438199875511465132055039 :=
  phaseBlock_append rec_1_14_2369_1_join6 rec_1_14_2369_1_join9 rfl rfl rfl
private theorem rec_1_14_2369_1_join11 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 0 1664 = 22393291334320283133649268653503 :=
  phaseBlock_append rec_1_14_2369_1_join4 rec_1_14_2369_1_join10 rfl rfl rfl
private theorem rec_1_14_2369_1_join12 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1792 256 = 1688538563966325312037020791679 :=
  phaseBlock_append rec_1_14_2369_1_part14 rec_1_14_2369_1_part15 rfl rfl rfl
private theorem rec_1_14_2369_1_join13 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1664 384 = 2673490002067321378142309808658 :=
  phaseBlock_append rec_1_14_2369_1_part13 rec_1_14_2369_1_join12 rfl rfl rfl
private theorem rec_1_14_2369_1_join14 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2176 256 = 1152557653021843902838671679803 :=
  phaseBlock_append rec_1_14_2369_1_part17 rec_1_14_2369_1_part18 rfl rfl rfl
private theorem rec_1_14_2369_1_join15 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2048 384 = 1860287141192778795509115636597 :=
  phaseBlock_append rec_1_14_2369_1_part16 rec_1_14_2369_1_join14 rfl rfl rfl
private theorem rec_1_14_2369_1_join16 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1664 768 = 4533777143260100173651425445255 :=
  phaseBlock_append rec_1_14_2369_1_join13 rec_1_14_2369_1_join15 rfl rfl rfl
private theorem rec_1_14_2369_1_join17 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2560 256 = 652581091310245435503048497469 :=
  phaseBlock_append rec_1_14_2369_1_part20 rec_1_14_2369_1_part21 rfl rfl rfl
private theorem rec_1_14_2369_1_join18 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2432 384 = 1101409682939785069604041122042 :=
  phaseBlock_append rec_1_14_2369_1_part19 rec_1_14_2369_1_join17 rfl rfl rfl
private theorem rec_1_14_2369_1_join19 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2816 256 = 338638077744558043324188903870 :=
  phaseBlock_append rec_1_14_2369_1_part22 rec_1_14_2369_1_part23 rfl rfl rfl
private theorem rec_1_14_2369_1_join20 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 3072 163 = 58946167450382219855197816599 :=
  phaseBlock_append rec_1_14_2369_1_part24 rec_1_14_2369_1_part25 rfl rfl rfl
private theorem rec_1_14_2369_1_join21 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2816 419 = 397584245194940263179386720469 :=
  phaseBlock_append rec_1_14_2369_1_join19 rec_1_14_2369_1_join20 rfl rfl rfl
private theorem rec_1_14_2369_1_join22 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 2432 803 = 1498993928134725332783427842511 :=
  phaseBlock_append rec_1_14_2369_1_join18 rec_1_14_2369_1_join21 rfl rfl rfl
private theorem rec_1_14_2369_1_join23 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 1664 1571 = 6032771071394825506434853287766 :=
  phaseBlock_append rec_1_14_2369_1_join16 rec_1_14_2369_1_join22 rfl rfl rfl
private theorem rec_1_14_2369_1_join24 :
    phaseBlock (fastLayerG (bank 1 14).shape 179798 2369 76 1 0 2 1) 0 3235 = 28426062405715108640084121941269 :=
  phaseBlock_append rec_1_14_2369_1_join11 rec_1_14_2369_1_join23 rfl rfl rfl

private theorem rec_1_14_2369_1 : fastPhase (bank 1 14).shape 179798 2369 76 1 0 2 1 = 28426062405715108640084121941269 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_1_14_2369_1_join24

theorem receipt_1_14 : Checked (bank 1 14) 76 0 2 := by
  refine checked_from_values (bank 1 14) 76 0 2
    (P3_7_1.checked (bank 1 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_14605_3234)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_14_2368_0 rec_1_14_2368_1 rec_1_14_2369_0 rec_1_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 0 128 = 9745667725639005308487039320256 := by decide +kernel
private theorem rec_1_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 128 128 = 9357933503542121737077118968000 := by decide +kernel
private theorem rec_1_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 256 128 = 8976013350368639867376097378496 := by decide +kernel
private theorem rec_1_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 384 128 = 8599861955196197712870735536320 := by decide +kernel
private theorem rec_1_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 512 128 = 8229434065448346783912462680256 := by decide +kernel
private theorem rec_1_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 640 128 = 7864684486869411270563161841856 := by decide +kernel
private theorem rec_1_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 768 128 = 7505568083499347225440955384000 := by decide +kernel
private theorem rec_1_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 896 128 = 7152039777648601746565990539456 := by decide +kernel
private theorem rec_1_15_2368_0_part8 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1024 128 = 6804054549872972160206224949440 := by decide +kernel
private theorem rec_1_15_2368_0_part9 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1152 128 = 6461567438948465203723212202176 := by decide +kernel
private theorem rec_1_15_2368_0_part10 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1280 128 = 6124533541846156208417887371456 := by decide +kernel
private theorem rec_1_15_2368_0_part11 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1408 128 = 5792908013707048282376352555200 := by decide +kernel
private theorem rec_1_15_2368_0_part12 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1536 128 = 5466646067816931493315662414016 := by decide +kernel
private theorem rec_1_15_2368_0_part13 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1664 128 = 5145702975581242051429609709760 := by decide +kernel
private theorem rec_1_15_2368_0_part14 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1792 128 = 4830034066499921492234510844096 := by decide +kernel
private theorem rec_1_15_2368_0_part15 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1920 128 = 4519594728142275859414991397056 := by decide +kernel
private theorem rec_1_15_2368_0_part16 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2048 128 = 4214340434334521701080585345226 := by decide +kernel
private theorem rec_1_15_2368_0_part17 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2176 128 = 3914227073444289054997562866702 := by decide +kernel
private theorem rec_1_15_2368_0_part18 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2304 128 = 3619210395348843701220779638422 := by decide +kernel
private theorem rec_1_15_2368_0_part19 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2432 128 = 3329245882554411712236047959754 := by decide +kernel
private theorem rec_1_15_2368_0_part20 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2560 128 = 3044289069605949678603747259706 := by decide +kernel
private theorem rec_1_15_2368_0_part21 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2688 128 = 2764295548800749543780445215908 := by decide +kernel
private theorem rec_1_15_2368_0_part22 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2816 128 = 2489220970271673502374177871740 := by decide +kernel
private theorem rec_1_15_2368_0_part23 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2944 128 = 2219021042650409850625053538127 := by decide +kernel
private theorem rec_1_15_2368_0_part24 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3072 128 = 1953651532569946960902164191805 := by decide +kernel
private theorem rec_1_15_2368_0_part25 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3200 128 = 1693068264468774660769379280786 := by decide +kernel
private theorem rec_1_15_2368_0_part26 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3328 128 = 1437227120798190136287854870837 := by decide +kernel
private theorem rec_1_15_2368_0_part27 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3456 128 = 1186084042254398263480846656630 := by decide +kernel
private theorem rec_1_15_2368_0_part28 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3584 128 = 939595027263744359750321795715 := by decide +kernel
private theorem rec_1_15_2368_0_part29 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3712 128 = 697716132112629484029174970787 := by decide +kernel
private theorem rec_1_15_2368_0_part30 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3840 128 = 460403471175338277845967902215 := by decide +kernel
private theorem rec_1_15_2368_0_part31 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3968 128 = 227613216607173907340825636835 := by decide +kernel
private theorem rec_1_15_2368_0_part32 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 4096 63 = 27911544878367353125670257590 := by decide +kernel
private theorem rec_1_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 0 256 = 19103601229181127045564158288256 :=
  phaseBlock_append rec_1_15_2368_0_part0 rec_1_15_2368_0_part1 rfl rfl rfl
private theorem rec_1_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 256 256 = 17575875305564837580246832914816 :=
  phaseBlock_append rec_1_15_2368_0_part2 rec_1_15_2368_0_part3 rfl rfl rfl
private theorem rec_1_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 0 512 = 36679476534745964625810991203072 :=
  phaseBlock_append rec_1_15_2368_0_join0 rec_1_15_2368_0_join1 rfl rfl rfl
private theorem rec_1_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 512 256 = 16094118552317758054475624522112 :=
  phaseBlock_append rec_1_15_2368_0_part4 rec_1_15_2368_0_part5 rfl rfl rfl
private theorem rec_1_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 768 256 = 14657607861147948972006945923456 :=
  phaseBlock_append rec_1_15_2368_0_part6 rec_1_15_2368_0_part7 rfl rfl rfl
private theorem rec_1_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 512 512 = 30751726413465707026482570445568 :=
  phaseBlock_append rec_1_15_2368_0_join3 rec_1_15_2368_0_join4 rfl rfl rfl
private theorem rec_1_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 0 1024 = 67431202948211671652293561648640 :=
  phaseBlock_append rec_1_15_2368_0_join2 rec_1_15_2368_0_join5 rfl rfl rfl
private theorem rec_1_15_2368_0_join7 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1024 256 = 13265621988821437363929437151616 :=
  phaseBlock_append rec_1_15_2368_0_part8 rec_1_15_2368_0_part9 rfl rfl rfl
private theorem rec_1_15_2368_0_join8 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1280 256 = 11917441555553204490794239926656 :=
  phaseBlock_append rec_1_15_2368_0_part10 rec_1_15_2368_0_part11 rfl rfl rfl
private theorem rec_1_15_2368_0_join9 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1024 512 = 25183063544374641854723677078272 :=
  phaseBlock_append rec_1_15_2368_0_join7 rec_1_15_2368_0_join8 rfl rfl rfl
private theorem rec_1_15_2368_0_join10 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1536 256 = 10612349043398173544745272123776 :=
  phaseBlock_append rec_1_15_2368_0_part12 rec_1_15_2368_0_part13 rfl rfl rfl
private theorem rec_1_15_2368_0_join11 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1792 256 = 9349628794642197351649502241152 :=
  phaseBlock_append rec_1_15_2368_0_part14 rec_1_15_2368_0_part15 rfl rfl rfl
private theorem rec_1_15_2368_0_join12 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1536 512 = 19961977838040370896394774364928 :=
  phaseBlock_append rec_1_15_2368_0_join10 rec_1_15_2368_0_join11 rfl rfl rfl
private theorem rec_1_15_2368_0_join13 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 1024 1024 = 45145041382415012751118451443200 :=
  phaseBlock_append rec_1_15_2368_0_join9 rec_1_15_2368_0_join12 rfl rfl rfl
private theorem rec_1_15_2368_0_join14 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 0 2048 = 112576244330626684403412013091840 :=
  phaseBlock_append rec_1_15_2368_0_join6 rec_1_15_2368_0_join13 rfl rfl rfl
private theorem rec_1_15_2368_0_join15 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2048 256 = 8128567507778810756078148211928 :=
  phaseBlock_append rec_1_15_2368_0_part16 rec_1_15_2368_0_part17 rfl rfl rfl
private theorem rec_1_15_2368_0_join16 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2304 256 = 6948456277903255413456827598176 :=
  phaseBlock_append rec_1_15_2368_0_part18 rec_1_15_2368_0_part19 rfl rfl rfl
private theorem rec_1_15_2368_0_join17 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2048 512 = 15077023785682066169534975810104 :=
  phaseBlock_append rec_1_15_2368_0_join15 rec_1_15_2368_0_join16 rfl rfl rfl
private theorem rec_1_15_2368_0_join18 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2560 256 = 5808584618406699222384192475614 :=
  phaseBlock_append rec_1_15_2368_0_part20 rec_1_15_2368_0_part21 rfl rfl rfl
private theorem rec_1_15_2368_0_join19 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2816 256 = 4708242012922083352999231409867 :=
  phaseBlock_append rec_1_15_2368_0_part22 rec_1_15_2368_0_part23 rfl rfl rfl
private theorem rec_1_15_2368_0_join20 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2560 512 = 10516826631328782575383423885481 :=
  phaseBlock_append rec_1_15_2368_0_join18 rec_1_15_2368_0_join19 rfl rfl rfl
private theorem rec_1_15_2368_0_join21 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2048 1024 = 25593850417010848744918399695585 :=
  phaseBlock_append rec_1_15_2368_0_join17 rec_1_15_2368_0_join20 rfl rfl rfl
private theorem rec_1_15_2368_0_join22 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3072 256 = 3646719797038721621671543472591 :=
  phaseBlock_append rec_1_15_2368_0_part24 rec_1_15_2368_0_part25 rfl rfl rfl
private theorem rec_1_15_2368_0_join23 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3328 256 = 2623311163052588399768701527467 :=
  phaseBlock_append rec_1_15_2368_0_part26 rec_1_15_2368_0_part27 rfl rfl rfl
private theorem rec_1_15_2368_0_join24 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3072 512 = 6270030960091310021440245000058 :=
  phaseBlock_append rec_1_15_2368_0_join22 rec_1_15_2368_0_join23 rfl rfl rfl
private theorem rec_1_15_2368_0_join25 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3584 256 = 1637311159376373843779496766502 :=
  phaseBlock_append rec_1_15_2368_0_part28 rec_1_15_2368_0_part29 rfl rfl rfl
private theorem rec_1_15_2368_0_join26 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3968 191 = 255524761485541260466495894425 :=
  phaseBlock_append rec_1_15_2368_0_part31 rec_1_15_2368_0_part32 rfl rfl rfl
private theorem rec_1_15_2368_0_join27 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3840 319 = 715928232660879538312463796640 :=
  phaseBlock_append rec_1_15_2368_0_part30 rec_1_15_2368_0_join26 rfl rfl rfl
private theorem rec_1_15_2368_0_join28 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3584 575 = 2353239392037253382091960563142 :=
  phaseBlock_append rec_1_15_2368_0_join25 rec_1_15_2368_0_join27 rfl rfl rfl
private theorem rec_1_15_2368_0_join29 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 3072 1087 = 8623270352128563403532205563200 :=
  phaseBlock_append rec_1_15_2368_0_join24 rec_1_15_2368_0_join28 rfl rfl rfl
private theorem rec_1_15_2368_0_join30 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 2048 2111 = 34217120769139412148450605258785 :=
  phaseBlock_append rec_1_15_2368_0_join21 rec_1_15_2368_0_join29 rfl rfl rfl
private theorem rec_1_15_2368_0_join31 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 0) 0 4159 = 146793365099766096551862618350625 :=
  phaseBlock_append rec_1_15_2368_0_join14 rec_1_15_2368_0_join30 rfl rfl rfl

private theorem rec_1_15_2368_0 : fastPhase (bank 1 15).shape 179798 2368 105 1 0 2 0 = 146793365099766096551862618350625 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_1_15_2368_0_join31

private theorem rec_1_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 0 128 = 9742658325107797683425204431680 := by decide +kernel
private theorem rec_1_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 128 128 = 9354968202541877839462876040000 := by decide +kernel
private theorem rec_1_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 256 128 = 8973091805922476473437555305280 := by decide +kernel
private theorem rec_1_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 384 128 = 8596983824771953145011349588800 := by decide +kernel
private theorem rec_1_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 512 128 = 8226599006958388403542319065920 := by decide +kernel
private theorem rec_1_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 640 128 = 7861892158670442970930262264640 := by decide +kernel
private theorem rec_1_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 768 128 = 7502818144392216924462501604160 := by decide +kernel
private theorem rec_1_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 896 128 = 7149331886878108879659668933440 := by decide +kernel
private theorem rec_1_15_2368_1_part8 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1024 128 = 6801388367127675173121491069760 := by decide +kernel
private theorem rec_1_15_2368_1_part9 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1152 128 = 6458942624360489045372575337280 := by decide +kernel
private theorem rec_1_15_2368_1_part10 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1280 128 = 6121949755990999823708195105600 := by decide +kernel
private theorem rec_1_15_2368_1_part11 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1408 128 = 5790364917603392105040075328320 := by decide +kernel
private theorem rec_1_15_2368_1_part12 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1536 128 = 5464143322926444938742178081600 := by decide +kernel
private theorem rec_1_15_2368_1_part13 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1664 128 = 5143240243808391009496488102720 := by decide +kernel
private theorem rec_1_15_2368_1_part14 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1792 128 = 4827611010191775820138798328640 := by decide +kernel
private theorem rec_1_15_2368_1_part15 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1920 128 = 4517211010088316874504495434560 := by decide +kernel
private theorem rec_1_15_2368_1_part16 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2048 128 = 4211995717752166204679508252751 := by decide +kernel
private theorem rec_1_15_2368_1_part17 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2176 128 = 3911921021787026171627115985167 := by decide +kernel
private theorem rec_1_15_2368_1_part18 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2304 128 = 3616942672361639541836719377243 := by decide +kernel
private theorem rec_1_15_2368_1_part19 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2432 128 = 3327016152421660985690803521797 := by decide +kernel
private theorem rec_1_15_2368_1_part20 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2560 128 = 3042096996954097914079695106143 := by decide +kernel
private theorem rec_1_15_2368_1_part21 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2688 128 = 2762140798698277812716252319295 := by decide +kernel
private theorem rec_1_15_2368_1_part22 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2816 128 = 2487103208229114168154167107007 := by decide +kernel
private theorem rec_1_15_2368_1_part23 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2944 128 = 2216939934619885112129474117577 := by decide +kernel
private theorem rec_1_15_2368_1_part24 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3072 128 = 1951606744944949078127299341167 := by decide +kernel
private theorem rec_1_15_2368_1_part25 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3200 128 = 1691059464084158319209706392749 := by decide +kernel
private theorem rec_1_15_2368_1_part26 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3328 128 = 1435253974930038969244666534677 := by decide +kernel
private theorem rec_1_15_2368_1_part27 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3456 128 = 1184146218619495313842290935244 := by decide +kernel
private theorem rec_1_15_2368_1_part28 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3584 128 = 937692194019578670010427381156 := by decide +kernel
private theorem rec_1_15_2368_1_part29 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3712 128 = 695847957857403377150753864895 := by decide +kernel
private theorem rec_1_15_2368_1_part30 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3840 128 = 458569624947442997992105080643 := by decide +kernel
private theorem rec_1_15_2368_1_part31 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3968 128 = 225813367885050223111475192769 := by decide +kernel
private theorem rec_1_15_2368_1_part32 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 4096 63 = 27038065620864537127379329329 := by decide +kernel
private theorem rec_1_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 0 256 = 19097626527649675522888080471680 :=
  phaseBlock_append rec_1_15_2368_1_part0 rec_1_15_2368_1_part1 rfl rfl rfl
private theorem rec_1_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 256 256 = 17570075630694429618448904894080 :=
  phaseBlock_append rec_1_15_2368_1_part2 rec_1_15_2368_1_part3 rfl rfl rfl
private theorem rec_1_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 0 512 = 36667702158344105141336985365760 :=
  phaseBlock_append rec_1_15_2368_1_join0 rec_1_15_2368_1_join1 rfl rfl rfl
private theorem rec_1_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 512 256 = 16088491165628831374472581330560 :=
  phaseBlock_append rec_1_15_2368_1_part4 rec_1_15_2368_1_part5 rfl rfl rfl
private theorem rec_1_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 768 256 = 14652150031270325804122170537600 :=
  phaseBlock_append rec_1_15_2368_1_part6 rec_1_15_2368_1_part7 rfl rfl rfl
private theorem rec_1_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 512 512 = 30740641196899157178594751868160 :=
  phaseBlock_append rec_1_15_2368_1_join3 rec_1_15_2368_1_join4 rfl rfl rfl
private theorem rec_1_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 0 1024 = 67408343355243262319931737233920 :=
  phaseBlock_append rec_1_15_2368_1_join2 rec_1_15_2368_1_join5 rfl rfl rfl
private theorem rec_1_15_2368_1_join7 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1024 256 = 13260330991488164218494066407040 :=
  phaseBlock_append rec_1_15_2368_1_part8 rec_1_15_2368_1_part9 rfl rfl rfl
private theorem rec_1_15_2368_1_join8 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1280 256 = 11912314673594391928748270433920 :=
  phaseBlock_append rec_1_15_2368_1_part10 rec_1_15_2368_1_part11 rfl rfl rfl
private theorem rec_1_15_2368_1_join9 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1024 512 = 25172645665082556147242336840960 :=
  phaseBlock_append rec_1_15_2368_1_join7 rec_1_15_2368_1_join8 rfl rfl rfl
private theorem rec_1_15_2368_1_join10 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1536 256 = 10607383566734835948238666184320 :=
  phaseBlock_append rec_1_15_2368_1_part12 rec_1_15_2368_1_part13 rfl rfl rfl
private theorem rec_1_15_2368_1_join11 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1792 256 = 9344822020280092694643293763200 :=
  phaseBlock_append rec_1_15_2368_1_part14 rec_1_15_2368_1_part15 rfl rfl rfl
private theorem rec_1_15_2368_1_join12 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1536 512 = 19952205587014928642881959947520 :=
  phaseBlock_append rec_1_15_2368_1_join10 rec_1_15_2368_1_join11 rfl rfl rfl
private theorem rec_1_15_2368_1_join13 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 1024 1024 = 45124851252097484790124296788480 :=
  phaseBlock_append rec_1_15_2368_1_join9 rec_1_15_2368_1_join12 rfl rfl rfl
private theorem rec_1_15_2368_1_join14 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 0 2048 = 112533194607340747110056034022400 :=
  phaseBlock_append rec_1_15_2368_1_join6 rec_1_15_2368_1_join13 rfl rfl rfl
private theorem rec_1_15_2368_1_join15 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2048 256 = 8123916739539192376306624237918 :=
  phaseBlock_append rec_1_15_2368_1_part16 rec_1_15_2368_1_part17 rfl rfl rfl
private theorem rec_1_15_2368_1_join16 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2304 256 = 6943958824783300527527522899040 :=
  phaseBlock_append rec_1_15_2368_1_part18 rec_1_15_2368_1_part19 rfl rfl rfl
private theorem rec_1_15_2368_1_join17 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2048 512 = 15067875564322492903834147136958 :=
  phaseBlock_append rec_1_15_2368_1_join15 rec_1_15_2368_1_join16 rfl rfl rfl
private theorem rec_1_15_2368_1_join18 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2560 256 = 5804237795652375726795947425438 :=
  phaseBlock_append rec_1_15_2368_1_part20 rec_1_15_2368_1_part21 rfl rfl rfl
private theorem rec_1_15_2368_1_join19 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2816 256 = 4704043142848999280283641224584 :=
  phaseBlock_append rec_1_15_2368_1_part22 rec_1_15_2368_1_part23 rfl rfl rfl
private theorem rec_1_15_2368_1_join20 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2560 512 = 10508280938501375007079588650022 :=
  phaseBlock_append rec_1_15_2368_1_join18 rec_1_15_2368_1_join19 rfl rfl rfl
private theorem rec_1_15_2368_1_join21 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2048 1024 = 25576156502823867910913735786980 :=
  phaseBlock_append rec_1_15_2368_1_join17 rec_1_15_2368_1_join20 rfl rfl rfl
private theorem rec_1_15_2368_1_join22 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3072 256 = 3642666209029107397337005733916 :=
  phaseBlock_append rec_1_15_2368_1_part24 rec_1_15_2368_1_part25 rfl rfl rfl
private theorem rec_1_15_2368_1_join23 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3328 256 = 2619400193549534283086957469921 :=
  phaseBlock_append rec_1_15_2368_1_part26 rec_1_15_2368_1_part27 rfl rfl rfl
private theorem rec_1_15_2368_1_join24 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3072 512 = 6262066402578641680423963203837 :=
  phaseBlock_append rec_1_15_2368_1_join22 rec_1_15_2368_1_join23 rfl rfl rfl
private theorem rec_1_15_2368_1_join25 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3584 256 = 1633540151876982047161181246051 :=
  phaseBlock_append rec_1_15_2368_1_part28 rec_1_15_2368_1_part29 rfl rfl rfl
private theorem rec_1_15_2368_1_join26 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3968 191 = 252851433505914760238854522098 :=
  phaseBlock_append rec_1_15_2368_1_part31 rec_1_15_2368_1_part32 rfl rfl rfl
private theorem rec_1_15_2368_1_join27 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3840 319 = 711421058453357758230959602741 :=
  phaseBlock_append rec_1_15_2368_1_part30 rec_1_15_2368_1_join26 rfl rfl rfl
private theorem rec_1_15_2368_1_join28 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3584 575 = 2344961210330339805392140848792 :=
  phaseBlock_append rec_1_15_2368_1_join25 rec_1_15_2368_1_join27 rfl rfl rfl
private theorem rec_1_15_2368_1_join29 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 3072 1087 = 8607027612908981485816104052629 :=
  phaseBlock_append rec_1_15_2368_1_join24 rec_1_15_2368_1_join28 rfl rfl rfl
private theorem rec_1_15_2368_1_join30 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 2048 2111 = 34183184115732849396729839839609 :=
  phaseBlock_append rec_1_15_2368_1_join21 rec_1_15_2368_1_join29 rfl rfl rfl
private theorem rec_1_15_2368_1_join31 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2368 105 1 0 2 1) 0 4159 = 146716378723073596506785873862009 :=
  phaseBlock_append rec_1_15_2368_1_join14 rec_1_15_2368_1_join30 rfl rfl rfl

private theorem rec_1_15_2368_1 : fastPhase (bank 1 15).shape 179798 2368 105 1 0 2 1 = 146716378723073596506785873862009 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_1_15_2368_1_join31

private theorem rec_1_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 0 128 = 9745757919528931145364807060864 := by decide +kernel
private theorem rec_1_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 128 128 = 9358018596922260001172107447680 := by decide +kernel
private theorem rec_1_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 256 128 = 8976093505781929101245131853184 := by decide +kernel
private theorem rec_1_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 384 128 = 8599937333639286659325282733440 := by decide +kernel
private theorem rec_1_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 512 128 = 8229504826373622370894633405824 := by decide +kernel
private theorem rec_1_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 640 128 = 7864750788187025716412411366784 := by decide +kernel
private theorem rec_1_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 768 128 = 7505630081579244264551481609600 := by decide +kernel
private theorem rec_1_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 896 128 = 7152097627322541975434829942144 := by decide +kernel
private theorem rec_1_15_2369_0_part8 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1024 128 = 6804108404436557503872046304640 := by decide +kernel
private theorem rec_1_15_2369_0_part9 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1152 128 = 6461617450163162502595808087424 := by decide +kernel
private theorem rec_1_15_2369_0_part10 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1280 128 = 6124579859941319925498363448704 := by decide +kernel
private theorem rec_1_15_2369_0_part11 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1408 128 = 5792950787381942330868014632320 := by decide +kernel
private theorem rec_1_15_2369_0_part12 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1536 128 = 5466685444242750184625601285504 := by decide +kernel
private theorem rec_1_15_2369_0_part13 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1664 128 = 5145739100403130163560983776640 := by decide +kernel
private theorem rec_1_15_2369_0_part14 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1792 128 = 4830067083838993458569526513024 := by decide +kernel
private theorem rec_1_15_2369_0_part15 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1920 128 = 4519624780597634077888581258624 := by decide +kernel
private theorem rec_1_15_2369_0_part16 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2048 128 = 4214367659776855228107830525415 := by decide +kernel
private theorem rec_1_15_2369_0_part17 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2176 128 = 3914251599678647773824890505408 := by decide +kernel
private theorem rec_1_15_2369_0_part18 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2304 128 = 3619232361597323797352406437130 := by decide +kernel
private theorem rec_1_15_2369_0_part19 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2432 128 = 3329265428145556272177063279759 := by decide +kernel
private theorem rec_1_15_2369_0_part20 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2560 128 = 3044306332126740203439864900817 := by decide +kernel
private theorem rec_1_15_2369_0_part21 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2688 128 = 2764310664115371353315372584335 := by decide +kernel
private theorem rec_1_15_2369_0_part22 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2816 128 = 2489234072641018347789907124289 := by decide +kernel
private theorem rec_1_15_2369_0_part23 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2944 128 = 2219032264826520676455524733967 := by decide +kernel
private theorem rec_1_15_2369_0_part24 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3072 128 = 1953661005576221870895040433292 := by decide +kernel
private theorem rec_1_15_2369_0_part25 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3200 128 = 1693076117633902614882487783008 := by decide +kernel
private theorem rec_1_15_2369_0_part26 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3328 128 = 1437233481985478503515812195343 := by decide +kernel
private theorem rec_1_15_2369_0_part27 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3456 128 = 1186089037629009398634932501458 := by decide +kernel
private theorem rec_1_15_2369_0_part28 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3584 128 = 939598781345069489604451104912 := by decide +kernel
private theorem rec_1_15_2369_0_part29 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3712 128 = 697718767832610883510980106794 := by decide +kernel
private theorem rec_1_15_2369_0_part30 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3840 128 = 460405109868311273110955556969 := by decide +kernel
private theorem rec_1_15_2369_0_part31 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3968 128 = 227613977966123949556003608450 := by decide +kernel
private theorem rec_1_15_2369_0_part32 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 4096 63 = 27911633521968019065851097300 := by decide +kernel
private theorem rec_1_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 0 256 = 19103776516451191146536914508544 :=
  phaseBlock_append rec_1_15_2369_0_part0 rec_1_15_2369_0_part1 rfl rfl rfl
private theorem rec_1_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 256 256 = 17576030839421215760570414586624 :=
  phaseBlock_append rec_1_15_2369_0_part2 rec_1_15_2369_0_part3 rfl rfl rfl
private theorem rec_1_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 0 512 = 36679807355872406907107329095168 :=
  phaseBlock_append rec_1_15_2369_0_join0 rec_1_15_2369_0_join1 rfl rfl rfl
private theorem rec_1_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 512 256 = 16094255614560648087307044772608 :=
  phaseBlock_append rec_1_15_2369_0_part4 rec_1_15_2369_0_part5 rfl rfl rfl
private theorem rec_1_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 768 256 = 14657727708901786239986311551744 :=
  phaseBlock_append rec_1_15_2369_0_part6 rec_1_15_2369_0_part7 rfl rfl rfl
private theorem rec_1_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 512 512 = 30751983323462434327293356324352 :=
  phaseBlock_append rec_1_15_2369_0_join3 rec_1_15_2369_0_join4 rfl rfl rfl
private theorem rec_1_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 0 1024 = 67431790679334841234400685419520 :=
  phaseBlock_append rec_1_15_2369_0_join2 rec_1_15_2369_0_join5 rfl rfl rfl
private theorem rec_1_15_2369_0_join7 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1024 256 = 13265725854599720006467854392064 :=
  phaseBlock_append rec_1_15_2369_0_part8 rec_1_15_2369_0_part9 rfl rfl rfl
private theorem rec_1_15_2369_0_join8 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1280 256 = 11917530647323262256366378081024 :=
  phaseBlock_append rec_1_15_2369_0_part10 rec_1_15_2369_0_part11 rfl rfl rfl
private theorem rec_1_15_2369_0_join9 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1024 512 = 25183256501922982262834232473088 :=
  phaseBlock_append rec_1_15_2369_0_join7 rec_1_15_2369_0_join8 rfl rfl rfl
private theorem rec_1_15_2369_0_join10 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1536 256 = 10612424544645880348186585062144 :=
  phaseBlock_append rec_1_15_2369_0_part12 rec_1_15_2369_0_part13 rfl rfl rfl
private theorem rec_1_15_2369_0_join11 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1792 256 = 9349691864436627536458107771648 :=
  phaseBlock_append rec_1_15_2369_0_part14 rec_1_15_2369_0_part15 rfl rfl rfl
private theorem rec_1_15_2369_0_join12 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1536 512 = 19962116409082507884644692833792 :=
  phaseBlock_append rec_1_15_2369_0_join10 rec_1_15_2369_0_join11 rfl rfl rfl
private theorem rec_1_15_2369_0_join13 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 1024 1024 = 45145372911005490147478925306880 :=
  phaseBlock_append rec_1_15_2369_0_join9 rec_1_15_2369_0_join12 rfl rfl rfl
private theorem rec_1_15_2369_0_join14 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 0 2048 = 112577163590340331381879610726400 :=
  phaseBlock_append rec_1_15_2369_0_join6 rec_1_15_2369_0_join13 rfl rfl rfl
private theorem rec_1_15_2369_0_join15 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2048 256 = 8128619259455503001932721030823 :=
  phaseBlock_append rec_1_15_2369_0_part16 rec_1_15_2369_0_part17 rfl rfl rfl
private theorem rec_1_15_2369_0_join16 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2304 256 = 6948497789742880069529469716889 :=
  phaseBlock_append rec_1_15_2369_0_part18 rec_1_15_2369_0_part19 rfl rfl rfl
private theorem rec_1_15_2369_0_join17 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2048 512 = 15077117049198383071462190747712 :=
  phaseBlock_append rec_1_15_2369_0_join15 rec_1_15_2369_0_join16 rfl rfl rfl
private theorem rec_1_15_2369_0_join18 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2560 256 = 5808616996242111556755237485152 :=
  phaseBlock_append rec_1_15_2369_0_part20 rec_1_15_2369_0_part21 rfl rfl rfl
private theorem rec_1_15_2369_0_join19 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2816 256 = 4708266337467539024245431858256 :=
  phaseBlock_append rec_1_15_2369_0_part22 rec_1_15_2369_0_part23 rfl rfl rfl
private theorem rec_1_15_2369_0_join20 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2560 512 = 10516883333709650581000669343408 :=
  phaseBlock_append rec_1_15_2369_0_join18 rec_1_15_2369_0_join19 rfl rfl rfl
private theorem rec_1_15_2369_0_join21 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2048 1024 = 25594000382908033652462860091120 :=
  phaseBlock_append rec_1_15_2369_0_join17 rec_1_15_2369_0_join20 rfl rfl rfl
private theorem rec_1_15_2369_0_join22 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3072 256 = 3646737123210124485777528216300 :=
  phaseBlock_append rec_1_15_2369_0_part24 rec_1_15_2369_0_part25 rfl rfl rfl
private theorem rec_1_15_2369_0_join23 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3328 256 = 2623322519614487902150744696801 :=
  phaseBlock_append rec_1_15_2369_0_part26 rec_1_15_2369_0_part27 rfl rfl rfl
private theorem rec_1_15_2369_0_join24 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3072 512 = 6270059642824612387928272913101 :=
  phaseBlock_append rec_1_15_2369_0_join22 rec_1_15_2369_0_join23 rfl rfl rfl
private theorem rec_1_15_2369_0_join25 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3584 256 = 1637317549177680373115431211706 :=
  phaseBlock_append rec_1_15_2369_0_part28 rec_1_15_2369_0_part29 rfl rfl rfl
private theorem rec_1_15_2369_0_join26 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3968 191 = 255525611488091968621854705750 :=
  phaseBlock_append rec_1_15_2369_0_part31 rec_1_15_2369_0_part32 rfl rfl rfl
private theorem rec_1_15_2369_0_join27 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3840 319 = 715930721356403241732810262719 :=
  phaseBlock_append rec_1_15_2369_0_part30 rec_1_15_2369_0_join26 rfl rfl rfl
private theorem rec_1_15_2369_0_join28 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3584 575 = 2353248270534083614848241474425 :=
  phaseBlock_append rec_1_15_2369_0_join25 rec_1_15_2369_0_join27 rfl rfl rfl
private theorem rec_1_15_2369_0_join29 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 3072 1087 = 8623307913358696002776514387526 :=
  phaseBlock_append rec_1_15_2369_0_join24 rec_1_15_2369_0_join28 rfl rfl rfl
private theorem rec_1_15_2369_0_join30 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 2048 2111 = 34217308296266729655239374478646 :=
  phaseBlock_append rec_1_15_2369_0_join21 rec_1_15_2369_0_join29 rfl rfl rfl
private theorem rec_1_15_2369_0_join31 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 0) 0 4159 = 146794471886607061037118985205046 :=
  phaseBlock_append rec_1_15_2369_0_join14 rec_1_15_2369_0_join30 rfl rfl rfl

private theorem rec_1_15_2369_0 : fastPhase (bank 1 15).shape 179798 2369 105 1 0 2 0 = 146794471886607061037118985205046 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_1_15_2369_0_join31

private theorem rec_1_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 0 128 = 9742748496431399408989071852096 := by decide +kernel
private theorem rec_1_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 128 128 = 9355053273998682886531329614400 := by decide +kernel
private theorem rec_1_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 256 128 = 8973171940048082133140416758336 := by decide +kernel
private theorem rec_1_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 384 128 = 8597059182555678024632967045696 := by decide +kernel
private theorem rec_1_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 512 128 = 8226669747845300406174889427520 := by decide +kernel
private theorem rec_1_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 640 128 = 7861958440563386395517851361856 := by decide +kernel
private theorem rec_1_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 768 128 = 7502880123653838686235762131520 := by decide +kernel
private theorem rec_1_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 896 128 = 7149389718332883850961256161856 := by decide +kernel
private theorem rec_1_15_2369_1_part8 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1024 128 = 6801442204063930644622176338496 := by decide +kernel
private theorem rec_1_15_2369_1_part9 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1152 128 = 6458992618532428307678057325120 := by decide +kernel
private theorem rec_1_15_2369_1_part10 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1280 128 = 6121996057620724869356608881216 := by decide +kernel
private theorem rec_1_15_2369_1_part11 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1408 128 = 5790407675382925450890199179840 := by decide +kernel
private theorem rec_1_15_2369_1_part12 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1536 128 = 5464182684019750568752338125376 := by decide +kernel
private theorem rec_1_15_2369_1_part13 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1664 128 = 5143276353853394437894160671296 := by decide +kernel
private theorem rec_1_15_2369_1_part14 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1792 128 = 4827644013302383274980910137920 := by decide +kernel
private theorem rec_1_15_2369_1_part15 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1920 128 = 4517241048856433601628421530176 := by decide +kernel
private theorem rec_1_15_2369_1_part16 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2048 128 = 4212022930042910819960811718701 := by decide +kernel
private theorem rec_1_15_2369_1_part17 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2176 128 = 3911945535404621825426005287660 := by decide +kernel
private theorem rec_1_15_2369_1_part18 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2304 128 = 3616964626521462500829022562283 := by decide +kernel
private theorem rec_1_15_2369_1_part19 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2432 128 = 3327035686444708597287898987818 := by decide +kernel
private theorem rec_1_15_2369_1_part20 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2560 128 = 3042114248419856110082590506993 := by decide +kernel
private theorem rec_1_15_2369_1_part21 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2688 128 = 2762155903463507244422047411365 := by decide +kernel
private theorem rec_1_15_2369_1_part22 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2816 128 = 2487116300547292972661257278873 := by decide +kernel
private theorem rec_1_15_2369_1_part23 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2944 128 = 2216951147235549749008021464426 := by decide +kernel
private theorem rec_1_15_2369_1_part24 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3072 128 = 1951616208874074551859480821433 := by decide +kernel
private theorem rec_1_15_2369_1_part25 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3200 128 = 1691067308648105920620418995600 := by decide +kernel
private theorem rec_1_15_2369_1_part26 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3328 128 = 1435260327984640295554160430480 := by decide +kernel
private theorem rec_1_15_2369_1_part27 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3456 128 = 1184151206322511993375887789792 := by decide +kernel
private theorem rec_1_15_2369_1_part28 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3584 128 = 937695940883062441082968646373 := by decide +kernel
private theorem rec_1_15_2369_1_part29 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3712 128 = 695850586805942858006929358256 := by decide +kernel
private theorem rec_1_15_2369_1_part30 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3840 128 = 458571257307967871161375337772 := by decide +kernel
private theorem rec_1_15_2369_1_part31 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3968 128 = 225814123343206127871156921183 := by decide +kernel
private theorem rec_1_15_2369_1_part32 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 4096 63 = 27038151516491535522211280388 := by decide +kernel
private theorem rec_1_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 0 256 = 19097801770430082295520401466496 :=
  phaseBlock_append rec_1_15_2369_1_part0 rec_1_15_2369_1_part1 rfl rfl rfl
private theorem rec_1_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 256 256 = 17570231122603760157773383804032 :=
  phaseBlock_append rec_1_15_2369_1_part2 rec_1_15_2369_1_part3 rfl rfl rfl
private theorem rec_1_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 0 512 = 36668032893033842453293785270528 :=
  phaseBlock_append rec_1_15_2369_1_join0 rec_1_15_2369_1_join1 rfl rfl rfl
private theorem rec_1_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 512 256 = 16088628188408686801692740789376 :=
  phaseBlock_append rec_1_15_2369_1_part4 rec_1_15_2369_1_part5 rfl rfl rfl
private theorem rec_1_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 768 256 = 14652269841986722537197018293376 :=
  phaseBlock_append rec_1_15_2369_1_part6 rec_1_15_2369_1_part7 rfl rfl rfl
private theorem rec_1_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 512 512 = 30740898030395409338889759082752 :=
  phaseBlock_append rec_1_15_2369_1_join3 rec_1_15_2369_1_join4 rfl rfl rfl
private theorem rec_1_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 0 1024 = 67408930923429251792183544353280 :=
  phaseBlock_append rec_1_15_2369_1_join2 rec_1_15_2369_1_join5 rfl rfl rfl
private theorem rec_1_15_2369_1_join7 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1024 256 = 13260434822596358952300233663616 :=
  phaseBlock_append rec_1_15_2369_1_part8 rec_1_15_2369_1_part9 rfl rfl rfl
private theorem rec_1_15_2369_1_join8 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1280 256 = 11912403733003650320246808061056 :=
  phaseBlock_append rec_1_15_2369_1_part10 rec_1_15_2369_1_part11 rfl rfl rfl
private theorem rec_1_15_2369_1_join9 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1024 512 = 25172838555600009272547041724672 :=
  phaseBlock_append rec_1_15_2369_1_join7 rec_1_15_2369_1_join8 rfl rfl rfl
private theorem rec_1_15_2369_1_join10 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1536 256 = 10607459037873145006646498796672 :=
  phaseBlock_append rec_1_15_2369_1_part12 rec_1_15_2369_1_part13 rfl rfl rfl
private theorem rec_1_15_2369_1_join11 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1792 256 = 9344885062158816876609331668096 :=
  phaseBlock_append rec_1_15_2369_1_part14 rec_1_15_2369_1_part15 rfl rfl rfl
private theorem rec_1_15_2369_1_join12 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1536 512 = 19952344100031961883255830464768 :=
  phaseBlock_append rec_1_15_2369_1_join10 rec_1_15_2369_1_join11 rfl rfl rfl
private theorem rec_1_15_2369_1_join13 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 1024 1024 = 45125182655631971155802872189440 :=
  phaseBlock_append rec_1_15_2369_1_join9 rec_1_15_2369_1_join12 rfl rfl rfl
private theorem rec_1_15_2369_1_join14 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 0 2048 = 112534113579061222947986416542720 :=
  phaseBlock_append rec_1_15_2369_1_join6 rec_1_15_2369_1_join13 rfl rfl rfl
private theorem rec_1_15_2369_1_join15 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2048 256 = 8123968465447532645386817006361 :=
  phaseBlock_append rec_1_15_2369_1_part16 rec_1_15_2369_1_part17 rfl rfl rfl
private theorem rec_1_15_2369_1_join16 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2304 256 = 6944000312966171098116921550101 :=
  phaseBlock_append rec_1_15_2369_1_part18 rec_1_15_2369_1_part19 rfl rfl rfl
private theorem rec_1_15_2369_1_join17 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2048 512 = 15067968778413703743503738556462 :=
  phaseBlock_append rec_1_15_2369_1_join15 rec_1_15_2369_1_join16 rfl rfl rfl
private theorem rec_1_15_2369_1_join18 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2560 256 = 5804270151883363354504637918358 :=
  phaseBlock_append rec_1_15_2369_1_part20 rec_1_15_2369_1_part21 rfl rfl rfl
private theorem rec_1_15_2369_1_join19 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2816 256 = 4704067447782842721669278743299 :=
  phaseBlock_append rec_1_15_2369_1_part22 rec_1_15_2369_1_part23 rfl rfl rfl
private theorem rec_1_15_2369_1_join20 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2560 512 = 10508337599666206076173916661657 :=
  phaseBlock_append rec_1_15_2369_1_join18 rec_1_15_2369_1_join19 rfl rfl rfl
private theorem rec_1_15_2369_1_join21 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2048 1024 = 25576306378079909819677655218119 :=
  phaseBlock_append rec_1_15_2369_1_join17 rec_1_15_2369_1_join20 rfl rfl rfl
private theorem rec_1_15_2369_1_join22 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3072 256 = 3642683517522180472479899817033 :=
  phaseBlock_append rec_1_15_2369_1_part24 rec_1_15_2369_1_part25 rfl rfl rfl
private theorem rec_1_15_2369_1_join23 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3328 256 = 2619411534307152288930048220272 :=
  phaseBlock_append rec_1_15_2369_1_part26 rec_1_15_2369_1_part27 rfl rfl rfl
private theorem rec_1_15_2369_1_join24 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3072 512 = 6262095051829332761409948037305 :=
  phaseBlock_append rec_1_15_2369_1_join22 rec_1_15_2369_1_join23 rfl rfl rfl
private theorem rec_1_15_2369_1_join25 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3584 256 = 1633546527689005299089898004629 :=
  phaseBlock_append rec_1_15_2369_1_part28 rec_1_15_2369_1_part29 rfl rfl rfl
private theorem rec_1_15_2369_1_join26 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3968 191 = 252852274859697663393368201571 :=
  phaseBlock_append rec_1_15_2369_1_part31 rec_1_15_2369_1_part32 rfl rfl rfl
private theorem rec_1_15_2369_1_join27 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3840 319 = 711423532167665534554743539343 :=
  phaseBlock_append rec_1_15_2369_1_part30 rec_1_15_2369_1_join26 rfl rfl rfl
private theorem rec_1_15_2369_1_join28 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3584 575 = 2344970059856670833644641543972 :=
  phaseBlock_append rec_1_15_2369_1_join25 rec_1_15_2369_1_join27 rfl rfl rfl
private theorem rec_1_15_2369_1_join29 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 3072 1087 = 8607065111686003595054589581277 :=
  phaseBlock_append rec_1_15_2369_1_join24 rec_1_15_2369_1_join28 rfl rfl rfl
private theorem rec_1_15_2369_1_join30 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 2048 2111 = 34183371489765913414732244799396 :=
  phaseBlock_append rec_1_15_2369_1_join21 rec_1_15_2369_1_join29 rfl rfl rfl
private theorem rec_1_15_2369_1_join31 :
    phaseBlock (fastLayerG (bank 1 15).shape 179798 2369 105 1 0 2 1) 0 4159 = 146717485068827136362718661342116 :=
  phaseBlock_append rec_1_15_2369_1_join14 rec_1_15_2369_1_join30 rfl rfl rfl

private theorem rec_1_15_2369_1 : fastPhase (bank 1 15).shape 179798 2369 105 1 0 2 1 = 146717485068827136362718661342116 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_1_15_2369_1_join31

theorem receipt_1_15 : Checked (bank 1 15) 105 0 2 := by
  refine checked_from_values (bank 1 15) 105 0 2
    (P3_7_1.checked (bank 1 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_18778_4158)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_15_2368_0 rec_1_15_2368_1 rec_1_15_2369_0 rec_1_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_1_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 0 128 = 32667014357150019792920664641184 := by decide +kernel
private theorem rec_1_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 128 128 = 31605437517090554220796752985760 := by decide +kernel
private theorem rec_1_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 256 128 = 30556829263758211537801984372384 := by decide +kernel
private theorem rec_1_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 384 128 = 29521107732551148788253180583584 := by decide +kernel
private theorem rec_1_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 512 128 = 28498191137526177900650490252960 := by decide +kernel
private theorem rec_1_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 640 128 = 27487997771373624870523174403744 := by decide +kernel
private theorem rec_1_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 768 128 = 26490446005392188943275391987360 := by decide +kernel
private theorem rec_1_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 896 128 = 25505454289463801797031985421984 := by decide +kernel
private theorem rec_1_16_2368_0_part8 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1024 128 = 24532941152028486725484266131104 := by decide +kernel
private theorem rec_1_16_2368_0_part9 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1152 128 = 23572825200059217820735800082080 := by decide +kernel
private theorem rec_1_16_2368_0_part10 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1280 128 = 22625025119036779156148193324704 := by decide +kernel
private theorem rec_1_16_2368_0_part11 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1408 128 = 21689459672924623969186877529760 := by decide +kernel
private theorem rec_1_16_2368_0_part12 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1536 128 = 20766047704143733844266895527584 := by decide +kernel
private theorem rec_1_16_2368_0_part13 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1664 128 = 19854708133547477895598686846624 := by decide +kernel
private theorem rec_1_16_2368_0_part14 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1792 128 = 18955359960396471950033873252000 := by decide +kernel
private theorem rec_1_16_2368_0_part15 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1920 128 = 18067922262333437729911044284064 := by decide +kernel
private theorem rec_1_16_2368_0_part16 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2048 128 = 17192314195358062035901542796960 := by decide +kernel
private theorem rec_1_16_2368_0_part17 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2176 128 = 16328454993801855929855250497184 := by decide +kernel
private theorem rec_1_16_2368_0_part18 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2304 128 = 15476263970303013917646373482144 := by decide +kernel
private theorem rec_1_16_2368_0_part19 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2432 128 = 14635660515781273132019227778720 := by decide +kernel
private theorem rec_1_16_2368_0_part20 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2560 128 = 13806564417341698611899834315812 := by decide +kernel
private theorem rec_1_16_2368_0_part21 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2688 128 = 12988896234314709074938741442100 := by decide +kernel
private theorem rec_1_16_2368_0_part22 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2816 128 = 12182575580038929152510913724287 := by decide +kernel
private theorem rec_1_16_2368_0_part23 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2944 128 = 11387521894845216333560606744960 := by decide +kernel
private theorem rec_1_16_2368_0_part24 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3072 128 = 10603654699018247041012837759269 := by decide +kernel
private theorem rec_1_16_2368_0_part25 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3200 128 = 9830893590622776562108163257123 := by decide +kernel
private theorem rec_1_16_2368_0_part26 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3328 128 = 9069158245469849791146574125321 := by decide +kernel
private theorem rec_1_16_2368_0_part27 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3456 128 = 8318368418297980322169471246216 := by decide +kernel
private theorem rec_1_16_2368_0_part28 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3584 128 = 7578443942574424757226404201378 := by decide +kernel
private theorem rec_1_16_2368_0_part29 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3712 128 = 6849304729445719896969107082589 := by decide +kernel
private theorem rec_1_16_2368_0_part30 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3840 128 = 6130870768119963506942581227870 := by decide +kernel
private theorem rec_1_16_2368_0_part31 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3968 128 = 5423062126950541662102768131013 := by decide +kernel
private theorem rec_1_16_2368_0_part32 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4096 128 = 4725798952030546102809510438026 := by decide +kernel
private theorem rec_1_16_2368_0_part33 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4224 128 = 4039001467352514239041467640056 := by decide +kernel
private theorem rec_1_16_2368_0_part34 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4352 128 = 3362589975557942536114694402209 := by decide +kernel
private theorem rec_1_16_2368_0_part35 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4480 128 = 2696484857427862045051375664442 := by decide +kernel
private theorem rec_1_16_2368_0_part36 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4608 128 = 2040606571615402175890521843459 := by decide +kernel
private theorem rec_1_16_2368_0_part37 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4736 128 = 1394875654923772240118408674562 := by decide +kernel
private theorem rec_1_16_2368_0_part38 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4864 128 = 759212722471853190741851482486 := by decide +kernel
private theorem rec_1_16_2368_0_part39 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4992 91 = 158645013616965767374119866370 := by decide +kernel
private theorem rec_1_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 0 256 = 64272451874240574013717417626944 :=
  phaseBlock_append rec_1_16_2368_0_part0 rec_1_16_2368_0_part1 rfl rfl rfl
private theorem rec_1_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 384 256 = 58019298870077326688903670836544 :=
  phaseBlock_append rec_1_16_2368_0_part3 rec_1_16_2368_0_part4 rfl rfl rfl
private theorem rec_1_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 256 384 = 88576128133835538226705655208928 :=
  phaseBlock_append rec_1_16_2368_0_part2 rec_1_16_2368_0_join1 rfl rfl rfl
private theorem rec_1_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 0 640 = 152848580008076112240423072835872 :=
  phaseBlock_append rec_1_16_2368_0_join0 rec_1_16_2368_0_join2 rfl rfl rfl
private theorem rec_1_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 640 256 = 53978443776765813813798566391104 :=
  phaseBlock_append rec_1_16_2368_0_part5 rec_1_16_2368_0_part6 rfl rfl rfl
private theorem rec_1_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1024 256 = 48105766352087704546220066213184 :=
  phaseBlock_append rec_1_16_2368_0_part8 rec_1_16_2368_0_part9 rfl rfl rfl
private theorem rec_1_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 896 384 = 73611220641551506343252051635168 :=
  phaseBlock_append rec_1_16_2368_0_part7 rec_1_16_2368_0_join5 rfl rfl rfl
private theorem rec_1_16_2368_0_join7 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 640 640 = 127589664418317320157050618026272 :=
  phaseBlock_append rec_1_16_2368_0_join4 rec_1_16_2368_0_join6 rfl rfl rfl
private theorem rec_1_16_2368_0_join8 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 0 1280 = 280438244426393432397473690862144 :=
  phaseBlock_append rec_1_16_2368_0_join3 rec_1_16_2368_0_join7 rfl rfl rfl
private theorem rec_1_16_2368_0_join9 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1280 256 = 44314484791961403125335070854464 :=
  phaseBlock_append rec_1_16_2368_0_part10 rec_1_16_2368_0_part11 rfl rfl rfl
private theorem rec_1_16_2368_0_join10 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1664 256 = 38810068093943949845632560098624 :=
  phaseBlock_append rec_1_16_2368_0_part13 rec_1_16_2368_0_part14 rfl rfl rfl
private theorem rec_1_16_2368_0_join11 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1536 384 = 59576115798087683689899455626208 :=
  phaseBlock_append rec_1_16_2368_0_part12 rec_1_16_2368_0_join10 rfl rfl rfl
private theorem rec_1_16_2368_0_join12 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1280 640 = 103890600590049086815234526480672 :=
  phaseBlock_append rec_1_16_2368_0_join9 rec_1_16_2368_0_join11 rfl rfl rfl
private theorem rec_1_16_2368_0_join13 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1920 256 = 35260236457691499765812587081024 :=
  phaseBlock_append rec_1_16_2368_0_part15 rec_1_16_2368_0_part16 rfl rfl rfl
private theorem rec_1_16_2368_0_join14 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2304 256 = 30111924486084287049665601260864 :=
  phaseBlock_append rec_1_16_2368_0_part18 rec_1_16_2368_0_part19 rfl rfl rfl
private theorem rec_1_16_2368_0_join15 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2176 384 = 46440379479886142979520851758048 :=
  phaseBlock_append rec_1_16_2368_0_part17 rec_1_16_2368_0_join14 rfl rfl rfl
private theorem rec_1_16_2368_0_join16 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1920 640 = 81700615937577642745333438839072 :=
  phaseBlock_append rec_1_16_2368_0_join13 rec_1_16_2368_0_join15 rfl rfl rfl
private theorem rec_1_16_2368_0_join17 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 1280 1280 = 185591216527626729560567965319744 :=
  phaseBlock_append rec_1_16_2368_0_join12 rec_1_16_2368_0_join16 rfl rfl rfl
private theorem rec_1_16_2368_0_join18 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 0 2560 = 466029460954020161958041656181888 :=
  phaseBlock_append rec_1_16_2368_0_join8 rec_1_16_2368_0_join17 rfl rfl rfl
private theorem rec_1_16_2368_0_join19 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2560 256 = 26795460651656407686838575757912 :=
  phaseBlock_append rec_1_16_2368_0_part20 rec_1_16_2368_0_part21 rfl rfl rfl
private theorem rec_1_16_2368_0_join20 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2944 256 = 21991176593863463374573444504229 :=
  phaseBlock_append rec_1_16_2368_0_part23 rec_1_16_2368_0_part24 rfl rfl rfl
private theorem rec_1_16_2368_0_join21 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2816 384 = 34173752173902392527084358228516 :=
  phaseBlock_append rec_1_16_2368_0_part22 rec_1_16_2368_0_join20 rfl rfl rfl
private theorem rec_1_16_2368_0_join22 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2560 640 = 60969212825558800213922933986428 :=
  phaseBlock_append rec_1_16_2368_0_join19 rec_1_16_2368_0_join21 rfl rfl rfl
private theorem rec_1_16_2368_0_join23 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3200 256 = 18900051836092626353254737382444 :=
  phaseBlock_append rec_1_16_2368_0_part25 rec_1_16_2368_0_part26 rfl rfl rfl
private theorem rec_1_16_2368_0_join24 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3584 256 = 14427748672020144654195511283967 :=
  phaseBlock_append rec_1_16_2368_0_part28 rec_1_16_2368_0_part29 rfl rfl rfl
private theorem rec_1_16_2368_0_join25 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3456 384 = 22746117090318124976364982530183 :=
  phaseBlock_append rec_1_16_2368_0_part27 rec_1_16_2368_0_join24 rfl rfl rfl
private theorem rec_1_16_2368_0_join26 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3200 640 = 41646168926410751329619719912627 :=
  phaseBlock_append rec_1_16_2368_0_join23 rec_1_16_2368_0_join25 rfl rfl rfl
private theorem rec_1_16_2368_0_join27 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2560 1280 = 102615381751969551543542653899055 :=
  phaseBlock_append rec_1_16_2368_0_join22 rec_1_16_2368_0_join26 rfl rfl rfl
private theorem rec_1_16_2368_0_join28 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3840 256 = 11553932895070505169045349358883 :=
  phaseBlock_append rec_1_16_2368_0_part30 rec_1_16_2368_0_part31 rfl rfl rfl
private theorem rec_1_16_2368_0_join29 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4224 256 = 7401591442910456775156162042265 :=
  phaseBlock_append rec_1_16_2368_0_part33 rec_1_16_2368_0_part34 rfl rfl rfl
private theorem rec_1_16_2368_0_join30 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4096 384 = 12127390394941002877965672480291 :=
  phaseBlock_append rec_1_16_2368_0_part32 rec_1_16_2368_0_join29 rfl rfl rfl
private theorem rec_1_16_2368_0_join31 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3840 640 = 23681323290011508047011021839174 :=
  phaseBlock_append rec_1_16_2368_0_join28 rec_1_16_2368_0_join30 rfl rfl rfl
private theorem rec_1_16_2368_0_join32 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4480 256 = 4737091429043264220941897507901 :=
  phaseBlock_append rec_1_16_2368_0_part35 rec_1_16_2368_0_part36 rfl rfl rfl
private theorem rec_1_16_2368_0_join33 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4864 219 = 917857736088818958115971348856 :=
  phaseBlock_append rec_1_16_2368_0_part38 rec_1_16_2368_0_part39 rfl rfl rfl
private theorem rec_1_16_2368_0_join34 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4736 347 = 2312733391012591198234380023418 :=
  phaseBlock_append rec_1_16_2368_0_part37 rec_1_16_2368_0_join33 rfl rfl rfl
private theorem rec_1_16_2368_0_join35 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 4480 603 = 7049824820055855419176277531319 :=
  phaseBlock_append rec_1_16_2368_0_join32 rec_1_16_2368_0_join34 rfl rfl rfl
private theorem rec_1_16_2368_0_join36 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 3840 1243 = 30731148110067363466187299370493 :=
  phaseBlock_append rec_1_16_2368_0_join31 rec_1_16_2368_0_join35 rfl rfl rfl
private theorem rec_1_16_2368_0_join37 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 2560 2523 = 133346529862036915009729953269548 :=
  phaseBlock_append rec_1_16_2368_0_join27 rec_1_16_2368_0_join36 rfl rfl rfl
private theorem rec_1_16_2368_0_join38 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 0) 0 5083 = 599375990816057076967771609451436 :=
  phaseBlock_append rec_1_16_2368_0_join18 rec_1_16_2368_0_join37 rfl rfl rfl

private theorem rec_1_16_2368_0 : fastPhase (bank 1 16).shape 179798 2368 138 1 0 2 0 = 599375990816057076967771609451436 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_1_16_2368_0_join38

private theorem rec_1_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 0 128 = 32658786623967558360700312873440 := by decide +kernel
private theorem rec_1_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 128 128 = 31597308066136886645089104304608 := by decide +kernel
private theorem rec_1_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 256 128 = 30548797475544396629614586513888 := by decide +kernel
private theorem rec_1_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 384 128 = 29513172988187744891613620500960 := by decide +kernel
private theorem rec_1_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 512 128 = 28490352818723050385437678676448 := by decide +kernel
private theorem rec_1_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 640 128 = 27480255260439753625298630400480 := by decide +kernel
private theorem rec_1_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 768 128 = 26482798685235475868114527521248 := by decide +kernel
private theorem rec_1_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 896 128 = 25497901543590878296355389913568 := by decide +kernel
private theorem rec_1_16_2368_1_part8 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1024 128 = 24525482364544521200888991017440 := by decide +kernel
private theorem rec_1_16_2368_1_part9 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1152 128 = 23565459755667723163826643376608 := by decide +kernel
private theorem rec_1_16_2368_1_part10 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1280 128 = 22617752403039420241368984177120 := by decide +kernel
private theorem rec_1_16_2368_1_part11 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1408 128 = 21682279071221025146651760785888 := by decide +kernel
private theorem rec_1_16_2368_1_part12 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1536 128 = 20758958603231286432591616289248 := by decide +kernel
private theorem rec_1_16_2368_1_part13 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1664 128 = 19847709920521147674731875031520 := by decide +kernel
private theorem rec_1_16_2368_1_part14 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1792 128 = 18948452022948606654088328153568 := by decide +kernel
private theorem rec_1_16_2368_1_part15 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1920 128 = 18061103988753574539995019131360 := by decide +kernel
private theorem rec_1_16_2368_1_part16 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2048 128 = 17185584974532735072950029314528 := by decide +kernel
private theorem rec_1_16_2368_1_part17 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2176 128 = 16321814215214403747461263464928 := by decide +kernel
private theorem rec_1_16_2368_1_part18 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2304 128 = 15469711024033386994892235295200 := by decide +kernel
private theorem rec_1_16_2368_1_part19 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2432 128 = 14629194792505841366307853007328 := by decide +kernel
private theorem rec_1_16_2368_1_part20 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2560 128 = 13800185308200742018471422758523 := by decide +kernel
private theorem rec_1_16_2368_1_part21 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2688 128 = 12982603130587451733039748182025 := by decide +kernel
private theorem rec_1_16_2368_1_part22 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2816 128 = 12176367873505998240300235576177 := by decide +kernel
private theorem rec_1_16_2368_1_part23 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2944 128 = 11381398977884338313092127073012 := by decide +kernel
private theorem rec_1_16_2368_1_part24 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3072 128 = 10597615964603375394656115277510 := by decide +kernel
private theorem rec_1_16_2368_1_part25 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3200 128 = 9824938432324115865786676160475 := by decide +kernel
private theorem rec_1_16_2368_1_part26 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3328 128 = 9063286057454020327520203155222 := by decide +kernel
private theorem rec_1_16_2368_1_part27 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3456 128 = 8312578595327598347981523760360 := by decide +kernel
private theorem rec_1_16_2368_1_part28 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3584 128 = 7572735880007583029453992819195 := by decide +kernel
private theorem rec_1_16_2368_1_part29 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3712 128 = 6843677823236165637070800875660 := by decide +kernel
private theorem rec_1_16_2368_1_part30 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3840 128 = 6125324414817163563620179986336 := by decide +kernel
private theorem rec_1_16_2368_1_part31 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3968 128 = 5417595723698799836701541602808 := by decide +kernel
private theorem rec_1_16_2368_1_part32 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4096 128 = 4720411896569105789629035073107 := by decide +kernel
private theorem rec_1_16_2368_1_part33 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4224 128 = 4033693158015744625706743499604 := by decide +kernel
private theorem rec_1_16_2368_1_part34 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4352 128 = 3357359811274728159393187663434 := by decide +kernel
private theorem rec_1_16_2368_1_part35 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4480 128 = 2691332237721280506327530958540 := by decide +kernel
private theorem rec_1_16_2368_1_part36 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4608 128 = 2035530896602874982029359493073 := by decide +kernel
private theorem rec_1_16_2368_1_part37 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4736 128 = 1389876325317035740767091798706 := by decide +kernel
private theorem rec_1_16_2368_1_part38 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4864 128 = 754289139576116237313583743363 := by decide +kernel
private theorem rec_1_16_2368_1_part39 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4992 91 = 155190393171158119956784358094 := by decide +kernel
private theorem rec_1_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 0 256 = 64256094690104445005789417178048 :=
  phaseBlock_append rec_1_16_2368_1_part0 rec_1_16_2368_1_part1 rfl rfl rfl
private theorem rec_1_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 384 256 = 58003525806910795277051299177408 :=
  phaseBlock_append rec_1_16_2368_1_part3 rec_1_16_2368_1_part4 rfl rfl rfl
private theorem rec_1_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 256 384 = 88552323282455191906665885691296 :=
  phaseBlock_append rec_1_16_2368_1_part2 rec_1_16_2368_1_join1 rfl rfl rfl
private theorem rec_1_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 0 640 = 152808417972559636912455302869344 :=
  phaseBlock_append rec_1_16_2368_1_join0 rec_1_16_2368_1_join2 rfl rfl rfl
private theorem rec_1_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 640 256 = 53963053945675229493413157921728 :=
  phaseBlock_append rec_1_16_2368_1_part5 rec_1_16_2368_1_part6 rfl rfl rfl
private theorem rec_1_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1024 256 = 48090942120212244364715634394048 :=
  phaseBlock_append rec_1_16_2368_1_part8 rec_1_16_2368_1_part9 rfl rfl rfl
private theorem rec_1_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 896 384 = 73588843663803122661071024307616 :=
  phaseBlock_append rec_1_16_2368_1_part7 rec_1_16_2368_1_join5 rfl rfl rfl
private theorem rec_1_16_2368_1_join7 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 640 640 = 127551897609478352154484182229344 :=
  phaseBlock_append rec_1_16_2368_1_join4 rec_1_16_2368_1_join6 rfl rfl rfl
private theorem rec_1_16_2368_1_join8 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 0 1280 = 280360315582037989066939485098688 :=
  phaseBlock_append rec_1_16_2368_1_join3 rec_1_16_2368_1_join7 rfl rfl rfl
private theorem rec_1_16_2368_1_join9 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1280 256 = 44300031474260445388020744963008 :=
  phaseBlock_append rec_1_16_2368_1_part10 rec_1_16_2368_1_part11 rfl rfl rfl
private theorem rec_1_16_2368_1_join10 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1664 256 = 38796161943469754328820203185088 :=
  phaseBlock_append rec_1_16_2368_1_part13 rec_1_16_2368_1_part14 rfl rfl rfl
private theorem rec_1_16_2368_1_join11 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1536 384 = 59555120546701040761411819474336 :=
  phaseBlock_append rec_1_16_2368_1_part12 rec_1_16_2368_1_join10 rfl rfl rfl
private theorem rec_1_16_2368_1_join12 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1280 640 = 103855152020961486149432564437344 :=
  phaseBlock_append rec_1_16_2368_1_join9 rec_1_16_2368_1_join11 rfl rfl rfl
private theorem rec_1_16_2368_1_join13 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1920 256 = 35246688963286309612945048445888 :=
  phaseBlock_append rec_1_16_2368_1_part15 rec_1_16_2368_1_part16 rfl rfl rfl
private theorem rec_1_16_2368_1_join14 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2304 256 = 30098905816539228361200088302528 :=
  phaseBlock_append rec_1_16_2368_1_part18 rec_1_16_2368_1_part19 rfl rfl rfl
private theorem rec_1_16_2368_1_join15 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2176 384 = 46420720031753632108661351767456 :=
  phaseBlock_append rec_1_16_2368_1_part17 rec_1_16_2368_1_join14 rfl rfl rfl
private theorem rec_1_16_2368_1_join16 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1920 640 = 81667408995039941721606400213344 :=
  phaseBlock_append rec_1_16_2368_1_join13 rec_1_16_2368_1_join15 rfl rfl rfl
private theorem rec_1_16_2368_1_join17 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 1280 1280 = 185522561016001427871038964650688 :=
  phaseBlock_append rec_1_16_2368_1_join12 rec_1_16_2368_1_join16 rfl rfl rfl
private theorem rec_1_16_2368_1_join18 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 0 2560 = 465882876598039416937978449749376 :=
  phaseBlock_append rec_1_16_2368_1_join8 rec_1_16_2368_1_join17 rfl rfl rfl
private theorem rec_1_16_2368_1_join19 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2560 256 = 26782788438788193751511170940548 :=
  phaseBlock_append rec_1_16_2368_1_part20 rec_1_16_2368_1_part21 rfl rfl rfl
private theorem rec_1_16_2368_1_join20 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2944 256 = 21979014942487713707748242350522 :=
  phaseBlock_append rec_1_16_2368_1_part23 rec_1_16_2368_1_part24 rfl rfl rfl
private theorem rec_1_16_2368_1_join21 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2816 384 = 34155382815993711948048477926699 :=
  phaseBlock_append rec_1_16_2368_1_part22 rec_1_16_2368_1_join20 rfl rfl rfl
private theorem rec_1_16_2368_1_join22 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2560 640 = 60938171254781905699559648867247 :=
  phaseBlock_append rec_1_16_2368_1_join19 rec_1_16_2368_1_join21 rfl rfl rfl
private theorem rec_1_16_2368_1_join23 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3200 256 = 18888224489778136193306879315697 :=
  phaseBlock_append rec_1_16_2368_1_part25 rec_1_16_2368_1_part26 rfl rfl rfl
private theorem rec_1_16_2368_1_join24 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3584 256 = 14416413703243748666524793694855 :=
  phaseBlock_append rec_1_16_2368_1_part28 rec_1_16_2368_1_part29 rfl rfl rfl
private theorem rec_1_16_2368_1_join25 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3456 384 = 22728992298571347014506317455215 :=
  phaseBlock_append rec_1_16_2368_1_part27 rec_1_16_2368_1_join24 rfl rfl rfl
private theorem rec_1_16_2368_1_join26 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3200 640 = 41617216788349483207813196770912 :=
  phaseBlock_append rec_1_16_2368_1_join23 rec_1_16_2368_1_join25 rfl rfl rfl
private theorem rec_1_16_2368_1_join27 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2560 1280 = 102555388043131388907372845638159 :=
  phaseBlock_append rec_1_16_2368_1_join22 rec_1_16_2368_1_join26 rfl rfl rfl
private theorem rec_1_16_2368_1_join28 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3840 256 = 11542920138515963400321721589144 :=
  phaseBlock_append rec_1_16_2368_1_part30 rec_1_16_2368_1_part31 rfl rfl rfl
private theorem rec_1_16_2368_1_join29 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4224 256 = 7391052969290472785099931163038 :=
  phaseBlock_append rec_1_16_2368_1_part33 rec_1_16_2368_1_part34 rfl rfl rfl
private theorem rec_1_16_2368_1_join30 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4096 384 = 12111464865859578574728966236145 :=
  phaseBlock_append rec_1_16_2368_1_part32 rec_1_16_2368_1_join29 rfl rfl rfl
private theorem rec_1_16_2368_1_join31 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3840 640 = 23654385004375541975050687825289 :=
  phaseBlock_append rec_1_16_2368_1_join28 rec_1_16_2368_1_join30 rfl rfl rfl
private theorem rec_1_16_2368_1_join32 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4480 256 = 4726863134324155488356890451613 :=
  phaseBlock_append rec_1_16_2368_1_part35 rec_1_16_2368_1_part36 rfl rfl rfl
private theorem rec_1_16_2368_1_join33 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4864 219 = 909479532747274357270368101457 :=
  phaseBlock_append rec_1_16_2368_1_part38 rec_1_16_2368_1_part39 rfl rfl rfl
private theorem rec_1_16_2368_1_join34 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4736 347 = 2299355858064310098037459900163 :=
  phaseBlock_append rec_1_16_2368_1_part37 rec_1_16_2368_1_join33 rfl rfl rfl
private theorem rec_1_16_2368_1_join35 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 4480 603 = 7026218992388465586394350351776 :=
  phaseBlock_append rec_1_16_2368_1_join32 rec_1_16_2368_1_join34 rfl rfl rfl
private theorem rec_1_16_2368_1_join36 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 3840 1243 = 30680603996764007561445038177065 :=
  phaseBlock_append rec_1_16_2368_1_join31 rec_1_16_2368_1_join35 rfl rfl rfl
private theorem rec_1_16_2368_1_join37 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 2560 2523 = 133235992039895396468817883815224 :=
  phaseBlock_append rec_1_16_2368_1_join27 rec_1_16_2368_1_join36 rfl rfl rfl
private theorem rec_1_16_2368_1_join38 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2368 138 1 0 2 1) 0 5083 = 599118868637934813406796333564600 :=
  phaseBlock_append rec_1_16_2368_1_join18 rec_1_16_2368_1_join37 rfl rfl rfl

private theorem rec_1_16_2368_1 : fastPhase (bank 1 16).shape 179798 2368 138 1 0 2 1 = 599118868637934813406796333564600 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_1_16_2368_1_join38

private theorem rec_1_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 0 128 = 32667316689966486015367460528352 := by decide +kernel
private theorem rec_1_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 128 128 = 31605725852139564970856988774624 := by decide +kernel
private theorem rec_1_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 256 128 = 30557103964573142156941932986592 := by decide +kernel
private theorem rec_1_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 384 128 = 29521369159865463417044380905696 := by decide +kernel
private theorem rec_1_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 512 128 = 28498439649276165163755211940064 := by decide +kernel
private theorem rec_1_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 640 128 = 27488233722701132682070580482272 := by decide +kernel
private theorem rec_1_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 768 128 = 26490669748647358432628399227104 := by decide +kernel
private theorem rec_1_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 896 128 = 25505666174207800354944822489312 := by decide +kernel
private theorem rec_1_16_2369_0_part8 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1024 128 = 24533141525036240170650729521376 := by decide +kernel
private theorem rec_1_16_2369_0_part9 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1152 128 = 23573014405322141686728207831264 := by decide +kernel
private theorem rec_1_16_2369_0_part10 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1280 128 = 22625203497765509098747036500192 := by decide +kernel
private theorem rec_1_16_2369_0_part11 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1408 128 = 21689627563551745294101169500384 := by decide +kernel
private theorem rec_1_16_2369_0_part12 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1536 128 = 20766205442326510155245219012832 := by decide +kernel
private theorem rec_1_16_2369_0_part13 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1664 128 = 19854856052170578862930938745056 := by decide +kernel
private theorem rec_1_16_2369_0_part14 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1792 128 = 18955498389574700199443707248864 := by decide +kernel
private theorem rec_1_16_2369_0_part15 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1920 128 = 18068051529414454851839011238112 := by decide +kernel
private theorem rec_1_16_2369_0_part16 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2048 128 = 17192434624925113715178928906464 := by decide +kernel
private theorem rec_1_16_2369_0_part17 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2176 128 = 16328566907676496195768613245152 := by decide +kernel
private theorem rec_1_16_2369_0_part18 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2304 128 = 15476367687547828514392775360736 := by decide +kernel
private theorem rec_1_16_2369_0_part19 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2432 128 = 14635756352702602009552167792864 := by decide +kernel
private theorem rec_1_16_2369_0_part20 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2560 128 = 13806652661828735483385932884203 := by decide +kernel
private theorem rec_1_16_2369_0_part21 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2688 128 = 12988977179679369238552490995434 := by decide +kernel
private theorem rec_1_16_2369_0_part22 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2816 128 = 12182649540155706827151508897226 := by decide +kernel
private theorem rec_1_16_2369_0_part23 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2944 128 = 11387589181209818816152664371229 := by decide +kernel
private theorem rec_1_16_2369_0_part24 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3072 128 = 10603715620102146585172739631186 := by decide +kernel
private theorem rec_1_16_2369_0_part25 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3200 128 = 9830948451656364681020096873427 := by decide +kernel
private theorem rec_1_16_2369_0_part26 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3328 128 = 9069207348607339009363968491487 := by decide +kernel
private theorem rec_1_16_2369_0_part27 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3456 128 = 8318412063287280583071212220097 := by decide +kernel
private theorem rec_1_16_2369_0_part28 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3584 128 = 7578482425849006493890517971232 := by decide +kernel
private theorem rec_1_16_2369_0_part29 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3712 128 = 6849338344281860979071505520529 := by decide +kernel
private theorem rec_1_16_2369_0_part30 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3840 128 = 6130899805239695198550572200195 := by decide +kernel
private theorem rec_1_16_2369_0_part31 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3968 128 = 5423086874006879832204211356090 := by decide +kernel
private theorem rec_1_16_2369_0_part32 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4096 128 = 4725819693603432805821177889578 := by decide +kernel
private theorem rec_1_16_2369_0_part33 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4224 128 = 4039018485098791140541337185539 := by decide +kernel
private theorem rec_1_16_2369_0_part34 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4352 128 = 3362603548372672235311231256178 := by decide +kernel
private theorem rec_1_16_2369_0_part35 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4480 128 = 2696495261122344961549806254232 := by decide +kernel
private theorem rec_1_16_2369_0_part36 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4608 128 = 2040614079013172575182018974943 := by decide +kernel
private theorem rec_1_16_2369_0_part37 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4736 128 = 1394880536066111545037522878338 := by decide +kernel
private theorem rec_1_16_2369_0_part38 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4864 128 = 759215244391257534331928733741 := by decide +kernel
private theorem rec_1_16_2369_0_part39 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4992 91 = 158645516957765030796707454321 := by decide +kernel
private theorem rec_1_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 0 256 = 64273042542106050986224449302976 :=
  phaseBlock_append rec_1_16_2369_0_part0 rec_1_16_2369_0_part1 rfl rfl rfl
private theorem rec_1_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 384 256 = 58019808809141628580799592845760 :=
  phaseBlock_append rec_1_16_2369_0_part3 rec_1_16_2369_0_part4 rfl rfl rfl
private theorem rec_1_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 256 384 = 88576912773714770737741525832352 :=
  phaseBlock_append rec_1_16_2369_0_part2 rec_1_16_2369_0_join1 rfl rfl rfl
private theorem rec_1_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 0 640 = 152849955315820821723965975135328 :=
  phaseBlock_append rec_1_16_2369_0_join0 rec_1_16_2369_0_join2 rfl rfl rfl
private theorem rec_1_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 640 256 = 53978903471348491114698979709376 :=
  phaseBlock_append rec_1_16_2369_0_part5 rec_1_16_2369_0_part6 rfl rfl rfl
private theorem rec_1_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1024 256 = 48106155930358381857378937352640 :=
  phaseBlock_append rec_1_16_2369_0_part8 rec_1_16_2369_0_part9 rfl rfl rfl
private theorem rec_1_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 896 384 = 73611822104566182212323759841952 :=
  phaseBlock_append rec_1_16_2369_0_part7 rec_1_16_2369_0_join5 rfl rfl rfl
private theorem rec_1_16_2369_0_join7 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 640 640 = 127590725575914673327022739551328 :=
  phaseBlock_append rec_1_16_2369_0_join4 rec_1_16_2369_0_join6 rfl rfl rfl
private theorem rec_1_16_2369_0_join8 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 0 1280 = 280440680891735495050988714686656 :=
  phaseBlock_append rec_1_16_2369_0_join3 rec_1_16_2369_0_join7 rfl rfl rfl
private theorem rec_1_16_2369_0_join9 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1280 256 = 44314831061317254392848206000576 :=
  phaseBlock_append rec_1_16_2369_0_part10 rec_1_16_2369_0_part11 rfl rfl rfl
private theorem rec_1_16_2369_0_join10 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1664 256 = 38810354441745279062374645993920 :=
  phaseBlock_append rec_1_16_2369_0_part13 rec_1_16_2369_0_part14 rfl rfl rfl
private theorem rec_1_16_2369_0_join11 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1536 384 = 59576559884071789217619865006752 :=
  phaseBlock_append rec_1_16_2369_0_part12 rec_1_16_2369_0_join10 rfl rfl rfl
private theorem rec_1_16_2369_0_join12 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1280 640 = 103891390945389043610468071007328 :=
  phaseBlock_append rec_1_16_2369_0_join9 rec_1_16_2369_0_join11 rfl rfl rfl
private theorem rec_1_16_2369_0_join13 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1920 256 = 35260486154339568567017940144576 :=
  phaseBlock_append rec_1_16_2369_0_part15 rec_1_16_2369_0_part16 rfl rfl rfl
private theorem rec_1_16_2369_0_join14 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2304 256 = 30112124040250430523944943153600 :=
  phaseBlock_append rec_1_16_2369_0_part18 rec_1_16_2369_0_part19 rfl rfl rfl
private theorem rec_1_16_2369_0_join15 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2176 384 = 46440690947926926719713556398752 :=
  phaseBlock_append rec_1_16_2369_0_part17 rec_1_16_2369_0_join14 rfl rfl rfl
private theorem rec_1_16_2369_0_join16 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1920 640 = 81701177102266495286731496543328 :=
  phaseBlock_append rec_1_16_2369_0_join13 rec_1_16_2369_0_join15 rfl rfl rfl
private theorem rec_1_16_2369_0_join17 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 1280 1280 = 185592568047655538897199567550656 :=
  phaseBlock_append rec_1_16_2369_0_join12 rec_1_16_2369_0_join16 rfl rfl rfl
private theorem rec_1_16_2369_0_join18 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 0 2560 = 466033248939391033948188282237312 :=
  phaseBlock_append rec_1_16_2369_0_join8 rec_1_16_2369_0_join17 rfl rfl rfl
private theorem rec_1_16_2369_0_join19 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2560 256 = 26795629841508104721938423879637 :=
  phaseBlock_append rec_1_16_2369_0_part20 rec_1_16_2369_0_part21 rfl rfl rfl
private theorem rec_1_16_2369_0_join20 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2944 256 = 21991304801311965401325404002415 :=
  phaseBlock_append rec_1_16_2369_0_part23 rec_1_16_2369_0_part24 rfl rfl rfl
private theorem rec_1_16_2369_0_join21 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2816 384 = 34173954341467672228476912899641 :=
  phaseBlock_append rec_1_16_2369_0_part22 rec_1_16_2369_0_join20 rfl rfl rfl
private theorem rec_1_16_2369_0_join22 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2560 640 = 60969584182975776950415336779278 :=
  phaseBlock_append rec_1_16_2369_0_join19 rec_1_16_2369_0_join21 rfl rfl rfl
private theorem rec_1_16_2369_0_join23 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3200 256 = 18900155800263703690384065364914 :=
  phaseBlock_append rec_1_16_2369_0_part25 rec_1_16_2369_0_part26 rfl rfl rfl
private theorem rec_1_16_2369_0_join24 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3584 256 = 14427820770130867472962023491761 :=
  phaseBlock_append rec_1_16_2369_0_part28 rec_1_16_2369_0_part29 rfl rfl rfl
private theorem rec_1_16_2369_0_join25 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3456 384 = 22746232833418148056033235711858 :=
  phaseBlock_append rec_1_16_2369_0_part27 rec_1_16_2369_0_join24 rfl rfl rfl
private theorem rec_1_16_2369_0_join26 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3200 640 = 41646388633681851746417301076772 :=
  phaseBlock_append rec_1_16_2369_0_join23 rec_1_16_2369_0_join25 rfl rfl rfl
private theorem rec_1_16_2369_0_join27 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2560 1280 = 102615972816657628696832637856050 :=
  phaseBlock_append rec_1_16_2369_0_join22 rec_1_16_2369_0_join26 rfl rfl rfl
private theorem rec_1_16_2369_0_join28 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3840 256 = 11553986679246575030754783556285 :=
  phaseBlock_append rec_1_16_2369_0_part30 rec_1_16_2369_0_part31 rfl rfl rfl
private theorem rec_1_16_2369_0_join29 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4224 256 = 7401622033471463375852568441717 :=
  phaseBlock_append rec_1_16_2369_0_part33 rec_1_16_2369_0_part34 rfl rfl rfl
private theorem rec_1_16_2369_0_join30 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4096 384 = 12127441727074896181673746331295 :=
  phaseBlock_append rec_1_16_2369_0_part32 rec_1_16_2369_0_join29 rfl rfl rfl
private theorem rec_1_16_2369_0_join31 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3840 640 = 23681428406321471212428529887580 :=
  phaseBlock_append rec_1_16_2369_0_join28 rec_1_16_2369_0_join30 rfl rfl rfl
private theorem rec_1_16_2369_0_join32 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4480 256 = 4737109340135517536731825229175 :=
  phaseBlock_append rec_1_16_2369_0_part35 rec_1_16_2369_0_part36 rfl rfl rfl
private theorem rec_1_16_2369_0_join33 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4864 219 = 917860761349022565128636188062 :=
  phaseBlock_append rec_1_16_2369_0_part38 rec_1_16_2369_0_part39 rfl rfl rfl
private theorem rec_1_16_2369_0_join34 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4736 347 = 2312741297415134110166159066400 :=
  phaseBlock_append rec_1_16_2369_0_part37 rec_1_16_2369_0_join33 rfl rfl rfl
private theorem rec_1_16_2369_0_join35 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 4480 603 = 7049850637550651646897984295575 :=
  phaseBlock_append rec_1_16_2369_0_join32 rec_1_16_2369_0_join34 rfl rfl rfl
private theorem rec_1_16_2369_0_join36 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 3840 1243 = 30731279043872122859326514183155 :=
  phaseBlock_append rec_1_16_2369_0_join31 rec_1_16_2369_0_join35 rfl rfl rfl
private theorem rec_1_16_2369_0_join37 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 2560 2523 = 133347251860529751556159152039205 :=
  phaseBlock_append rec_1_16_2369_0_join27 rec_1_16_2369_0_join36 rfl rfl rfl
private theorem rec_1_16_2369_0_join38 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 0) 0 5083 = 599380500799920785504347434276517 :=
  phaseBlock_append rec_1_16_2369_0_join18 rec_1_16_2369_0_join37 rfl rfl rfl

private theorem rec_1_16_2369_0 : fastPhase (bank 1 16).shape 179798 2369 138 1 0 2 0 = 599380500799920785504347434276517 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_1_16_2369_0_join38

private theorem rec_1_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 0 128 = 32659088895127484812674626914400 := by decide +kernel
private theorem rec_1_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 128 128 = 31597596340964635565636207204448 := by decide +kernel
private theorem rec_1_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 256 128 = 30549072117560066212965191002208 := by decide +kernel
private theorem rec_1_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 384 128 = 29513434358111537122487872845920 := by decide +kernel
private theorem rec_1_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 512 128 = 28490601274478006718807943268448 := by decide +kernel
private theorem rec_1_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 640 128 = 27480491157154489786542972115040 := by decide +kernel
private theorem rec_1_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 768 128 = 26483022375246915773560891861088 := by decide +kernel
private theorem rec_1_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 896 128 = 25498113376446987094216480929888 := by decide +kernel
private theorem rec_1_16_2369_1_part8 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1024 128 = 24525682687007037432587847010400 := by decide +kernel
private theorem rec_1_16_2369_1_part9 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1152 128 = 23565648911714890045712910375008 := by decide +kernel
private theorem rec_1_16_2369_1_part10 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1280 128 = 22617930733868716066825887197280 := by decide +kernel
private theorem rec_1_16_2369_1_part11 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1408 128 = 21682446915251892808593772869728 := by decide +kernel
private theorem rec_1_16_2369_1_part12 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1536 128 = 20759116296107862066352825321568 := by decide +kernel
private theorem rec_1_16_2369_1_part13 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1664 128 = 19847857795114988421345048336480 := by decide +kernel
private theorem rec_1_16_2369_1_part14 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1792 128 = 18948590409361417543954674870368 := by decide +kernel
private theorem rec_1_16_2369_1_part15 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1920 128 = 18061233214319934496944650369120 := by decide +kernel
private theorem rec_1_16_2369_1_part16 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2048 128 = 17185705363822822038693116086368 := by decide +kernel
private theorem rec_1_16_2369_1_part17 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2176 128 = 16321926090036718926429892401248 := by decide +kernel
private theorem rec_1_16_2369_1_part18 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2304 128 = 15469814703437478219472962136160 := by decide +kernel
private theorem rec_1_16_2369_1_part19 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2432 128 = 14629290592785025582464953874528 := by decide +kernel
private theorem rec_1_16_2369_1_part20 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2560 128 = 13800273517241821259874793567568 := by decide +kernel
private theorem rec_1_16_2369_1_part21 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2688 128 = 12982684041697900097158944816186 := by decide +kernel
private theorem rec_1_16_2369_1_part22 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2816 128 = 12176441800546887375858824203534 := by decide +kernel
private theorem rec_1_16_2369_1_part23 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2944 128 = 11381466232337739413603332329126 := by decide +kernel
private theorem rec_1_16_2369_1_part24 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3072 128 = 10597676854927121754818761734760 := by decide +kernel
private theorem rec_1_16_2369_1_part25 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3200 128 = 9824993263735112030410918079648 := by decide +kernel
private theorem rec_1_16_2369_1_part26 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3328 128 = 9063335132093107030860326473610 := by decide +kernel
private theorem rec_1_16_2369_1_part27 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3456 128 = 8312622212928989959766719800896 := by decide +kernel
private theorem rec_1_16_2369_1_part28 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3584 128 = 7572774336991265376662994772542 := by decide +kernel
private theorem rec_1_16_2369_1_part29 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3712 128 = 6843711412865108686937740671084 := by decide +kernel
private theorem rec_1_16_2369_1_part30 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3840 128 = 6125353427799838691465991270585 := by decide +kernel
private theorem rec_1_16_2369_1_part31 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3968 128 = 5417620447674725653496868640793 := by decide +kernel
private theorem rec_1_16_2369_1_part32 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4096 128 = 4720432616104862339290645110616 := by decide +kernel
private theorem rec_1_16_2369_1_part33 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4224 128 = 4033710154754852878570519886755 := by decide +kernel
private theorem rec_1_16_2369_1_part34 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4352 128 = 3357373364098710132376386013367 := by decide +kernel
private theorem rec_1_16_2369_1_part35 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4480 128 = 2691342622428062931810595122138 := by decide +kernel
private theorem rec_1_16_2369_1_part36 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4608 128 = 2035538386002794285768767416936 := by decide +kernel
private theorem rec_1_16_2369_1_part37 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4736 128 = 1389881189437895018741314188690 := by decide +kernel
private theorem rec_1_16_2369_1_part38 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4864 128 = 754291645437052690214583163316 := by decide +kernel
private theorem rec_1_16_2369_1_part39 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4992 91 = 155190885673851055167577264365 := by decide +kernel
private theorem rec_1_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 0 256 = 64256685236092120378310834118848 :=
  phaseBlock_append rec_1_16_2369_1_part0 rec_1_16_2369_1_part1 rfl rfl rfl
private theorem rec_1_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 384 256 = 58004035632589543841295816114368 :=
  phaseBlock_append rec_1_16_2369_1_part3 rec_1_16_2369_1_part4 rfl rfl rfl
private theorem rec_1_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 256 384 = 88553107750149610054261007116576 :=
  phaseBlock_append rec_1_16_2369_1_part2 rec_1_16_2369_1_join1 rfl rfl rfl
private theorem rec_1_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 0 640 = 152809792986241730432571841235424 :=
  phaseBlock_append rec_1_16_2369_1_join0 rec_1_16_2369_1_join2 rfl rfl rfl
private theorem rec_1_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 640 256 = 53963513532401405560103863976128 :=
  phaseBlock_append rec_1_16_2369_1_part5 rec_1_16_2369_1_part6 rfl rfl rfl
private theorem rec_1_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1024 256 = 48091331598721927478300757385408 :=
  phaseBlock_append rec_1_16_2369_1_part8 rec_1_16_2369_1_part9 rfl rfl rfl
private theorem rec_1_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 896 384 = 73589444975168914572517238315296 :=
  phaseBlock_append rec_1_16_2369_1_part7 rec_1_16_2369_1_join5 rfl rfl rfl
private theorem rec_1_16_2369_1_join7 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 640 640 = 127552958507570320132621102291424 :=
  phaseBlock_append rec_1_16_2369_1_join4 rec_1_16_2369_1_join6 rfl rfl rfl
private theorem rec_1_16_2369_1_join8 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 0 1280 = 280362751493812050565192943526848 :=
  phaseBlock_append rec_1_16_2369_1_join3 rec_1_16_2369_1_join7 rfl rfl rfl
private theorem rec_1_16_2369_1_join9 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1280 256 = 44300377649120608875419660067008 :=
  phaseBlock_append rec_1_16_2369_1_part10 rec_1_16_2369_1_part11 rfl rfl rfl
private theorem rec_1_16_2369_1_join10 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1664 256 = 38796448204476405965299723206848 :=
  phaseBlock_append rec_1_16_2369_1_part13 rec_1_16_2369_1_part14 rfl rfl rfl
private theorem rec_1_16_2369_1_join11 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1536 384 = 59555564500584268031652548528416 :=
  phaseBlock_append rec_1_16_2369_1_part12 rec_1_16_2369_1_join10 rfl rfl rfl
private theorem rec_1_16_2369_1_join12 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1280 640 = 103855942149704876907072208595424 :=
  phaseBlock_append rec_1_16_2369_1_join9 rec_1_16_2369_1_join11 rfl rfl rfl
private theorem rec_1_16_2369_1_join13 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1920 256 = 35246938578142756535637766455488 :=
  phaseBlock_append rec_1_16_2369_1_part15 rec_1_16_2369_1_part16 rfl rfl rfl
private theorem rec_1_16_2369_1_join14 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2304 256 = 30099105296222503801937916010688 :=
  phaseBlock_append rec_1_16_2369_1_part18 rec_1_16_2369_1_part19 rfl rfl rfl
private theorem rec_1_16_2369_1_join15 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2176 384 = 46421031386259222728367808411936 :=
  phaseBlock_append rec_1_16_2369_1_part17 rec_1_16_2369_1_join14 rfl rfl rfl
private theorem rec_1_16_2369_1_join16 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1920 640 = 81667969964401979264005574867424 :=
  phaseBlock_append rec_1_16_2369_1_join13 rec_1_16_2369_1_join15 rfl rfl rfl
private theorem rec_1_16_2369_1_join17 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 1280 1280 = 185523912114106856171077783462848 :=
  phaseBlock_append rec_1_16_2369_1_join12 rec_1_16_2369_1_join16 rfl rfl rfl
private theorem rec_1_16_2369_1_join18 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 0 2560 = 465886663607918906736270726989696 :=
  phaseBlock_append rec_1_16_2369_1_join8 rec_1_16_2369_1_join17 rfl rfl rfl
private theorem rec_1_16_2369_1_join19 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2560 256 = 26782957558939721357033738383754 :=
  phaseBlock_append rec_1_16_2369_1_part20 rec_1_16_2369_1_part21 rfl rfl rfl
private theorem rec_1_16_2369_1_join20 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2944 256 = 21979143087264861168422094063886 :=
  phaseBlock_append rec_1_16_2369_1_part23 rec_1_16_2369_1_part24 rfl rfl rfl
private theorem rec_1_16_2369_1_join21 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2816 384 = 34155584887811748544280918267420 :=
  phaseBlock_append rec_1_16_2369_1_part22 rec_1_16_2369_1_join20 rfl rfl rfl
private theorem rec_1_16_2369_1_join22 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2560 640 = 60938542446751469901314656651174 :=
  phaseBlock_append rec_1_16_2369_1_join19 rec_1_16_2369_1_join21 rfl rfl rfl
private theorem rec_1_16_2369_1_join23 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3200 256 = 18888328395828219061271244553258 :=
  phaseBlock_append rec_1_16_2369_1_part25 rec_1_16_2369_1_part26 rfl rfl rfl
private theorem rec_1_16_2369_1_join24 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3584 256 = 14416485749856374063600735443626 :=
  phaseBlock_append rec_1_16_2369_1_part28 rec_1_16_2369_1_part29 rfl rfl rfl
private theorem rec_1_16_2369_1_join25 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3456 384 = 22729107962785364023367455244522 :=
  phaseBlock_append rec_1_16_2369_1_part27 rec_1_16_2369_1_join24 rfl rfl rfl
private theorem rec_1_16_2369_1_join26 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3200 640 = 41617436358613583084638699797780 :=
  phaseBlock_append rec_1_16_2369_1_join23 rec_1_16_2369_1_join25 rfl rfl rfl
private theorem rec_1_16_2369_1_join27 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2560 1280 = 102555978805365052985953356448954 :=
  phaseBlock_append rec_1_16_2369_1_join22 rec_1_16_2369_1_join26 rfl rfl rfl
private theorem rec_1_16_2369_1_join28 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3840 256 = 11542973875474564344962859911378 :=
  phaseBlock_append rec_1_16_2369_1_part30 rec_1_16_2369_1_part31 rfl rfl rfl
private theorem rec_1_16_2369_1_join29 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4224 256 = 7391083518853563010946905900122 :=
  phaseBlock_append rec_1_16_2369_1_part33 rec_1_16_2369_1_part34 rfl rfl rfl
private theorem rec_1_16_2369_1_join30 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4096 384 = 12111516134958425350237551010738 :=
  phaseBlock_append rec_1_16_2369_1_part32 rec_1_16_2369_1_join29 rfl rfl rfl
private theorem rec_1_16_2369_1_join31 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3840 640 = 23654490010432989695200410922116 :=
  phaseBlock_append rec_1_16_2369_1_join28 rec_1_16_2369_1_join30 rfl rfl rfl
private theorem rec_1_16_2369_1_join32 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4480 256 = 4726881008430857217579362539074 :=
  phaseBlock_append rec_1_16_2369_1_part35 rec_1_16_2369_1_part36 rfl rfl rfl
private theorem rec_1_16_2369_1_join33 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4864 219 = 909482531110903745382160427681 :=
  phaseBlock_append rec_1_16_2369_1_part38 rec_1_16_2369_1_part39 rfl rfl rfl
private theorem rec_1_16_2369_1_join34 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4736 347 = 2299363720548798764123474616371 :=
  phaseBlock_append rec_1_16_2369_1_part37 rec_1_16_2369_1_join33 rfl rfl rfl
private theorem rec_1_16_2369_1_join35 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 4480 603 = 7026244728979655981702837155445 :=
  phaseBlock_append rec_1_16_2369_1_join32 rec_1_16_2369_1_join34 rfl rfl rfl
private theorem rec_1_16_2369_1_join36 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 3840 1243 = 30680734739412645676903248077561 :=
  phaseBlock_append rec_1_16_2369_1_join31 rec_1_16_2369_1_join35 rfl rfl rfl
private theorem rec_1_16_2369_1_join37 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 2560 2523 = 133236713544777698662856604526515 :=
  phaseBlock_append rec_1_16_2369_1_join27 rec_1_16_2369_1_join36 rfl rfl rfl
private theorem rec_1_16_2369_1_join38 :
    phaseBlock (fastLayerG (bank 1 16).shape 179798 2369 138 1 0 2 1) 0 5083 = 599123377152696605399127331516211 :=
  phaseBlock_append rec_1_16_2369_1_join18 rec_1_16_2369_1_join37 rfl rfl rfl

private theorem rec_1_16_2369_1 : fastPhase (bank 1 16).shape 179798 2369 138 1 0 2 1 = 599123377152696605399127331516211 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_1_16_2369_1_join38

theorem receipt_1_16 : Checked (bank 1 16) 138 0 2 := by
  refine checked_from_values (bank 1 16) 138 0 2
    (P3_7_1.checked (bank 1 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_22951_5082)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_1_16_2368_0 rec_1_16_2368_1 rec_1_16_2369_0 rec_1_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect1_checked (i : Fin 17) (hi : i ≠ 0) :
    Checked (bank 1 i) (reserve i) (excess 1) (seed 1) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact receipt_1_1
  · exact receipt_1_2
  · exact receipt_1_3
  · exact receipt_1_4
  · exact receipt_1_5
  · exact receipt_1_6
  · exact receipt_1_7
  · exact receipt_1_8
  · exact receipt_1_9
  · exact receipt_1_10
  · exact receipt_1_11
  · exact receipt_1_12
  · exact receipt_1_13
  · exact receipt_1_14
  · exact receipt_1_15
  · exact receipt_1_16

end Lower6961.Lo.RescueSource
