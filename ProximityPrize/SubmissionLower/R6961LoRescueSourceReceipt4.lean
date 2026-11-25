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


private theorem rec_4_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2368 1 1 2 1 0) 0 128 = 22846640236232950817760 := by decide +kernel
private theorem rec_4_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2368 1 1 2 1 0) 128 2 = 4707419854357670097 := by decide +kernel
private theorem rec_4_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2368 1 1 2 1 0) 0 130 = 22851347656087308487857 :=
  phaseBlock_append rec_4_1_2368_0_part0 rec_4_1_2368_0_part1 rfl rfl rfl

private theorem rec_4_1_2368_0 : fastPhase (bank 4 1).shape 179798 2368 1 1 2 1 0 = 22851347656087308487857 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_4_1_2368_0_join0

private theorem rec_4_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2368 1 1 2 1 1) 0 128 = 22450837341568748171872 := by decide +kernel
private theorem rec_4_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2368 1 1 2 1 1) 128 2 = 1558188445868512425 := by decide +kernel
private theorem rec_4_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2368 1 1 2 1 1) 0 130 = 22452395530014616684297 :=
  phaseBlock_append rec_4_1_2368_1_part0 rec_4_1_2368_1_part1 rfl rfl rfl

private theorem rec_4_1_2368_1 : fastPhase (bank 4 1).shape 179798 2368 1 1 2 1 1 = 22452395530014616684297 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_4_1_2368_1_join0

private theorem rec_4_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2369 1 1 2 1 0) 0 128 = 22846774475218018605504 := by decide +kernel
private theorem rec_4_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2369 1 1 2 1 0) 128 2 = 4707416686404044662 := by decide +kernel
private theorem rec_4_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2369 1 1 2 1 0) 0 130 = 22851481891904422650166 :=
  phaseBlock_append rec_4_1_2369_0_part0 rec_4_1_2369_0_part1 rfl rfl rfl

private theorem rec_4_1_2369_0 : fastPhase (bank 4 1).shape 179798 2369 1 1 2 1 0 = 22851481891904422650166 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_4_1_2369_0_join0

private theorem rec_4_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2369 1 1 2 1 1) 0 128 = 22450968982432194929280 := by decide +kernel
private theorem rec_4_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2369 1 1 2 1 1) 128 2 = 1558187404216795836 := by decide +kernel
private theorem rec_4_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 1).shape 179798 2369 1 1 2 1 1) 0 130 = 22452527169836411725116 :=
  phaseBlock_append rec_4_1_2369_1_part0 rec_4_1_2369_1_part1 rfl rfl rfl

private theorem rec_4_1_2369_1 : fastPhase (bank 4 1).shape 179798 2369 1 1 2 1 1 = 22452527169836411725116 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_4_1_2369_1_join0

theorem receipt_4_1 : Checked (bank 4 1) 1 2 1 := by
  refine checked_from_values (bank 4 1) 1 2 1
    (P3_7_1.checked (bank 4 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_1_2368_0 rec_4_1_2368_1 rec_4_1_2369_0 rec_4_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2368 2 1 2 1 0) 0 128 = 35785723169420142556768 := by decide +kernel
private theorem rec_4_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2368 2 1 2 1 0) 128 2 = 7387850094321546525 := by decide +kernel
private theorem rec_4_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2368 2 1 2 1 0) 0 130 = 35793111019514464103293 :=
  phaseBlock_append rec_4_2_2368_0_part0 rec_4_2_2368_0_part1 rfl rfl rfl

private theorem rec_4_2_2368_0 : fastPhase (bank 4 2).shape 179798 2368 2 1 2 1 0 = 35793111019514464103293 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_4_2_2368_0_join0

private theorem rec_4_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2368 2 1 2 1 1) 0 128 = 35166307172564790444768 := by decide +kernel
private theorem rec_4_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2368 2 1 2 1 1) 128 2 = 2445465266162294805 := by decide +kernel
private theorem rec_4_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2368 2 1 2 1 1) 0 130 = 35168752637830952739573 :=
  phaseBlock_append rec_4_2_2368_1_part0 rec_4_2_2368_1_part1 rfl rfl rfl

private theorem rec_4_2_2368_1 : fastPhase (bank 4 2).shape 179798 2368 2 1 2 1 1 = 35168752637830952739573 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_4_2_2368_1_join0

private theorem rec_4_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2369 2 1 2 1 0) 0 128 = 35785931486996376980736 := by decide +kernel
private theorem rec_4_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2369 2 1 2 1 0) 128 2 = 7387844797640087040 := by decide +kernel
private theorem rec_4_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2369 2 1 2 1 0) 0 130 = 35793319331794017067776 :=
  phaseBlock_append rec_4_2_2369_0_part0 rec_4_2_2369_0_part1 rfl rfl rfl

private theorem rec_4_2_2369_0 : fastPhase (bank 4 2).shape 179798 2369 2 1 2 1 0 = 35793319331794017067776 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_4_2_2369_0_join0

private theorem rec_4_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2369 2 1 2 1 1) 0 128 = 35166511461852126223296 := by decide +kernel
private theorem rec_4_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2369 2 1 2 1 1) 128 2 = 2445463523983760280 := by decide +kernel
private theorem rec_4_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 2).shape 179798 2369 2 1 2 1 1) 0 130 = 35168956925376109983576 :=
  phaseBlock_append rec_4_2_2369_1_part0 rec_4_2_2369_1_part1 rfl rfl rfl

private theorem rec_4_2_2369_1 : fastPhase (bank 4 2).shape 179798 2369 2 1 2 1 1 = 35168956925376109983576 :=
  phase_of_blockG (n := 130) (by decide +kernel) rec_4_2_2369_1_join0

theorem receipt_4_2 : Checked (bank 4 2) 2 2 1 := by
  refine checked_from_values (bank 4 2) 2 2 1
    (P3_7_1.checked (bank 4 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_2_2368_0 rec_4_2_2368_1 rec_4_2_2369_0 rec_4_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2368 3 1 2 1 0) 0 128 = 99448442450186864236320 := by decide +kernel
private theorem rec_4_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2368 3 1 2 1 0) 128 63 = 8824900055820631842192 := by decide +kernel
private theorem rec_4_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2368 3 1 2 1 0) 0 191 = 108273342506007496078512 :=
  phaseBlock_append rec_4_3_2368_0_part0 rec_4_3_2368_0_part1 rfl rfl rfl

private theorem rec_4_3_2368_0 : fastPhase (bank 4 3).shape 179798 2368 3 1 2 1 0 = 108273342506007496078512 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_3_2368_0_join0

private theorem rec_4_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2368 3 1 2 1 1) 0 128 = 98459789785474532801568 := by decide +kernel
private theorem rec_4_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2368 3 1 2 1 1) 128 63 = 8521759142502109450464 := by decide +kernel
private theorem rec_4_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2368 3 1 2 1 1) 0 191 = 106981548927976642252032 :=
  phaseBlock_append rec_4_3_2368_1_part0 rec_4_3_2368_1_part1 rfl rfl rfl

private theorem rec_4_3_2368_1 : fastPhase (bank 4 3).shape 179798 2368 3 1 2 1 1 = 106981548927976642252032 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_3_2368_1_join0

private theorem rec_4_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2369 3 1 2 1 0) 0 128 = 99449063365690020029184 := by decide +kernel
private theorem rec_4_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2369 3 1 2 1 0) 128 63 = 8824909434830534553984 := by decide +kernel
private theorem rec_4_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2369 3 1 2 1 0) 0 191 = 108273972800520554583168 :=
  phaseBlock_append rec_4_3_2369_0_part0 rec_4_3_2369_0_part1 rfl rfl rfl

private theorem rec_4_3_2369_0 : fastPhase (bank 4 3).shape 179798 2369 3 1 2 1 0 = 108273972800520554583168 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_3_2369_0_join0

private theorem rec_4_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2369 3 1 2 1 1) 0 128 = 98460402693931373030208 := by decide +kernel
private theorem rec_4_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2369 3 1 2 1 1) 128 63 = 8521768198252638030240 := by decide +kernel
private theorem rec_4_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 3).shape 179798 2369 3 1 2 1 1) 0 191 = 106982170892184011060448 :=
  phaseBlock_append rec_4_3_2369_1_part0 rec_4_3_2369_1_part1 rfl rfl rfl

private theorem rec_4_3_2369_1 : fastPhase (bank 4 3).shape 179798 2369 3 1 2 1 1 = 106982170892184011060448 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_3_2369_1_join0

theorem receipt_4_3 : Checked (bank 4 3) 3 2 1 := by
  refine checked_from_values (bank 4 3) 3 2 1
    (P3_7_1.checked (bank 4 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_3_2368_0 rec_4_3_2368_1 rec_4_3_2369_0 rec_4_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2368 4 1 2 1 0) 0 128 = 120869953475372653249152 := by decide +kernel
private theorem rec_4_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2368 4 1 2 1 0) 128 63 = 10736397433528757245248 := by decide +kernel
private theorem rec_4_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2368 4 1 2 1 0) 0 191 = 131606350908901410494400 :=
  phaseBlock_append rec_4_4_2368_0_part0 rec_4_4_2368_0_part1 rfl rfl rfl

private theorem rec_4_4_2368_0 : fastPhase (bank 4 4).shape 179798 2368 4 1 2 1 0 = 131606350908901410494400 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_4_2368_0_join0

private theorem rec_4_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2368 4 1 2 1 1) 0 128 = 119669423345252071451520 := by decide +kernel
private theorem rec_4_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2368 4 1 2 1 1) 128 63 = 10367668443141688815696 := by decide +kernel
private theorem rec_4_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2368 4 1 2 1 1) 0 191 = 130037091788393760267216 :=
  phaseBlock_append rec_4_4_2368_1_part0 rec_4_4_2368_1_part1 rfl rfl rfl

private theorem rec_4_4_2368_1 : fastPhase (bank 4 4).shape 179798 2368 4 1 2 1 1 = 130037091788393760267216 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_4_2368_1_join0

private theorem rec_4_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2369 4 1 2 1 0) 0 128 = 120870703677548401289856 := by decide +kernel
private theorem rec_4_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2369 4 1 2 1 0) 128 63 = 10736408505285564575040 := by decide +kernel
private theorem rec_4_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2369 4 1 2 1 0) 0 191 = 131607112182833965864896 :=
  phaseBlock_append rec_4_4_2369_0_part0 rec_4_4_2369_0_part1 rfl rfl rfl

private theorem rec_4_4_2369_0 : fastPhase (bank 4 4).shape 179798 2369 4 1 2 1 0 = 131607112182833965864896 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_4_2369_0_join0

private theorem rec_4_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2369 4 1 2 1 1) 0 128 = 119670163873679454011904 := by decide +kernel
private theorem rec_4_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2369 4 1 2 1 1) 128 63 = 10367679133716447541824 := by decide +kernel
private theorem rec_4_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 4).shape 179798 2369 4 1 2 1 1) 0 191 = 130037843007395901553728 :=
  phaseBlock_append rec_4_4_2369_1_part0 rec_4_4_2369_1_part1 rfl rfl rfl

private theorem rec_4_4_2369_1 : fastPhase (bank 4 4).shape 179798 2369 4 1 2 1 1 = 130037843007395901553728 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_4_2369_1_join0

theorem receipt_4_4 : Checked (bank 4 4) 4 2 1 := by
  refine checked_from_values (bank 4 4) 4 2 1
    (P3_7_1.checked (bank 4 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_4_2368_0 rec_4_4_2368_1 rec_4_4_2369_0 rec_4_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2368 5 1 2 1 0) 0 128 = 150025824713288711761248 := by decide +kernel
private theorem rec_4_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2368 5 1 2 1 0) 128 63 = 13339336716502338995376 := by decide +kernel
private theorem rec_4_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2368 5 1 2 1 0) 0 191 = 163365161429791050756624 :=
  phaseBlock_append rec_4_5_2368_0_part0 rec_4_5_2368_0_part1 rfl rfl rfl

private theorem rec_4_5_2368_0 : fastPhase (bank 4 5).shape 179798 2368 5 1 2 1 0 = 163365161429791050756624 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_5_2368_0_join0

private theorem rec_4_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2368 5 1 2 1 1) 0 128 = 148537048169058347123808 := by decide +kernel
private theorem rec_4_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2368 5 1 2 1 1) 128 63 = 12881303477866593499296 := by decide +kernel
private theorem rec_4_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2368 5 1 2 1 1) 0 191 = 161418351646924940623104 :=
  phaseBlock_append rec_4_5_2368_1_part0 rec_4_5_2368_1_part1 rfl rfl rfl

private theorem rec_4_5_2368_1 : fastPhase (bank 4 5).shape 179798 2368 5 1 2 1 1 = 161418351646924940623104 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_5_2368_1_join0

private theorem rec_4_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2369 5 1 2 1 0) 0 128 = 150026750339716512637056 := by decide +kernel
private theorem rec_4_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2369 5 1 2 1 0) 128 63 = 13339350051540257650752 := by decide +kernel
private theorem rec_4_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2369 5 1 2 1 0) 0 191 = 163366100391256770287808 :=
  phaseBlock_append rec_4_5_2369_0_part0 rec_4_5_2369_0_part1 rfl rfl rfl

private theorem rec_4_5_2369_0 : fastPhase (bank 4 5).shape 179798 2369 5 1 2 1 0 = 163366100391256770287808 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_5_2369_0_join0

private theorem rec_4_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2369 5 1 2 1 1) 0 128 = 148537961860215202220736 := by decide +kernel
private theorem rec_4_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2369 5 1 2 1 1) 128 63 = 12881316354333399336672 := by decide +kernel
private theorem rec_4_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 5).shape 179798 2369 5 1 2 1 1) 0 191 = 161419278214548601557408 :=
  phaseBlock_append rec_4_5_2369_1_part0 rec_4_5_2369_1_part1 rfl rfl rfl

private theorem rec_4_5_2369_1 : fastPhase (bank 4 5).shape 179798 2369 5 1 2 1 1 = 161419278214548601557408 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_5_2369_1_join0

theorem receipt_4_5 : Checked (bank 4 5) 5 2 1 := by
  refine checked_from_values (bank 4 5) 5 2 1
    (P3_7_1.checked (bank 4 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_5_2368_0 rec_4_5_2368_1 rec_4_5_2369_0 rec_4_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2368 7 1 2 1 0) 0 128 = 251752284553163583401856 := by decide +kernel
private theorem rec_4_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2368 7 1 2 1 0) 128 63 = 22428293094306413458368 := by decide +kernel
private theorem rec_4_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2368 7 1 2 1 0) 0 191 = 274180577647469996860224 :=
  phaseBlock_append rec_4_6_2368_0_part0 rec_4_6_2368_0_part1 rfl rfl rfl

private theorem rec_4_6_2368_0 : fastPhase (bank 4 6).shape 179798 2368 7 1 2 1 0 = 274180577647469996860224 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_6_2368_0_join0

private theorem rec_4_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2368 7 1 2 1 1) 0 128 = 249258527845601450402688 := by decide +kernel
private theorem rec_4_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2368 7 1 2 1 1) 128 63 = 21658476191924698625856 := by decide +kernel
private theorem rec_4_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2368 7 1 2 1 1) 0 191 = 270917004037526149028544 :=
  phaseBlock_append rec_4_6_2368_1_part0 rec_4_6_2368_1_part1 rfl rfl rfl

private theorem rec_4_6_2368_1 : fastPhase (bank 4 6).shape 179798 2368 7 1 2 1 1 = 270917004037526149028544 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_6_2368_1_join0

private theorem rec_4_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2369 7 1 2 1 0) 0 128 = 251753819222599797882240 := by decide +kernel
private theorem rec_4_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2369 7 1 2 1 0) 128 63 = 22428314099491899066048 := by decide +kernel
private theorem rec_4_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2369 7 1 2 1 0) 0 191 = 274182133322091696948288 :=
  phaseBlock_append rec_4_6_2369_0_part0 rec_4_6_2369_0_part1 rfl rfl rfl

private theorem rec_4_6_2369_0 : fastPhase (bank 4 6).shape 179798 2369 7 1 2 1 0 = 274182133322091696948288 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_6_2369_0_join0

private theorem rec_4_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2369 7 1 2 1 1) 0 128 = 249260042727937092806976 := by decide +kernel
private theorem rec_4_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2369 7 1 2 1 1) 128 63 = 21658496476590380951712 := by decide +kernel
private theorem rec_4_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 6).shape 179798 2369 7 1 2 1 1) 0 191 = 270918539204527473758688 :=
  phaseBlock_append rec_4_6_2369_1_part0 rec_4_6_2369_1_part1 rfl rfl rfl

private theorem rec_4_6_2369_1 : fastPhase (bank 4 6).shape 179798 2369 7 1 2 1 1 = 270918539204527473758688 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_4_6_2369_1_join0

theorem receipt_4_6 : Checked (bank 4 6) 7 2 1 := by
  refine checked_from_values (bank 4 6) 7 2 1
    (P3_7_1.checked (bank 4 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_6_2368_0 rec_4_6_2368_1 rec_4_6_2369_0 rec_4_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2368 10 1 2 1 0) 0 128 = 888819228662398446102144 := by decide +kernel
private theorem rec_4_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2368 10 1 2 1 0) 128 128 = 280827418101924317333120 := by decide +kernel
private theorem rec_4_7_2368_0_part2 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2368 10 1 2 1 0) 256 22 = 4718735962214851739800 := by decide +kernel
private theorem rec_4_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2368 10 1 2 1 0) 128 150 = 285546154064139169072920 :=
  phaseBlock_append rec_4_7_2368_0_part1 rec_4_7_2368_0_part2 rfl rfl rfl
private theorem rec_4_7_2368_0_join1 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2368 10 1 2 1 0) 0 278 = 1174365382726537615175064 :=
  phaseBlock_append rec_4_7_2368_0_part0 rec_4_7_2368_0_join0 rfl rfl rfl

private theorem rec_4_7_2368_0 : fastPhase (bank 4 7).shape 179798 2368 10 1 2 1 0 = 1174365382726537615175064 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_7_2368_0_join1

private theorem rec_4_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2368 10 1 2 1 1) 0 128 = 883447206300650796772800 := by decide +kernel
private theorem rec_4_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2368 10 1 2 1 1) 128 128 = 276975020738468457655744 := by decide +kernel
private theorem rec_4_7_2368_1_part2 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2368 10 1 2 1 1) 256 22 = 4295438986652145381126 := by decide +kernel
private theorem rec_4_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2368 10 1 2 1 1) 128 150 = 281270459725120603036870 :=
  phaseBlock_append rec_4_7_2368_1_part1 rec_4_7_2368_1_part2 rfl rfl rfl
private theorem rec_4_7_2368_1_join1 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2368 10 1 2 1 1) 0 278 = 1164717666025771399809670 :=
  phaseBlock_append rec_4_7_2368_1_part0 rec_4_7_2368_1_join0 rfl rfl rfl

private theorem rec_4_7_2368_1 : fastPhase (bank 4 7).shape 179798 2368 10 1 2 1 1 = 1164717666025771399809670 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_7_2368_1_join1

private theorem rec_4_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2369 10 1 2 1 0) 0 128 = 888825246591192601555712 := by decide +kernel
private theorem rec_4_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2369 10 1 2 1 0) 128 128 = 280828062578955044729600 := by decide +kernel
private theorem rec_4_7_2369_0_part2 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2369 10 1 2 1 0) 256 22 = 4718733610014882732560 := by decide +kernel
private theorem rec_4_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2369 10 1 2 1 0) 128 150 = 285546796188969927462160 :=
  phaseBlock_append rec_4_7_2369_0_part1 rec_4_7_2369_0_part2 rfl rfl rfl
private theorem rec_4_7_2369_0_join1 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2369 10 1 2 1 0) 0 278 = 1174372042780162529017872 :=
  phaseBlock_append rec_4_7_2369_0_part0 rec_4_7_2369_0_join0 rfl rfl rfl

private theorem rec_4_7_2369_0 : fastPhase (bank 4 7).shape 179798 2369 10 1 2 1 0 = 1174372042780162529017872 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_7_2369_0_join1

private theorem rec_4_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2369 10 1 2 1 1) 0 128 = 883453173597397101209280 := by decide +kernel
private theorem rec_4_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2369 10 1 2 1 1) 128 128 = 276975654985783266854592 := by decide +kernel
private theorem rec_4_7_2369_1_part2 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2369 10 1 2 1 1) 256 22 = 4295436852844887768018 := by decide +kernel
private theorem rec_4_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2369 10 1 2 1 1) 128 150 = 281271091838628154622610 :=
  phaseBlock_append rec_4_7_2369_1_part1 rec_4_7_2369_1_part2 rfl rfl rfl
private theorem rec_4_7_2369_1_join1 :
    phaseBlock (fastLayerG (bank 4 7).shape 179798 2369 10 1 2 1 1) 0 278 = 1164724265436025255831890 :=
  phaseBlock_append rec_4_7_2369_1_part0 rec_4_7_2369_1_join0 rfl rfl rfl

private theorem rec_4_7_2369_1 : fastPhase (bank 4 7).shape 179798 2369 10 1 2 1 1 = 1164724265436025255831890 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_7_2369_1_join1

theorem receipt_4_7 : Checked (bank 4 7) 10 2 1 := by
  refine checked_from_values (bank 4 7) 10 2 1
    (P3_7_1.checked (bank 4 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_7_2368_0 rec_4_7_2368_1 rec_4_7_2369_0 rec_4_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2368 16 1 2 1 0) 0 128 = 2585523931944119041217088 := by decide +kernel
private theorem rec_4_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2368 16 1 2 1 0) 128 128 = 819667268483539292672576 := by decide +kernel
private theorem rec_4_8_2368_0_part2 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2368 16 1 2 1 0) 256 22 = 13808670118629054930844 := by decide +kernel
private theorem rec_4_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2368 16 1 2 1 0) 128 150 = 833475938602168347603420 :=
  phaseBlock_append rec_4_8_2368_0_part1 rec_4_8_2368_0_part2 rfl rfl rfl
private theorem rec_4_8_2368_0_join1 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2368 16 1 2 1 0) 0 278 = 3418999870546287388820508 :=
  phaseBlock_append rec_4_8_2368_0_part0 rec_4_8_2368_0_join0 rfl rfl rfl

private theorem rec_4_8_2368_0 : fastPhase (bank 4 8).shape 179798 2368 16 1 2 1 0 = 3418999870546287388820508 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_8_2368_0_join1

private theorem rec_4_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2368 16 1 2 1 1) 0 128 = 2569967778916326169208064 := by decide +kernel
private theorem rec_4_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2368 16 1 2 1 1) 128 128 = 808442062160791028204800 := by decide +kernel
private theorem rec_4_8_2368_1_part2 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2368 16 1 2 1 1) 256 22 = 12570200842590669067020 := by decide +kernel
private theorem rec_4_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2368 16 1 2 1 1) 128 150 = 821012263003381697271820 :=
  phaseBlock_append rec_4_8_2368_1_part1 rec_4_8_2368_1_part2 rfl rfl rfl
private theorem rec_4_8_2368_1_join1 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2368 16 1 2 1 1) 0 278 = 3390980041919707866479884 :=
  phaseBlock_append rec_4_8_2368_1_part0 rec_4_8_2368_1_join0 rfl rfl rfl

private theorem rec_4_8_2368_1 : fastPhase (bank 4 8).shape 179798 2368 16 1 2 1 1 = 3390980041919707866479884 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_8_2368_1_join1

private theorem rec_4_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2369 16 1 2 1 0) 0 128 = 2585541039929246791336064 := by decide +kernel
private theorem rec_4_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2369 16 1 2 1 0) 128 128 = 819669037794274981970048 := by decide +kernel
private theorem rec_4_8_2369_0_part2 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2369 16 1 2 1 0) 256 22 = 13808661515017649293112 := by decide +kernel
private theorem rec_4_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2369 16 1 2 1 0) 128 150 = 833477699309292631263160 :=
  phaseBlock_append rec_4_8_2369_0_part1 rec_4_8_2369_0_part2 rfl rfl rfl
private theorem rec_4_8_2369_0_join1 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2369 16 1 2 1 0) 0 278 = 3419018739238539422599224 :=
  phaseBlock_append rec_4_8_2369_0_part0 rec_4_8_2369_0_join0 rfl rfl rfl

private theorem rec_4_8_2369_0 : fastPhase (bank 4 8).shape 179798 2369 16 1 2 1 0 = 3419018739238539422599224 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_8_2369_0_join1

private theorem rec_4_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2369 16 1 2 1 1) 0 128 = 2569984742941128500332992 := by decide +kernel
private theorem rec_4_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2369 16 1 2 1 1) 128 128 = 808443803290107233135040 := by decide +kernel
private theorem rec_4_8_2369_1_part2 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2369 16 1 2 1 1) 256 22 = 12570193033351515712920 := by decide +kernel
private theorem rec_4_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2369 16 1 2 1 1) 128 150 = 821013996323458748847960 :=
  phaseBlock_append rec_4_8_2369_1_part1 rec_4_8_2369_1_part2 rfl rfl rfl
private theorem rec_4_8_2369_1_join1 :
    phaseBlock (fastLayerG (bank 4 8).shape 179798 2369 16 1 2 1 1) 0 278 = 3390998739264587249180952 :=
  phaseBlock_append rec_4_8_2369_1_part0 rec_4_8_2369_1_join0 rfl rfl rfl

private theorem rec_4_8_2369_1 : fastPhase (bank 4 8).shape 179798 2369 16 1 2 1 1 = 3390998739264587249180952 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_8_2369_1_join1

theorem receipt_4_8 : Checked (bank 4 8) 16 2 1 := by
  refine checked_from_values (bank 4 8) 16 2 1
    (P3_7_1.checked (bank 4 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_8_2368_0 rec_4_8_2368_1 rec_4_8_2369_0 rec_4_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2368 10 1 2 1 0) 0 128 = 888819228662398446102144 := by decide +kernel
private theorem rec_4_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2368 10 1 2 1 0) 128 128 = 280827418101924317333120 := by decide +kernel
private theorem rec_4_9_2368_0_part2 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2368 10 1 2 1 0) 256 22 = 4718735962214851739800 := by decide +kernel
private theorem rec_4_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2368 10 1 2 1 0) 128 150 = 285546154064139169072920 :=
  phaseBlock_append rec_4_9_2368_0_part1 rec_4_9_2368_0_part2 rfl rfl rfl
private theorem rec_4_9_2368_0_join1 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2368 10 1 2 1 0) 0 278 = 1174365382726537615175064 :=
  phaseBlock_append rec_4_9_2368_0_part0 rec_4_9_2368_0_join0 rfl rfl rfl

private theorem rec_4_9_2368_0 : fastPhase (bank 4 9).shape 179798 2368 10 1 2 1 0 = 1174365382726537615175064 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_9_2368_0_join1

private theorem rec_4_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2368 10 1 2 1 1) 0 128 = 883447206300650796772800 := by decide +kernel
private theorem rec_4_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2368 10 1 2 1 1) 128 128 = 276975020738468457655744 := by decide +kernel
private theorem rec_4_9_2368_1_part2 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2368 10 1 2 1 1) 256 22 = 4295438986652145381126 := by decide +kernel
private theorem rec_4_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2368 10 1 2 1 1) 128 150 = 281270459725120603036870 :=
  phaseBlock_append rec_4_9_2368_1_part1 rec_4_9_2368_1_part2 rfl rfl rfl
private theorem rec_4_9_2368_1_join1 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2368 10 1 2 1 1) 0 278 = 1164717666025771399809670 :=
  phaseBlock_append rec_4_9_2368_1_part0 rec_4_9_2368_1_join0 rfl rfl rfl

private theorem rec_4_9_2368_1 : fastPhase (bank 4 9).shape 179798 2368 10 1 2 1 1 = 1164717666025771399809670 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_9_2368_1_join1

private theorem rec_4_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2369 10 1 2 1 0) 0 128 = 888825246591192601555712 := by decide +kernel
private theorem rec_4_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2369 10 1 2 1 0) 128 128 = 280828062578955044729600 := by decide +kernel
private theorem rec_4_9_2369_0_part2 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2369 10 1 2 1 0) 256 22 = 4718733610014882732560 := by decide +kernel
private theorem rec_4_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2369 10 1 2 1 0) 128 150 = 285546796188969927462160 :=
  phaseBlock_append rec_4_9_2369_0_part1 rec_4_9_2369_0_part2 rfl rfl rfl
private theorem rec_4_9_2369_0_join1 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2369 10 1 2 1 0) 0 278 = 1174372042780162529017872 :=
  phaseBlock_append rec_4_9_2369_0_part0 rec_4_9_2369_0_join0 rfl rfl rfl

private theorem rec_4_9_2369_0 : fastPhase (bank 4 9).shape 179798 2369 10 1 2 1 0 = 1174372042780162529017872 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_9_2369_0_join1

private theorem rec_4_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2369 10 1 2 1 1) 0 128 = 883453173597397101209280 := by decide +kernel
private theorem rec_4_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2369 10 1 2 1 1) 128 128 = 276975654985783266854592 := by decide +kernel
private theorem rec_4_9_2369_1_part2 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2369 10 1 2 1 1) 256 22 = 4295436852844887768018 := by decide +kernel
private theorem rec_4_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2369 10 1 2 1 1) 128 150 = 281271091838628154622610 :=
  phaseBlock_append rec_4_9_2369_1_part1 rec_4_9_2369_1_part2 rfl rfl rfl
private theorem rec_4_9_2369_1_join1 :
    phaseBlock (fastLayerG (bank 4 9).shape 179798 2369 10 1 2 1 1) 0 278 = 1164724265436025255831890 :=
  phaseBlock_append rec_4_9_2369_1_part0 rec_4_9_2369_1_join0 rfl rfl rfl

private theorem rec_4_9_2369_1 : fastPhase (bank 4 9).shape 179798 2369 10 1 2 1 1 = 1164724265436025255831890 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_4_9_2369_1_join1

theorem receipt_4_9 : Checked (bank 4 9) 10 2 1 := by
  refine checked_from_values (bank 4 9) 10 2 1
    (P3_7_1.checked (bank 4 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_9_2368_0 rec_4_9_2368_1 rec_4_9_2369_0 rec_4_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2368 20 1 2 1 0) 0 128 = 5892078012369617572394592 := by decide +kernel
private theorem rec_4_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2368 20 1 2 1 0) 128 128 = 2904498735733278995277408 := by decide +kernel
private theorem rec_4_10_2368_0_part2 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2368 20 1 2 1 0) 256 114 = 661147287948318895948200 := by decide +kernel
private theorem rec_4_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2368 20 1 2 1 0) 128 242 = 3565646023681597891225608 :=
  phaseBlock_append rec_4_10_2368_0_part1 rec_4_10_2368_0_part2 rfl rfl rfl
private theorem rec_4_10_2368_0_join1 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2368 20 1 2 1 0) 0 370 = 9457724036051215463620200 :=
  phaseBlock_append rec_4_10_2368_0_part0 rec_4_10_2368_0_join0 rfl rfl rfl

private theorem rec_4_10_2368_0 : fastPhase (bank 4 10).shape 179798 2368 20 1 2 1 0 = 9457724036051215463620200 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_4_10_2368_0_join1

private theorem rec_4_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2368 20 1 2 1 1) 0 128 = 5867144574063975902233632 := by decide +kernel
private theorem rec_4_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2368 20 1 2 1 1) 128 128 = 2883682151704898133185568 := by decide +kernel
private theorem rec_4_10_2368_1_part2 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2368 20 1 2 1 1) 256 114 = 648549705099995306878650 := by decide +kernel
private theorem rec_4_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2368 20 1 2 1 1) 128 242 = 3532231856804893440064218 :=
  phaseBlock_append rec_4_10_2368_1_part1 rec_4_10_2368_1_part2 rfl rfl rfl
private theorem rec_4_10_2368_1_join1 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2368 20 1 2 1 1) 0 370 = 9399376430868869342297850 :=
  phaseBlock_append rec_4_10_2368_1_part0 rec_4_10_2368_1_join0 rfl rfl rfl

private theorem rec_4_10_2368_1 : fastPhase (bank 4 10).shape 179798 2368 20 1 2 1 1 = 9399376430868869342297850 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_4_10_2368_1_join1

private theorem rec_4_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2369 20 1 2 1 0) 0 128 = 5892120102750871636011456 := by decide +kernel
private theorem rec_4_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2369 20 1 2 1 0) 128 128 = 2904508710590234702662080 := by decide +kernel
private theorem rec_4_10_2369_0_part2 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2369 20 1 2 1 0) 256 114 = 661147747162660011970728 := by decide +kernel
private theorem rec_4_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2369 20 1 2 1 0) 128 242 = 3565656457752894714632808 :=
  phaseBlock_append rec_4_10_2369_0_part1 rec_4_10_2369_0_part2 rfl rfl rfl
private theorem rec_4_10_2369_0_join1 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2369 20 1 2 1 0) 0 370 = 9457776560503766350644264 :=
  phaseBlock_append rec_4_10_2369_0_part0 rec_4_10_2369_0_join0 rfl rfl rfl

private theorem rec_4_10_2369_0 : fastPhase (bank 4 10).shape 179798 2369 20 1 2 1 0 = 9457776560503766350644264 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_4_10_2369_0_join1

private theorem rec_4_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2369 20 1 2 1 1) 0 128 = 5867186408773178219433216 := by decide +kernel
private theorem rec_4_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2369 20 1 2 1 1) 128 128 = 2883692031754658793688320 := by decide +kernel
private theorem rec_4_10_2369_1_part2 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2369 20 1 2 1 1) 256 114 = 648550155679162332245778 := by decide +kernel
private theorem rec_4_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2369 20 1 2 1 1) 128 242 = 3532242187433821125934098 :=
  phaseBlock_append rec_4_10_2369_1_part1 rec_4_10_2369_1_part2 rfl rfl rfl
private theorem rec_4_10_2369_1_join1 :
    phaseBlock (fastLayerG (bank 4 10).shape 179798 2369 20 1 2 1 1) 0 370 = 9399428596206999345367314 :=
  phaseBlock_append rec_4_10_2369_1_part0 rec_4_10_2369_1_join0 rfl rfl rfl

private theorem rec_4_10_2369_1 : fastPhase (bank 4 10).shape 179798 2369 20 1 2 1 1 = 9399428596206999345367314 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_4_10_2369_1_join1

theorem receipt_4_10 : Checked (bank 4 10) 20 2 1 := by
  refine checked_from_values (bank 4 10) 20 2 1
    (P3_7_1.checked (bank 4 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_10_2368_0 rec_4_10_2368_1 rec_4_10_2369_0 rec_4_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 0) 0 128 = 31766982451604992078338528 := by decide +kernel
private theorem rec_4_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 0) 128 128 = 19926532592604853208836576 := by decide +kernel
private theorem rec_4_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 0) 256 128 = 9768876860214477495171552 := by decide +kernel
private theorem rec_4_11_2368_0_part3 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 0) 384 109 = 2164191854283632415412566 := by decide +kernel
private theorem rec_4_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 0) 0 256 = 51693515044209845287175104 :=
  phaseBlock_append rec_4_11_2368_0_part0 rec_4_11_2368_0_part1 rfl rfl rfl
private theorem rec_4_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 0) 256 237 = 11933068714498109910584118 :=
  phaseBlock_append rec_4_11_2368_0_part2 rec_4_11_2368_0_part3 rfl rfl rfl
private theorem rec_4_11_2368_0_join2 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 0) 0 493 = 63626583758707955197759222 :=
  phaseBlock_append rec_4_11_2368_0_join0 rec_4_11_2368_0_join1 rfl rfl rfl

private theorem rec_4_11_2368_0 : fastPhase (bank 4 11).shape 179798 2368 32 1 2 1 0 = 63626583758707955197759222 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_4_11_2368_0_join2

private theorem rec_4_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 1) 0 128 = 31671207737414681472144992 := by decide +kernel
private theorem rec_4_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 1) 128 128 = 19840221492063338138322528 := by decide +kernel
private theorem rec_4_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 1) 256 128 = 9698607234260161073411680 := by decide +kernel
private theorem rec_4_11_2368_1_part3 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 1) 384 109 = 2121856791693511343324751 := by decide +kernel
private theorem rec_4_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 1) 0 256 = 51511429229478019610467520 :=
  phaseBlock_append rec_4_11_2368_1_part0 rec_4_11_2368_1_part1 rfl rfl rfl
private theorem rec_4_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 1) 256 237 = 11820464025953672416736431 :=
  phaseBlock_append rec_4_11_2368_1_part2 rec_4_11_2368_1_part3 rfl rfl rfl
private theorem rec_4_11_2368_1_join2 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2368 32 1 2 1 1) 0 493 = 63331893255431692027203951 :=
  phaseBlock_append rec_4_11_2368_1_join0 rec_4_11_2368_1_join1 rfl rfl rfl

private theorem rec_4_11_2368_1 : fastPhase (bank 4 11).shape 179798 2368 32 1 2 1 1 = 63331893255431692027203951 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_4_11_2368_1_join2

private theorem rec_4_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 0) 0 128 = 31767220302900433563998880 := by decide +kernel
private theorem rec_4_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 0) 128 128 = 19926622919091831387507360 := by decide +kernel
private theorem rec_4_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 0) 256 128 = 9768896824412796918479520 := by decide +kernel
private theorem rec_4_11_2369_0_part3 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 0) 384 109 = 2164192129206794268278235 := by decide +kernel
private theorem rec_4_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 0) 0 256 = 51693843221992264951506240 :=
  phaseBlock_append rec_4_11_2369_0_part0 rec_4_11_2369_0_part1 rfl rfl rfl
private theorem rec_4_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 0) 256 237 = 11933088953619591186757755 :=
  phaseBlock_append rec_4_11_2369_0_part2 rec_4_11_2369_0_part3 rfl rfl rfl
private theorem rec_4_11_2369_0_join2 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 0) 0 493 = 63626932175611856138263995 :=
  phaseBlock_append rec_4_11_2369_0_join0 rec_4_11_2369_0_join1 rfl rfl rfl

private theorem rec_4_11_2369_0 : fastPhase (bank 4 11).shape 179798 2369 32 1 2 1 0 = 63626932175611856138263995 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_4_11_2369_0_join2

private theorem rec_4_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 1) 0 128 = 31671444539212790585255840 := by decide +kernel
private theorem rec_4_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 1) 128 128 = 19840311276418047186671520 := by decide +kernel
private theorem rec_4_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 1) 256 128 = 9698627006103624550762400 := by decide +kernel
private theorem rec_4_11_2369_1_part3 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 1) 384 109 = 2121857062263599446716165 := by decide +kernel
private theorem rec_4_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 1) 0 256 = 51511755815630837771927360 :=
  phaseBlock_append rec_4_11_2369_1_part0 rec_4_11_2369_1_part1 rfl rfl rfl
private theorem rec_4_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 1) 256 237 = 11820484068367223997478565 :=
  phaseBlock_append rec_4_11_2369_1_part2 rec_4_11_2369_1_part3 rfl rfl rfl
private theorem rec_4_11_2369_1_join2 :
    phaseBlock (fastLayerG (bank 4 11).shape 179798 2369 32 1 2 1 1) 0 493 = 63332239883998061769405925 :=
  phaseBlock_append rec_4_11_2369_1_join0 rec_4_11_2369_1_join1 rfl rfl rfl

private theorem rec_4_11_2369_1 : fastPhase (bank 4 11).shape 179798 2369 32 1 2 1 1 = 63332239883998061769405925 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_4_11_2369_1_join2

theorem receipt_4_11 : Checked (bank 4 11) 32 2 1 := by
  refine checked_from_values (bank 4 11) 32 2 1
    (P3_7_1.checked (bank 4 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_11_2368_0 rec_4_11_2368_1 rec_4_11_2369_0 rec_4_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 0) 0 128 = 28762976929308104596009760 := by decide +kernel
private theorem rec_4_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 0) 128 128 = 18038764995389763339100960 := by decide +kernel
private theorem rec_4_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 0) 256 128 = 8841748447884643696907040 := by decide +kernel
private theorem rec_4_12_2368_0_part3 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 0) 384 109 = 1958472850552561303343460 := by decide +kernel
private theorem rec_4_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 0) 0 256 = 46801741924697867935110720 :=
  phaseBlock_append rec_4_12_2368_0_part0 rec_4_12_2368_0_part1 rfl rfl rfl
private theorem rec_4_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 0) 256 237 = 10800221298437205000250500 :=
  phaseBlock_append rec_4_12_2368_0_part2 rec_4_12_2368_0_part3 rfl rfl rfl
private theorem rec_4_12_2368_0_join2 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 0) 0 493 = 57601963223135072935361220 :=
  phaseBlock_append rec_4_12_2368_0_join0 rec_4_12_2368_0_join1 rfl rfl rfl

private theorem rec_4_12_2368_0 : fastPhase (bank 4 12).shape 179798 2368 31 1 2 1 0 = 57601963223135072935361220 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_4_12_2368_0_join2

private theorem rec_4_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 1) 0 128 = 28676216158612981116483360 := by decide +kernel
private theorem rec_4_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 1) 128 128 = 17960604041018205429172000 := by decide +kernel
private theorem rec_4_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 1) 256 128 = 8778135220926748466960160 := by decide +kernel
private theorem rec_4_12_2368_1_part3 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 1) 384 109 = 1920159969095259718461045 := by decide +kernel
private theorem rec_4_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 1) 0 256 = 46636820199631186545655360 :=
  phaseBlock_append rec_4_12_2368_1_part0 rec_4_12_2368_1_part1 rfl rfl rfl
private theorem rec_4_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 1) 256 237 = 10698295190022008185421205 :=
  phaseBlock_append rec_4_12_2368_1_part2 rec_4_12_2368_1_part3 rfl rfl rfl
private theorem rec_4_12_2368_1_join2 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2368 31 1 2 1 1) 0 493 = 57335115389653194731076565 :=
  phaseBlock_append rec_4_12_2368_1_join0 rec_4_12_2368_1_join1 rfl rfl rfl

private theorem rec_4_12_2368_1 : fastPhase (bank 4 12).shape 179798 2368 31 1 2 1 1 = 57335115389653194731076565 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_4_12_2368_1_join2

private theorem rec_4_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 0) 0 128 = 28763192710273070793528000 := by decide +kernel
private theorem rec_4_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 0) 128 128 = 18038847010216839342863040 := by decide +kernel
private theorem rec_4_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 0) 256 128 = 8841766629739536144388800 := by decide +kernel
private theorem rec_4_12_2369_0_part3 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 0) 384 109 = 1958473122829924870664880 := by decide +kernel
private theorem rec_4_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 0) 0 256 = 46802039720489910136391040 :=
  phaseBlock_append rec_4_12_2369_0_part0 rec_4_12_2369_0_part1 rfl rfl rfl
private theorem rec_4_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 0) 256 237 = 10800239752569461015053680 :=
  phaseBlock_append rec_4_12_2369_0_part2 rec_4_12_2369_0_part3 rfl rfl rfl
private theorem rec_4_12_2369_0_join2 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 0) 0 493 = 57602279473059371151444720 :=
  phaseBlock_append rec_4_12_2369_0_join0 rec_4_12_2369_0_join1 rfl rfl rfl

private theorem rec_4_12_2369_0 : fastPhase (bank 4 12).shape 179798 2369 31 1 2 1 0 = 57602279473059371151444720 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_4_12_2369_0_join2

private theorem rec_4_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 1) 0 128 = 28676430987448980196876800 := by decide +kernel
private theorem rec_4_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 1) 128 128 = 17960685563736034813370880 := by decide +kernel
private theorem rec_4_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 1) 256 128 = 8778153227784779478458880 := by decide +kernel
private theorem rec_4_12_2369_1_part3 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 1) 384 109 = 1920160236963651906548880 := by decide +kernel
private theorem rec_4_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 1) 0 256 = 46637116551185015010247680 :=
  phaseBlock_append rec_4_12_2369_1_part0 rec_4_12_2369_1_part1 rfl rfl rfl
private theorem rec_4_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 1) 256 237 = 10698313464748431385007760 :=
  phaseBlock_append rec_4_12_2369_1_part2 rec_4_12_2369_1_part3 rfl rfl rfl
private theorem rec_4_12_2369_1_join2 :
    phaseBlock (fastLayerG (bank 4 12).shape 179798 2369 31 1 2 1 1) 0 493 = 57335430015933446395255440 :=
  phaseBlock_append rec_4_12_2369_1_join0 rec_4_12_2369_1_join1 rfl rfl rfl

private theorem rec_4_12_2369_1 : fastPhase (bank 4 12).shape 179798 2369 31 1 2 1 1 = 57335430015933446395255440 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_4_12_2369_1_join2

theorem receipt_4_12 : Checked (bank 4 12) 31 2 1 := by
  refine checked_from_values (bank 4 12) 31 2 1
    (P3_7_1.checked (bank 4 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_12_2368_0 rec_4_12_2368_1 rec_4_12_2369_0 rec_4_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 0 128 = 126300637754159642337695872 := by decide +kernel
private theorem rec_4_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 128 128 = 92794135856787222450780288 := by decide +kernel
private theorem rec_4_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 256 128 = 61996265368454464561617024 := by decide +kernel
private theorem rec_4_13_2368_0_part3 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 384 128 = 35104808873995720921872512 := by decide +kernel
private theorem rec_4_13_2368_0_part4 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 512 128 = 13302428597263059955669120 := by decide +kernel
private theorem rec_4_13_2368_0_part5 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 640 38 = 644250507800761015575876 := by decide +kernel
private theorem rec_4_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 128 256 = 154790401225241687012397312 :=
  phaseBlock_append rec_4_13_2368_0_part1 rec_4_13_2368_0_part2 rfl rfl rfl
private theorem rec_4_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 0 384 = 281091038979401329350093184 :=
  phaseBlock_append rec_4_13_2368_0_part0 rec_4_13_2368_0_join0 rfl rfl rfl
private theorem rec_4_13_2368_0_join2 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 512 166 = 13946679105063820971244996 :=
  phaseBlock_append rec_4_13_2368_0_part4 rec_4_13_2368_0_part5 rfl rfl rfl
private theorem rec_4_13_2368_0_join3 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 384 294 = 49051487979059541893117508 :=
  phaseBlock_append rec_4_13_2368_0_part3 rec_4_13_2368_0_join2 rfl rfl rfl
private theorem rec_4_13_2368_0_join4 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 0) 0 678 = 330142526958460871243210692 :=
  phaseBlock_append rec_4_13_2368_0_join1 rec_4_13_2368_0_join3 rfl rfl rfl

private theorem rec_4_13_2368_0 : fastPhase (bank 4 13).shape 179798 2368 44 1 2 1 0 = 330142526958460871243210692 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_4_13_2368_0_join4

private theorem rec_4_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 0 128 = 126034743279225040312683264 := by decide +kernel
private theorem rec_4_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 128 128 = 92543713667751646627867392 := by decide +kernel
private theorem rec_4_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 256 128 = 61770906675160561438165760 := by decide +kernel
private theorem rec_4_13_2368_1_part3 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 384 128 = 34913984944793439773682432 := by decide +kernel
private theorem rec_4_13_2368_1_part4 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 512 128 = 13155491225927229896182528 := by decide +kernel
private theorem rec_4_13_2368_1_part5 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 640 38 = 610440716114942645299008 := by decide +kernel
private theorem rec_4_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 128 256 = 154314620342912208066033152 :=
  phaseBlock_append rec_4_13_2368_1_part1 rec_4_13_2368_1_part2 rfl rfl rfl
private theorem rec_4_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 0 384 = 280349363622137248378716416 :=
  phaseBlock_append rec_4_13_2368_1_part0 rec_4_13_2368_1_join0 rfl rfl rfl
private theorem rec_4_13_2368_1_join2 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 512 166 = 13765931942042172541481536 :=
  phaseBlock_append rec_4_13_2368_1_part4 rec_4_13_2368_1_part5 rfl rfl rfl
private theorem rec_4_13_2368_1_join3 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 384 294 = 48679916886835612315163968 :=
  phaseBlock_append rec_4_13_2368_1_part3 rec_4_13_2368_1_join2 rfl rfl rfl
private theorem rec_4_13_2368_1_join4 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2368 44 1 2 1 1) 0 678 = 329029280508972860693880384 :=
  phaseBlock_append rec_4_13_2368_1_join1 rec_4_13_2368_1_join3 rfl rfl rfl

private theorem rec_4_13_2368_1 : fastPhase (bank 4 13).shape 179798 2368 44 1 2 1 1 = 329029280508972860693880384 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_4_13_2368_1_join4

private theorem rec_4_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 0 128 = 126301632077649111366316800 := by decide +kernel
private theorem rec_4_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 128 128 = 92794657160447711570277120 := by decide +kernel
private theorem rec_4_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 256 128 = 61996489801557256702145280 := by decide +kernel
private theorem rec_4_13_2369_0_part3 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 384 128 = 35104873719948065067283200 := by decide +kernel
private theorem rec_4_13_2369_0_part4 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 512 128 = 13302432741854885962003200 := by decide +kernel
private theorem rec_4_13_2369_0_part5 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 640 38 = 644250011575594376132700 := by decide +kernel
private theorem rec_4_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 128 256 = 154791146962004968272422400 :=
  phaseBlock_append rec_4_13_2369_0_part1 rec_4_13_2369_0_part2 rfl rfl rfl
private theorem rec_4_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 0 384 = 281092779039654079638739200 :=
  phaseBlock_append rec_4_13_2369_0_part0 rec_4_13_2369_0_join0 rfl rfl rfl
private theorem rec_4_13_2369_0_join2 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 512 166 = 13946682753430480338135900 :=
  phaseBlock_append rec_4_13_2369_0_part4 rec_4_13_2369_0_part5 rfl rfl rfl
private theorem rec_4_13_2369_0_join3 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 384 294 = 49051556473378545405419100 :=
  phaseBlock_append rec_4_13_2369_0_part3 rec_4_13_2369_0_join2 rfl rfl rfl
private theorem rec_4_13_2369_0_join4 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 0) 0 678 = 330144335513032625044158300 :=
  phaseBlock_append rec_4_13_2369_0_join1 rec_4_13_2369_0_join3 rfl rfl rfl

private theorem rec_4_13_2369_0 : fastPhase (bank 4 13).shape 179798 2369 44 1 2 1 0 = 330144335513032625044158300 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_4_13_2369_0_join4

private theorem rec_4_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 0 128 = 126035734500730524718752000 := by decide +kernel
private theorem rec_4_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 128 128 = 92544232971937217048797440 := by decide +kernel
private theorem rec_4_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 256 128 = 61771129979647076477395200 := by decide +kernel
private theorem rec_4_13_2369_1_part3 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 384 128 = 34914049304333777309917440 := by decide +kernel
private theorem rec_4_13_2369_1_part4 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 512 128 = 13155495300640975993463040 := by decide +kernel
private theorem rec_4_13_2369_1_part5 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 640 38 = 610440246430002646676280 := by decide +kernel
private theorem rec_4_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 128 256 = 154315362951584293526192640 :=
  phaseBlock_append rec_4_13_2369_1_part1 rec_4_13_2369_1_part2 rfl rfl rfl
private theorem rec_4_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 0 384 = 280351097452314818244944640 :=
  phaseBlock_append rec_4_13_2369_1_part0 rec_4_13_2369_1_join0 rfl rfl rfl
private theorem rec_4_13_2369_1_join2 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 512 166 = 13765935547070978640139320 :=
  phaseBlock_append rec_4_13_2369_1_part4 rec_4_13_2369_1_part5 rfl rfl rfl
private theorem rec_4_13_2369_1_join3 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 384 294 = 48679984851404755950056760 :=
  phaseBlock_append rec_4_13_2369_1_part3 rec_4_13_2369_1_join2 rfl rfl rfl
private theorem rec_4_13_2369_1_join4 :
    phaseBlock (fastLayerG (bank 4 13).shape 179798 2369 44 1 2 1 1) 0 678 = 329031082303719574195001400 :=
  phaseBlock_append rec_4_13_2369_1_join1 rec_4_13_2369_1_join3 rfl rfl rfl

private theorem rec_4_13_2369_1 : fastPhase (bank 4 13).shape 179798 2369 44 1 2 1 1 = 329031082303719574195001400 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_4_13_2369_1_join4

theorem receipt_4_13 : Checked (bank 4 13) 44 2 1 := by
  refine checked_from_values (bank 4 13) 44 2 1
    (P3_7_1.checked (bank 4 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_13_2368_0 rec_4_13_2368_1 rec_4_13_2369_0 rec_4_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 0 128 = 1237243169092124159324479488 := by decide +kernel
private theorem rec_4_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 128 128 = 1001763859139088239861547008 := by decide +kernel
private theorem rec_4_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 256 128 = 777294195122599184713850880 := by decide +kernel
private theorem rec_4_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 384 128 = 568362042061423905150631936 := by decide +kernel
private theorem rec_4_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 512 128 = 379465921190449434606821376 := by decide +kernel
private theorem rec_4_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 640 128 = 215075069101258343963639808 := by decide +kernel
private theorem rec_4_14_2368_0_part6 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 768 128 = 79629496882704156829196288 := by decide +kernel
private theorem rec_4_14_2368_0_part7 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 896 29 = 2573617092701981744508976 := by decide +kernel
private theorem rec_4_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 0 256 = 2239007028231212399186026496 :=
  phaseBlock_append rec_4_14_2368_0_part0 rec_4_14_2368_0_part1 rfl rfl rfl
private theorem rec_4_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 256 256 = 1345656237184023089864482816 :=
  phaseBlock_append rec_4_14_2368_0_part2 rec_4_14_2368_0_part3 rfl rfl rfl
private theorem rec_4_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 0 512 = 3584663265415235489050509312 :=
  phaseBlock_append rec_4_14_2368_0_join0 rec_4_14_2368_0_join1 rfl rfl rfl
private theorem rec_4_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 512 256 = 594540990291707778570461184 :=
  phaseBlock_append rec_4_14_2368_0_part4 rec_4_14_2368_0_part5 rfl rfl rfl
private theorem rec_4_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 768 157 = 82203113975406138573705264 :=
  phaseBlock_append rec_4_14_2368_0_part6 rec_4_14_2368_0_part7 rfl rfl rfl
private theorem rec_4_14_2368_0_join5 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 512 413 = 676744104267113917144166448 :=
  phaseBlock_append rec_4_14_2368_0_join3 rec_4_14_2368_0_join4 rfl rfl rfl
private theorem rec_4_14_2368_0_join6 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 0) 0 925 = 4261407369682349406194675760 :=
  phaseBlock_append rec_4_14_2368_0_join2 rec_4_14_2368_0_join5 rfl rfl rfl

private theorem rec_4_14_2368_0 : fastPhase (bank 4 14).shape 179798 2368 76 1 2 1 0 = 4261407369682349406194675760 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_4_14_2368_0_join6

private theorem rec_4_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 0 128 = 1235396158850154586154119488 := by decide +kernel
private theorem rec_4_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 128 128 = 999979885724942469274677568 := by decide +kernel
private theorem rec_4_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 256 128 = 775609394297901463103451456 := by decide +kernel
private theorem rec_4_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 384 128 = 566812317051360127337181504 := by decide +kernel
private theorem rec_4_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 512 128 = 378086943150684720897503552 := by decide +kernel
private theorem rec_4_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 640 128 = 213902277584854617211547968 := by decide +kernel
private theorem rec_4_14_2368_1_part6 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 768 128 = 78698100307037719492538688 := by decide +kernel
private theorem rec_4_14_2368_1_part7 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 896 29 = 2399750198360994220865886 := by decide +kernel
private theorem rec_4_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 0 256 = 2235376044575097055428797056 :=
  phaseBlock_append rec_4_14_2368_1_part0 rec_4_14_2368_1_part1 rfl rfl rfl
private theorem rec_4_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 256 256 = 1342421711349261590440632960 :=
  phaseBlock_append rec_4_14_2368_1_part2 rec_4_14_2368_1_part3 rfl rfl rfl
private theorem rec_4_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 0 512 = 3577797755924358645869430016 :=
  phaseBlock_append rec_4_14_2368_1_join0 rec_4_14_2368_1_join1 rfl rfl rfl
private theorem rec_4_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 512 256 = 591989220735539338109051520 :=
  phaseBlock_append rec_4_14_2368_1_part4 rec_4_14_2368_1_part5 rfl rfl rfl
private theorem rec_4_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 768 157 = 81097850505398713713404574 :=
  phaseBlock_append rec_4_14_2368_1_part6 rec_4_14_2368_1_part7 rfl rfl rfl
private theorem rec_4_14_2368_1_join5 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 512 413 = 673087071240938051822456094 :=
  phaseBlock_append rec_4_14_2368_1_join3 rec_4_14_2368_1_join4 rfl rfl rfl
private theorem rec_4_14_2368_1_join6 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2368 76 1 2 1 1) 0 925 = 4250884827165296697691886110 :=
  phaseBlock_append rec_4_14_2368_1_join2 rec_4_14_2368_1_join5 rfl rfl rfl

private theorem rec_4_14_2368_1 : fastPhase (bank 4 14).shape 179798 2368 76 1 2 1 1 = 4250884827165296697691886110 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_4_14_2368_1_join6

private theorem rec_4_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 0 128 = 1237253113522486164288530912 := by decide +kernel
private theorem rec_4_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 128 128 = 1001770202858066515823163872 := by decide +kernel
private theorem rec_4_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 256 128 = 777297905537469409393281504 := by decide +kernel
private theorem rec_4_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 384 128 = 568363942372954389096765920 := by decide +kernel
private theorem rec_4_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 512 128 = 379466691297412059684645344 := by decide +kernel
private theorem rec_4_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 640 128 = 215075246503136302772140512 := by decide +kernel
private theorem rec_4_14_2369_0_part6 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 768 128 = 79629477580596493049711072 := by decide +kernel
private theorem rec_4_14_2369_0_part7 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 896 29 = 2573614518391349918985779 := by decide +kernel
private theorem rec_4_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 0 256 = 2239023316380552680111694784 :=
  phaseBlock_append rec_4_14_2369_0_part0 rec_4_14_2369_0_part1 rfl rfl rfl
private theorem rec_4_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 256 256 = 1345661847910423798490047424 :=
  phaseBlock_append rec_4_14_2369_0_part2 rec_4_14_2369_0_part3 rfl rfl rfl
private theorem rec_4_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 0 512 = 3584685164290976478601742208 :=
  phaseBlock_append rec_4_14_2369_0_join0 rec_4_14_2369_0_join1 rfl rfl rfl
private theorem rec_4_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 512 256 = 594541937800548362456785856 :=
  phaseBlock_append rec_4_14_2369_0_part4 rec_4_14_2369_0_part5 rfl rfl rfl
private theorem rec_4_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 768 157 = 82203092098987842968696851 :=
  phaseBlock_append rec_4_14_2369_0_part6 rec_4_14_2369_0_part7 rfl rfl rfl
private theorem rec_4_14_2369_0_join5 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 512 413 = 676745029899536205425482707 :=
  phaseBlock_append rec_4_14_2369_0_join3 rec_4_14_2369_0_join4 rfl rfl rfl
private theorem rec_4_14_2369_0_join6 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 0) 0 925 = 4261430194190512684027224915 :=
  phaseBlock_append rec_4_14_2369_0_join2 rec_4_14_2369_0_join5 rfl rfl rfl

private theorem rec_4_14_2369_0 : fastPhase (bank 4 14).shape 179798 2369 76 1 2 1 0 = 4261430194190512684027224915 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_4_14_2369_0_join6

private theorem rec_4_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 0 128 = 1235406081007480409459049888 := by decide +kernel
private theorem rec_4_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 128 128 = 999986213030024537877714336 := by decide +kernel
private theorem rec_4_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 256 128 = 775613093301513158101132704 := by decide +kernel
private theorem rec_4_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 384 128 = 566814210103549172071773600 := by decide +kernel
private theorem rec_4_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 512 128 = 378087709305272093536028064 := by decide +kernel
private theorem rec_4_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 640 128 = 213902453502130264255255968 := by decide +kernel
private theorem rec_4_14_2369_1_part6 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 768 128 = 78698081154653070216832416 := by decide +kernel
private theorem rec_4_14_2369_1_part7 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 896 29 = 2399747799584153299297989 := by decide +kernel
private theorem rec_4_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 0 256 = 2235392294037504947336764224 :=
  phaseBlock_append rec_4_14_2369_1_part0 rec_4_14_2369_1_part1 rfl rfl rfl
private theorem rec_4_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 256 256 = 1342427303405062330172906304 :=
  phaseBlock_append rec_4_14_2369_1_part2 rec_4_14_2369_1_part3 rfl rfl rfl
private theorem rec_4_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 0 512 = 3577819597442567277509670528 :=
  phaseBlock_append rec_4_14_2369_1_join0 rec_4_14_2369_1_join1 rfl rfl rfl
private theorem rec_4_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 512 256 = 591990162807402357791284032 :=
  phaseBlock_append rec_4_14_2369_1_part4 rec_4_14_2369_1_part5 rfl rfl rfl
private theorem rec_4_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 768 157 = 81097828954237223516130405 :=
  phaseBlock_append rec_4_14_2369_1_part6 rec_4_14_2369_1_part7 rfl rfl rfl
private theorem rec_4_14_2369_1_join5 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 512 413 = 673087991761639581307414437 :=
  phaseBlock_append rec_4_14_2369_1_join3 rec_4_14_2369_1_join4 rfl rfl rfl
private theorem rec_4_14_2369_1_join6 :
    phaseBlock (fastLayerG (bank 4 14).shape 179798 2369 76 1 2 1 1) 0 925 = 4250907589204206858817084965 :=
  phaseBlock_append rec_4_14_2369_1_join2 rec_4_14_2369_1_join5 rfl rfl rfl

private theorem rec_4_14_2369_1 : fastPhase (bank 4 14).shape 179798 2369 76 1 2 1 1 = 4250907589204206858817084965 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_4_14_2369_1_join6

theorem receipt_4_14 : Checked (bank 4 14) 76 2 1 := by
  refine checked_from_values (bank 4 14) 76 2 1
    (P3_7_1.checked (bank 4 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_14_2368_0 rec_4_14_2368_1 rec_4_14_2369_0 rec_4_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 0 128 = 5300176708512363591304038368 := by decide +kernel
private theorem rec_4_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 128 128 = 4590256692345486700291831776 := by decide +kernel
private theorem rec_4_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 256 128 = 3899880780665196901030373344 := by decide +kernel
private theorem rec_4_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 384 128 = 3235948088982323712644224992 := by decide +kernel
private theorem rec_4_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 512 128 = 2605321515536859814166595552 := by decide +kernel
private theorem rec_4_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 640 128 = 2014827800438536459819939808 := by decide +kernel
private theorem rec_4_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 768 128 = 1471257584807398894296557536 := by decide +kernel
private theorem rec_4_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 896 128 = 981365469914381768039192544 := by decide +kernel
private theorem rec_4_15_2368_0_part8 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 1024 128 = 551870076321884552521631712 := by decide +kernel
private theorem rec_4_15_2368_0_part9 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 1152 128 = 189454103024346955529304032 := by decide +kernel
private theorem rec_4_15_2368_0_part10 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 1280 14 = 1816231103588966337128107 := by decide +kernel
private theorem rec_4_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 0 256 = 9890433400857850291595870144 :=
  phaseBlock_append rec_4_15_2368_0_part0 rec_4_15_2368_0_part1 rfl rfl rfl
private theorem rec_4_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 384 256 = 5841269604519183526810820544 :=
  phaseBlock_append rec_4_15_2368_0_part3 rec_4_15_2368_0_part4 rfl rfl rfl
private theorem rec_4_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 256 384 = 9741150385184380427841193888 :=
  phaseBlock_append rec_4_15_2368_0_part2 rec_4_15_2368_0_join1 rfl rfl rfl
private theorem rec_4_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 0 640 = 19631583786042230719437064032 :=
  phaseBlock_append rec_4_15_2368_0_join0 rec_4_15_2368_0_join2 rfl rfl rfl
private theorem rec_4_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 768 256 = 2452623054721780662335750080 :=
  phaseBlock_append rec_4_15_2368_0_part6 rec_4_15_2368_0_part7 rfl rfl rfl
private theorem rec_4_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 640 384 = 4467450855160317122155689888 :=
  phaseBlock_append rec_4_15_2368_0_part5 rec_4_15_2368_0_join4 rfl rfl rfl
private theorem rec_4_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 1152 142 = 191270334127935921866432139 :=
  phaseBlock_append rec_4_15_2368_0_part9 rec_4_15_2368_0_part10 rfl rfl rfl
private theorem rec_4_15_2368_0_join7 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 1024 270 = 743140410449820474388063851 :=
  phaseBlock_append rec_4_15_2368_0_part8 rec_4_15_2368_0_join6 rfl rfl rfl
private theorem rec_4_15_2368_0_join8 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 640 654 = 5210591265610137596543753739 :=
  phaseBlock_append rec_4_15_2368_0_join5 rec_4_15_2368_0_join7 rfl rfl rfl
private theorem rec_4_15_2368_0_join9 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 0) 0 1294 = 24842175051652368315980817771 :=
  phaseBlock_append rec_4_15_2368_0_join3 rec_4_15_2368_0_join8 rfl rfl rfl

private theorem rec_4_15_2368_0 : fastPhase (bank 4 15).shape 179798 2368 105 1 2 1 0 = 24842175051652368315980817771 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_4_15_2368_0_join9

private theorem rec_4_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 0 128 = 5294645328313914552420699104 := by decide +kernel
private theorem rec_4_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 128 128 = 4584839372648773552670063584 := by decide +kernel
private theorem rec_4_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 256 128 = 3894632551986320230264466400 := by decide +kernel
private theorem rec_4_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 384 128 = 3230923694882323198239742944 := by decide +kernel
private theorem rec_4_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 512 128 = 2600575413088631806599580640 := by decide +kernel
private theorem rec_4_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 640 128 = 2010414160693751557596117984 := by decide +kernel
private theorem rec_4_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 768 128 = 1467230293263419521010543584 := by decide +kernel
private theorem rec_4_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 896 128 = 977778126981179749433695200 := by decide +kernel
private theorem rec_4_15_2368_1_part8 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 1024 128 = 548775997788958693546658784 := by decide +kernel
private theorem rec_4_15_2368_1_part9 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 1152 128 = 186906320527640617401367520 := by decide +kernel
private theorem rec_4_15_2368_1_part10 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 1280 14 = 1572963403289847191093107 := by decide +kernel
private theorem rec_4_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 0 256 = 9879484700962688105090762688 :=
  phaseBlock_append rec_4_15_2368_1_part0 rec_4_15_2368_1_part1 rfl rfl rfl
private theorem rec_4_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 384 256 = 5831499107970955004839323584 :=
  phaseBlock_append rec_4_15_2368_1_part3 rec_4_15_2368_1_part4 rfl rfl rfl
private theorem rec_4_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 256 384 = 9726131659957275235103789984 :=
  phaseBlock_append rec_4_15_2368_1_part2 rec_4_15_2368_1_join1 rfl rfl rfl
private theorem rec_4_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 0 640 = 19605616360919963340194552672 :=
  phaseBlock_append rec_4_15_2368_1_join0 rec_4_15_2368_1_join2 rfl rfl rfl
private theorem rec_4_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 768 256 = 2445008420244599270444238784 :=
  phaseBlock_append rec_4_15_2368_1_part6 rec_4_15_2368_1_part7 rfl rfl rfl
private theorem rec_4_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 640 384 = 4455422580938350828040356768 :=
  phaseBlock_append rec_4_15_2368_1_part5 rec_4_15_2368_1_join4 rfl rfl rfl
private theorem rec_4_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 1152 142 = 188479283930930464592460627 :=
  phaseBlock_append rec_4_15_2368_1_part9 rec_4_15_2368_1_part10 rfl rfl rfl
private theorem rec_4_15_2368_1_join7 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 1024 270 = 737255281719889158139119411 :=
  phaseBlock_append rec_4_15_2368_1_part8 rec_4_15_2368_1_join6 rfl rfl rfl
private theorem rec_4_15_2368_1_join8 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 640 654 = 5192677862658239986179476179 :=
  phaseBlock_append rec_4_15_2368_1_join5 rec_4_15_2368_1_join7 rfl rfl rfl
private theorem rec_4_15_2368_1_join9 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2368 105 1 2 1 1) 0 1294 = 24798294223578203326374028851 :=
  phaseBlock_append rec_4_15_2368_1_join3 rec_4_15_2368_1_join8 rfl rfl rfl

private theorem rec_4_15_2368_1 : fastPhase (bank 4 15).shape 179798 2368 105 1 2 1 1 = 24798294223578203326374028851 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_4_15_2368_1_join9

private theorem rec_4_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 0 128 = 5300220601406618136610979328 := by decide +kernel
private theorem rec_4_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 128 128 = 4590288966561353705796288000 := by decide +kernel
private theorem rec_4_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 256 128 = 3899903630344003509035908608 := by decide +kernel
private theorem rec_4_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 384 128 = 3235963487270022684051193344 := by decide +kernel
private theorem rec_4_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 512 128 = 2605331215702044184596954624 := by decide +kernel
private theorem rec_4_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 640 128 = 2014833336988650996672511488 := by decide +kernel
private theorem rec_4_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 768 128 = 1471260274603148354732736000 := by decide +kernel
private theorem rec_4_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 896 128 = 981366413282335957899099648 := by decide +kernel
private theorem rec_4_15_2369_0_part8 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 1024 128 = 551870158165280186170719744 := by decide +kernel
private theorem rec_4_15_2369_0_part9 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 1152 128 = 189453993932086316635405824 := by decide +kernel
private theorem rec_4_15_2369_0_part10 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 1280 14 = 1816229117198638605015504 := by decide +kernel
private theorem rec_4_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 0 256 = 9890509567967971842407267328 :=
  phaseBlock_append rec_4_15_2369_0_part0 rec_4_15_2369_0_part1 rfl rfl rfl
private theorem rec_4_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 384 256 = 5841294702972066868648147968 :=
  phaseBlock_append rec_4_15_2369_0_part3 rec_4_15_2369_0_part4 rfl rfl rfl
private theorem rec_4_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 256 384 = 9741198333316070377684056576 :=
  phaseBlock_append rec_4_15_2369_0_part2 rec_4_15_2369_0_join1 rfl rfl rfl
private theorem rec_4_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 0 640 = 19631707901284042220091323904 :=
  phaseBlock_append rec_4_15_2369_0_join0 rec_4_15_2369_0_join2 rfl rfl rfl
private theorem rec_4_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 768 256 = 2452626687885484312631835648 :=
  phaseBlock_append rec_4_15_2369_0_part6 rec_4_15_2369_0_part7 rfl rfl rfl
private theorem rec_4_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 640 384 = 4467460024874135309304347136 :=
  phaseBlock_append rec_4_15_2369_0_part5 rec_4_15_2369_0_join4 rfl rfl rfl
private theorem rec_4_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 1152 142 = 191270223049284955240421328 :=
  phaseBlock_append rec_4_15_2369_0_part9 rec_4_15_2369_0_part10 rfl rfl rfl
private theorem rec_4_15_2369_0_join7 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 1024 270 = 743140381214565141411141072 :=
  phaseBlock_append rec_4_15_2369_0_part8 rec_4_15_2369_0_join6 rfl rfl rfl
private theorem rec_4_15_2369_0_join8 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 640 654 = 5210600406088700450715488208 :=
  phaseBlock_append rec_4_15_2369_0_join5 rec_4_15_2369_0_join7 rfl rfl rfl
private theorem rec_4_15_2369_0_join9 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 0) 0 1294 = 24842308307372742670806812112 :=
  phaseBlock_append rec_4_15_2369_0_join3 rec_4_15_2369_0_join8 rfl rfl rfl

private theorem rec_4_15_2369_0 : fastPhase (bank 4 15).shape 179798 2369 105 1 2 1 0 = 24842308307372742670806812112 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_4_15_2369_0_join9

private theorem rec_4_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 0 128 = 5294689152102004229877283008 := by decide +kernel
private theorem rec_4_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 128 128 = 4584871590778455354674731200 := by decide +kernel
private theorem rec_4_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 256 128 = 3894655357286408314438711488 := by decide +kernel
private theorem rec_4_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 384 128 = 3230939059193403202699106496 := by decide +kernel
private theorem rec_4_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 512 128 = 2600585088381063480170035392 := by decide +kernel
private theorem rec_4_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 640 128 = 2010419680183868190960900288 := by decide +kernel
private theorem rec_4_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 768 128 = 1467232972527924178787432640 := by decide +kernel
private theorem rec_4_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 896 128 = 977779065069738303182739648 := by decide +kernel
private theorem rec_4_15_2369_1_part8 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 1024 128 = 548776078334989655708350656 := by decide +kernel
private theorem rec_4_15_2369_1_part9 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 1152 128 = 186906212857301776165263552 := by decide +kernel
private theorem rec_4_15_2369_1_part10 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 1280 14 = 1572961683766725193981494 := by decide +kernel
private theorem rec_4_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 0 256 = 9879560742880459584552014208 :=
  phaseBlock_append rec_4_15_2369_1_part0 rec_4_15_2369_1_part1 rfl rfl rfl
private theorem rec_4_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 384 256 = 5831524147574466682869141888 :=
  phaseBlock_append rec_4_15_2369_1_part3 rec_4_15_2369_1_part4 rfl rfl rfl
private theorem rec_4_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 256 384 = 9726179504860874997307853376 :=
  phaseBlock_append rec_4_15_2369_1_part2 rec_4_15_2369_1_join1 rfl rfl rfl
private theorem rec_4_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 0 640 = 19605740247741334581859867584 :=
  phaseBlock_append rec_4_15_2369_1_join0 rec_4_15_2369_1_join2 rfl rfl rfl
private theorem rec_4_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 768 256 = 2445012037597662481970172288 :=
  phaseBlock_append rec_4_15_2369_1_part6 rec_4_15_2369_1_part7 rfl rfl rfl
private theorem rec_4_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 640 384 = 4455431717781530672931072576 :=
  phaseBlock_append rec_4_15_2369_1_part5 rec_4_15_2369_1_join4 rfl rfl rfl
private theorem rec_4_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 1152 142 = 188479174541068501359245046 :=
  phaseBlock_append rec_4_15_2369_1_part9 rec_4_15_2369_1_part10 rfl rfl rfl
private theorem rec_4_15_2369_1_join7 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 1024 270 = 737255252876058157067595702 :=
  phaseBlock_append rec_4_15_2369_1_part8 rec_4_15_2369_1_join6 rfl rfl rfl
private theorem rec_4_15_2369_1_join8 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 640 654 = 5192686970657588829998668278 :=
  phaseBlock_append rec_4_15_2369_1_join5 rec_4_15_2369_1_join7 rfl rfl rfl
private theorem rec_4_15_2369_1_join9 :
    phaseBlock (fastLayerG (bank 4 15).shape 179798 2369 105 1 2 1 1) 0 1294 = 24798427218398923411858535862 :=
  phaseBlock_append rec_4_15_2369_1_join3 rec_4_15_2369_1_join8 rfl rfl rfl

private theorem rec_4_15_2369_1 : fastPhase (bank 4 15).shape 179798 2369 105 1 2 1 1 = 24798427218398923411858535862 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_4_15_2369_1_join9

theorem receipt_4_15 : Checked (bank 4 15) 105 2 1 := by
  refine checked_from_values (bank 4 15) 105 2 1
    (P3_7_1.checked (bank 4 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_15_2368_0 rec_4_15_2368_1 rec_4_15_2369_0 rec_4_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 0 128 = 19881681342626044599062203584 := by decide +kernel
private theorem rec_4_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 128 128 = 17973521775243968020196396224 := by decide +kernel
private theorem rec_4_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 256 128 = 16098207699783405056750619840 := by decide +kernel
private theorem rec_4_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 384 128 = 14265396476489810498378960064 := by decide +kernel
private theorem rec_4_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 512 128 = 12484702614002850507349265600 := by decide +kernel
private theorem rec_4_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 640 128 = 10765697828496978033823747264 := by decide +kernel
private theorem rec_4_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 768 128 = 9117911102822008231139577024 := by decide +kernel
private theorem rec_4_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 896 128 = 7550828745643693871089487040 := by decide +kernel
private theorem rec_4_16_2368_0_part8 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 1024 128 = 6073894450584300759202368704 := by decide +kernel
private theorem rec_4_16_2368_0_part9 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 1152 128 = 4696509355363183150023871680 := by decide +kernel
private theorem rec_4_16_2368_0_part10 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 1280 128 = 3428032100937359162397002944 := by decide +kernel
private theorem rec_4_16_2368_0_part11 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 1408 128 = 2277778890642086194742725824 := by decide +kernel
private theorem rec_4_16_2368_0_part12 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 1536 128 = 1255023549331436340340559040 := by decide +kernel
private theorem rec_4_16_2368_0_part13 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 1664 123 = 369451924662796213796276850 := by decide +kernel
private theorem rec_4_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 128 256 = 34071729475027373076947016064 :=
  phaseBlock_append rec_4_16_2368_0_part1 rec_4_16_2368_0_part2 rfl rfl rfl
private theorem rec_4_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 0 384 = 53953410817653417676009219648 :=
  phaseBlock_append rec_4_16_2368_0_part0 rec_4_16_2368_0_join0 rfl rfl rfl
private theorem rec_4_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 384 256 = 26750099090492661005728225664 :=
  phaseBlock_append rec_4_16_2368_0_part3 rec_4_16_2368_0_part4 rfl rfl rfl
private theorem rec_4_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 640 256 = 19883608931318986264963324288 :=
  phaseBlock_append rec_4_16_2368_0_part5 rec_4_16_2368_0_part6 rfl rfl rfl
private theorem rec_4_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 384 512 = 46633708021811647270691549952 :=
  phaseBlock_append rec_4_16_2368_0_join2 rec_4_16_2368_0_join3 rfl rfl rfl
private theorem rec_4_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 0 896 = 100587118839465064946700769600 :=
  phaseBlock_append rec_4_16_2368_0_join1 rec_4_16_2368_0_join4 rfl rfl rfl
private theorem rec_4_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 1024 256 = 10770403805947483909226240384 :=
  phaseBlock_append rec_4_16_2368_0_part8 rec_4_16_2368_0_part9 rfl rfl rfl
private theorem rec_4_16_2368_0_join7 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 896 384 = 18321232551591177780315727424 :=
  phaseBlock_append rec_4_16_2368_0_part7 rec_4_16_2368_0_join6 rfl rfl rfl
private theorem rec_4_16_2368_0_join8 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 1280 256 = 5705810991579445357139728768 :=
  phaseBlock_append rec_4_16_2368_0_part10 rec_4_16_2368_0_part11 rfl rfl rfl
private theorem rec_4_16_2368_0_join9 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 1536 251 = 1624475473994232554136835890 :=
  phaseBlock_append rec_4_16_2368_0_part12 rec_4_16_2368_0_part13 rfl rfl rfl
private theorem rec_4_16_2368_0_join10 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 1280 507 = 7330286465573677911276564658 :=
  phaseBlock_append rec_4_16_2368_0_join8 rec_4_16_2368_0_join9 rfl rfl rfl
private theorem rec_4_16_2368_0_join11 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 896 891 = 25651519017164855691592292082 :=
  phaseBlock_append rec_4_16_2368_0_join7 rec_4_16_2368_0_join10 rfl rfl rfl
private theorem rec_4_16_2368_0_join12 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 0) 0 1787 = 126238637856629920638293061682 :=
  phaseBlock_append rec_4_16_2368_0_join5 rec_4_16_2368_0_join11 rfl rfl rfl

private theorem rec_4_16_2368_0 : fastPhase (bank 4 16).shape 179798 2368 138 1 2 1 0 = 126238637856629920638293061682 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_4_16_2368_0_join12

private theorem rec_4_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 0 128 = 19866870125484819556469048320 := by decide +kernel
private theorem rec_4_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 128 128 = 17958906286877689576350065664 := by decide +kernel
private theorem rec_4_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 256 128 = 16083864949109865101527434240 := by decide +kernel
private theorem rec_4_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 384 128 = 14251403132942739910851421184 := by decide +kernel
private theorem rec_4_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 512 128 = 12471135007998836732845261824 := by decide +kernel
private theorem rec_4_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 640 128 = 10752631951902382660985758720 := by decide +kernel
private theorem rec_4_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 768 128 = 9105422609419884568983880704 := by decide +kernel
private theorem rec_4_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 896 128 = 7538992951600704526065361920 := by decide +kernel
private theorem rec_4_16_2368_1_part8 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 1024 128 = 6062786334917635212251300864 := by decide +kernel
private theorem rec_4_16_2368_1_part9 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 1152 128 = 4686203560407475333638759424 := by decide +kernel
private theorem rec_4_16_2368_1_part10 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 1280 128 = 3418602932811605037681361920 := by decide +kernel
private theorem rec_4_16_2368_1_part11 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 1408 128 = 2269300319716561328469894144 := by decide +kernel
private theorem rec_4_16_2368_1_part12 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 1536 128 = 1247569210694613482012902400 := by decide +kernel
private theorem rec_4_16_2368_1_part13 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 1664 123 = 363321936295554925731905050 := by decide +kernel
private theorem rec_4_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 128 256 = 34042771235987554677877499904 :=
  phaseBlock_append rec_4_16_2368_1_part1 rec_4_16_2368_1_part2 rfl rfl rfl
private theorem rec_4_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 0 384 = 53909641361472374234346548224 :=
  phaseBlock_append rec_4_16_2368_1_part0 rec_4_16_2368_1_join0 rfl rfl rfl
private theorem rec_4_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 384 256 = 26722538140941576643696683008 :=
  phaseBlock_append rec_4_16_2368_1_part3 rec_4_16_2368_1_part4 rfl rfl rfl
private theorem rec_4_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 640 256 = 19858054561322267229969639424 :=
  phaseBlock_append rec_4_16_2368_1_part5 rec_4_16_2368_1_part6 rfl rfl rfl
private theorem rec_4_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 384 512 = 46580592702263843873666322432 :=
  phaseBlock_append rec_4_16_2368_1_join2 rec_4_16_2368_1_join3 rfl rfl rfl
private theorem rec_4_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 0 896 = 100490234063736218108012870656 :=
  phaseBlock_append rec_4_16_2368_1_join1 rec_4_16_2368_1_join4 rfl rfl rfl
private theorem rec_4_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 1024 256 = 10748989895325110545890060288 :=
  phaseBlock_append rec_4_16_2368_1_part8 rec_4_16_2368_1_part9 rfl rfl rfl
private theorem rec_4_16_2368_1_join7 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 896 384 = 18287982846925815071955422208 :=
  phaseBlock_append rec_4_16_2368_1_part7 rec_4_16_2368_1_join6 rfl rfl rfl
private theorem rec_4_16_2368_1_join8 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 1280 256 = 5687903252528166366151256064 :=
  phaseBlock_append rec_4_16_2368_1_part10 rec_4_16_2368_1_part11 rfl rfl rfl
private theorem rec_4_16_2368_1_join9 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 1536 251 = 1610891146990168407744807450 :=
  phaseBlock_append rec_4_16_2368_1_part12 rec_4_16_2368_1_part13 rfl rfl rfl
private theorem rec_4_16_2368_1_join10 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 1280 507 = 7298794399518334773896063514 :=
  phaseBlock_append rec_4_16_2368_1_join8 rec_4_16_2368_1_join9 rfl rfl rfl
private theorem rec_4_16_2368_1_join11 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 896 891 = 25586777246444149845851485722 :=
  phaseBlock_append rec_4_16_2368_1_join7 rec_4_16_2368_1_join10 rfl rfl rfl
private theorem rec_4_16_2368_1_join12 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2368 138 1 2 1 1) 0 1787 = 126077011310180367953864356378 :=
  phaseBlock_append rec_4_16_2368_1_join5 rec_4_16_2368_1_join11 rfl rfl rfl

private theorem rec_4_16_2368_1 : fastPhase (bank 4 16).shape 179798 2368 138 1 2 1 1 = 126077011310180367953864356378 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_4_16_2368_1_join12

private theorem rec_4_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 0 128 = 19881849913812207169443354240 := by decide +kernel
private theorem rec_4_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 128 128 = 17973657584706460066030147200 := by decide +kernel
private theorem rec_4_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 256 128 = 16098315174410089207461402240 := by decide +kernel
private theorem rec_4_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 384 128 = 14265479731290202910179251840 := by decide +kernel
private theorem rec_4_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 512 128 = 12484765453433670125813520000 := by decide +kernel
private theorem rec_4_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 640 128 = 10765743747785892657392768640 := by decide +kernel
private theorem rec_4_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 768 128 = 9117943289289577375555344000 := by decide +kernel
private theorem rec_4_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 896 128 = 7550850080023508434760423040 := by decide +kernel
private theorem rec_4_16_2369_0_part8 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 1024 128 = 6073907508341319489499059840 := by decide +kernel
private theorem rec_4_16_2369_0_part9 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 1152 128 = 4696516408010265910505232000 := by decide +kernel
private theorem rec_4_16_2369_0_part10 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 1280 128 = 3428035117349997000966887040 := by decide +kernel
private theorem rec_4_16_2369_0_part11 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 1408 128 = 2277779538371328212736988800 := by decide +kernel
private theorem rec_4_16_2369_0_part12 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 1536 128 = 1255023195915013362544563840 := by decide +kernel
private theorem rec_4_16_2369_0_part13 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 1664 123 = 369451638416188964469799500 := by decide +kernel
private theorem rec_4_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 128 256 = 34071972759116549273491549440 :=
  phaseBlock_append rec_4_16_2369_0_part1 rec_4_16_2369_0_part2 rfl rfl rfl
private theorem rec_4_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 0 384 = 53953822672928756442934903680 :=
  phaseBlock_append rec_4_16_2369_0_part0 rec_4_16_2369_0_join0 rfl rfl rfl
private theorem rec_4_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 384 256 = 26750245184723873035992771840 :=
  phaseBlock_append rec_4_16_2369_0_part3 rec_4_16_2369_0_part4 rfl rfl rfl
private theorem rec_4_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 640 256 = 19883687037075470032948112640 :=
  phaseBlock_append rec_4_16_2369_0_part5 rec_4_16_2369_0_part6 rfl rfl rfl
private theorem rec_4_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 384 512 = 46633932221799343068940884480 :=
  phaseBlock_append rec_4_16_2369_0_join2 rec_4_16_2369_0_join3 rfl rfl rfl
private theorem rec_4_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 0 896 = 100587754894728099511875788160 :=
  phaseBlock_append rec_4_16_2369_0_join1 rec_4_16_2369_0_join4 rfl rfl rfl
private theorem rec_4_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 1024 256 = 10770423916351585400004291840 :=
  phaseBlock_append rec_4_16_2369_0_part8 rec_4_16_2369_0_part9 rfl rfl rfl
private theorem rec_4_16_2369_0_join7 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 896 384 = 18321273996375093834764714880 :=
  phaseBlock_append rec_4_16_2369_0_part7 rec_4_16_2369_0_join6 rfl rfl rfl
private theorem rec_4_16_2369_0_join8 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 1280 256 = 5705814655721325213703875840 :=
  phaseBlock_append rec_4_16_2369_0_part10 rec_4_16_2369_0_part11 rfl rfl rfl
private theorem rec_4_16_2369_0_join9 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 1536 251 = 1624474834331202327014363340 :=
  phaseBlock_append rec_4_16_2369_0_part12 rec_4_16_2369_0_part13 rfl rfl rfl
private theorem rec_4_16_2369_0_join10 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 1280 507 = 7330289490052527540718239180 :=
  phaseBlock_append rec_4_16_2369_0_join8 rec_4_16_2369_0_join9 rfl rfl rfl
private theorem rec_4_16_2369_0_join11 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 896 891 = 25651563486427621375482954060 :=
  phaseBlock_append rec_4_16_2369_0_join7 rec_4_16_2369_0_join10 rfl rfl rfl
private theorem rec_4_16_2369_0_join12 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 0) 0 1787 = 126239318381155720887358742220 :=
  phaseBlock_append rec_4_16_2369_0_join5 rec_4_16_2369_0_join11 rfl rfl rfl

private theorem rec_4_16_2369_0 : fastPhase (bank 4 16).shape 179798 2369 138 1 2 1 0 = 126239318381155720887358742220 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_4_16_2369_0_join12

private theorem rec_4_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 0 128 = 19867038506643233892380100480 := by decide +kernel
private theorem rec_4_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 128 128 = 17959041932254563778376542080 := by decide +kernel
private theorem rec_4_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 256 128 = 16083972283740287882732668800 := by decide +kernel
private theorem rec_4_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 384 128 = 14251486269991925864506615680 := by decide +kernel
private theorem rec_4_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 512 128 = 12471197750087663569094985600 := by decide +kernel
private theorem rec_4_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 640 128 = 10752677792431125244443895680 := by decide +kernel
private theorem rec_4_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 768 128 = 9105454733890145757260023680 := by decide +kernel
private theorem rec_4_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 896 128 = 7539014238935542809221654400 := by decide +kernel
private theorem rec_4_16_2369_1_part8 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 1024 128 = 6062799358779889153189726080 := by decide +kernel
private theorem rec_4_16_2369_1_part9 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 1152 128 = 4686210590516284809418876800 := by decide +kernel
private theorem rec_4_16_2369_1_part10 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 1280 128 = 3418605936257129281768490880 := by decide +kernel
private theorem rec_4_16_2369_1_part11 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 1408 128 = 2269300962272893773913745280 := by decide +kernel
private theorem rec_4_16_2369_1_part12 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 1536 128 = 1247568858130893405556656000 := by decide +kernel
private theorem rec_4_16_2369_1_part13 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 1664 123 = 363321654908563467215127375 := by decide +kernel
private theorem rec_4_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 128 256 = 34043014215994851661109210880 :=
  phaseBlock_append rec_4_16_2369_1_part1 rec_4_16_2369_1_part2 rfl rfl rfl
private theorem rec_4_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 0 384 = 53910052722638085553489311360 :=
  phaseBlock_append rec_4_16_2369_1_part0 rec_4_16_2369_1_join0 rfl rfl rfl
private theorem rec_4_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 384 256 = 26722684020079589433601601280 :=
  phaseBlock_append rec_4_16_2369_1_part3 rec_4_16_2369_1_part4 rfl rfl rfl
private theorem rec_4_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 640 256 = 19858132526321271001703919360 :=
  phaseBlock_append rec_4_16_2369_1_part5 rec_4_16_2369_1_part6 rfl rfl rfl
private theorem rec_4_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 384 512 = 46580816546400860435305520640 :=
  phaseBlock_append rec_4_16_2369_1_join2 rec_4_16_2369_1_join3 rfl rfl rfl
private theorem rec_4_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 0 896 = 100490869269038945988794832000 :=
  phaseBlock_append rec_4_16_2369_1_join1 rec_4_16_2369_1_join4 rfl rfl rfl
private theorem rec_4_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 1024 256 = 10749009949296173962608602880 :=
  phaseBlock_append rec_4_16_2369_1_part8 rec_4_16_2369_1_part9 rfl rfl rfl
private theorem rec_4_16_2369_1_join7 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 896 384 = 18288024188231716771830257280 :=
  phaseBlock_append rec_4_16_2369_1_part7 rec_4_16_2369_1_join6 rfl rfl rfl
private theorem rec_4_16_2369_1_join8 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 1280 256 = 5687906898530023055682236160 :=
  phaseBlock_append rec_4_16_2369_1_part10 rec_4_16_2369_1_part11 rfl rfl rfl
private theorem rec_4_16_2369_1_join9 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 1536 251 = 1610890513039456872771783375 :=
  phaseBlock_append rec_4_16_2369_1_part12 rec_4_16_2369_1_part13 rfl rfl rfl
private theorem rec_4_16_2369_1_join10 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 1280 507 = 7298797411569479928454019535 :=
  phaseBlock_append rec_4_16_2369_1_join8 rec_4_16_2369_1_join9 rfl rfl rfl
private theorem rec_4_16_2369_1_join11 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 896 891 = 25586821599801196700284276815 :=
  phaseBlock_append rec_4_16_2369_1_join7 rec_4_16_2369_1_join10 rfl rfl rfl
private theorem rec_4_16_2369_1_join12 :
    phaseBlock (fastLayerG (bank 4 16).shape 179798 2369 138 1 2 1 1) 0 1787 = 126077690868840142689079108815 :=
  phaseBlock_append rec_4_16_2369_1_join5 rec_4_16_2369_1_join11 rfl rfl rfl

private theorem rec_4_16_2369_1 : fastPhase (bank 4 16).shape 179798 2369 138 1 2 1 1 = 126077690868840142689079108815 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_4_16_2369_1_join12

theorem receipt_4_16 : Checked (bank 4 16) 138 2 1 := by
  refine checked_from_values (bank 4 16) 138 2 1
    (P3_7_1.checked (bank 4 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_16_2368_0 rec_4_16_2368_1 rec_4_16_2369_0 rec_4_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect4_checked (i : Fin 17) (hi : i ≠ 0) :
    Checked (bank 4 i) (reserve i) (excess 4) (seed 4) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact receipt_4_1
  · exact receipt_4_2
  · exact receipt_4_3
  · exact receipt_4_4
  · exact receipt_4_5
  · exact receipt_4_6
  · exact receipt_4_7
  · exact receipt_4_8
  · exact receipt_4_9
  · exact receipt_4_10
  · exact receipt_4_11
  · exact receipt_4_12
  · exact receipt_4_13
  · exact receipt_4_14
  · exact receipt_4_15
  · exact receipt_4_16

end Lower6961.Lo.RescueSource
