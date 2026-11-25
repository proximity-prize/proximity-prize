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


private theorem rec_0_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2368 1 1 0 1 0) 0 128 = 74506340672428595361586560 := by decide +kernel
private theorem rec_0_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2368 1 1 0 1 0) 128 128 = 39353754075167670571084191 := by decide +kernel
private theorem rec_0_1_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2368 1 1 0 1 0) 256 114 = 10328228599594895756117814 := by decide +kernel
private theorem rec_0_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2368 1 1 0 1 0) 128 242 = 49681982674762566327202005 :=
  phaseBlock_append rec_0_1_2368_0_part1 rec_0_1_2368_0_part2 rfl rfl rfl
private theorem rec_0_1_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2368 1 1 0 1 0) 0 370 = 124188323347191161688788565 :=
  phaseBlock_append rec_0_1_2368_0_part0 rec_0_1_2368_0_join0 rfl rfl rfl

private theorem rec_0_1_2368_0 : fastPhase (bank 0 1).shape 179798 2368 1 1 0 1 0 = 124188323347191161688788565 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_0_1_2368_0_join1

private theorem rec_0_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2368 1 1 0 1 1) 0 128 = 74210764645860012435535680 := by decide +kernel
private theorem rec_0_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2368 1 1 0 1 1) 128 128 = 39105503944390750353255044 := by decide +kernel
private theorem rec_0_1_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2368 1 1 0 1 1) 256 114 = 10143569733599243153018764 := by decide +kernel
private theorem rec_0_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2368 1 1 0 1 1) 128 242 = 49249073677989993506273808 :=
  phaseBlock_append rec_0_1_2368_1_part1 rec_0_1_2368_1_part2 rfl rfl rfl
private theorem rec_0_1_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2368 1 1 0 1 1) 0 370 = 123459838323850005941809488 :=
  phaseBlock_append rec_0_1_2368_1_part0 rec_0_1_2368_1_join0 rfl rfl rfl

private theorem rec_0_1_2368_1 : fastPhase (bank 0 1).shape 179798 2368 1 1 0 1 1 = 123459838323850005941809488 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_0_1_2368_1_join1

private theorem rec_0_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2369 1 1 0 1 0) 0 128 = 74506985542772710674541440 := by decide +kernel
private theorem rec_0_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2369 1 1 0 1 0) 128 128 = 39354017906312448866888598 := by decide +kernel
private theorem rec_0_1_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2369 1 1 0 1 0) 256 114 = 10328277779496434701319562 := by decide +kernel
private theorem rec_0_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2369 1 1 0 1 0) 128 242 = 49682295685808883568208160 :=
  phaseBlock_append rec_0_1_2369_0_part1 rec_0_1_2369_0_part2 rfl rfl rfl
private theorem rec_0_1_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2369 1 1 0 1 0) 0 370 = 124189281228581594242749600 :=
  phaseBlock_append rec_0_1_2369_0_part0 rec_0_1_2369_0_join0 rfl rfl rfl

private theorem rec_0_1_2369_0 : fastPhase (bank 0 1).shape 179798 2369 1 1 0 1 0 = 124189281228581594242749600 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_0_1_2369_0_join1

private theorem rec_0_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2369 1 1 0 1 1) 0 128 = 74211407416258991342608320 := by decide +kernel
private theorem rec_0_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2369 1 1 0 1 1) 128 128 = 39105766350735777428341302 := by decide +kernel
private theorem rec_0_1_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2369 1 1 0 1 1) 256 114 = 10143618144603480535257990 := by decide +kernel
private theorem rec_0_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2369 1 1 0 1 1) 128 242 = 49249384495339257963599292 :=
  phaseBlock_append rec_0_1_2369_1_part1 rec_0_1_2369_1_part2 rfl rfl rfl
private theorem rec_0_1_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 1).shape 179798 2369 1 1 0 1 1) 0 370 = 123460791911598249306207612 :=
  phaseBlock_append rec_0_1_2369_1_part0 rec_0_1_2369_1_join0 rfl rfl rfl

private theorem rec_0_1_2369_1 : fastPhase (bank 0 1).shape 179798 2369 1 1 0 1 1 = 123460791911598249306207612 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_0_1_2369_1_join1

theorem receipt_0_1 : Checked (bank 0 1) 1 0 1 := by
  refine checked_from_values (bank 0 1) 1 0 1
    (P3_7_1.checked (bank 0 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_1_2368_0 rec_0_1_2368_1 rec_0_1_2369_0 rec_0_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 0) 0 128 = 154556279811537460509226368 := by decide +kernel
private theorem rec_0_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 0) 128 128 = 100731719367823963645597056 := by decide +kernel
private theorem rec_0_2_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 0) 256 128 = 53771192309124363147711848 := by decide +kernel
private theorem rec_0_2_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 0) 384 109 = 13573678837855581428282115 := by decide +kernel
private theorem rec_0_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 0) 0 256 = 255287999179361424154823424 :=
  phaseBlock_append rec_0_2_2368_0_part0 rec_0_2_2368_0_part1 rfl rfl rfl
private theorem rec_0_2_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 0) 256 237 = 67344871146979944575993963 :=
  phaseBlock_append rec_0_2_2368_0_part2 rec_0_2_2368_0_part3 rfl rfl rfl
private theorem rec_0_2_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 0) 0 493 = 322632870326341368730817387 :=
  phaseBlock_append rec_0_2_2368_0_join0 rec_0_2_2368_0_join1 rfl rfl rfl

private theorem rec_0_2_2368_0 : fastPhase (bank 0 2).shape 179798 2368 2 1 0 1 0 = 322632870326341368730817387 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_2_2368_0_join2

private theorem rec_0_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 1) 0 128 = 154113713375836777934235968 := by decide +kernel
private theorem rec_0_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 1) 128 128 = 100342742867096932559350080 := by decide +kernel
private theorem rec_0_2_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 1) 256 128 = 53432257899483423073421185 := by decide +kernel
private theorem rec_0_2_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 1) 384 109 = 13321862159138954463202821 := by decide +kernel
private theorem rec_0_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 1) 0 256 = 254456456242933710493586048 :=
  phaseBlock_append rec_0_2_2368_1_part0 rec_0_2_2368_1_part1 rfl rfl rfl
private theorem rec_0_2_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 1) 256 237 = 66754120058622377536624006 :=
  phaseBlock_append rec_0_2_2368_1_part2 rec_0_2_2368_1_part3 rfl rfl rfl
private theorem rec_0_2_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2368 2 1 0 1 1) 0 493 = 321210576301556088030210054 :=
  phaseBlock_append rec_0_2_2368_1_join0 rec_0_2_2368_1_join1 rfl rfl rfl

private theorem rec_0_2_2368_1 : fastPhase (bank 0 2).shape 179798 2368 2 1 0 1 1 = 321210576301556088030210054 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_2_2368_1_join2

private theorem rec_0_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 0) 0 128 = 154557646351575486353926464 := by decide +kernel
private theorem rec_0_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 0) 128 128 = 100732464599411566285179200 := by decide +kernel
private theorem rec_0_2_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 0) 256 128 = 53771506167344656434185249 := by decide +kernel
private theorem rec_0_2_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 0) 384 109 = 13573737864899204210725695 := by decide +kernel
private theorem rec_0_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 0) 0 256 = 255290110950987052639105664 :=
  phaseBlock_append rec_0_2_2369_0_part0 rec_0_2_2369_0_part1 rfl rfl rfl
private theorem rec_0_2_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 0) 256 237 = 67345244032243860644910944 :=
  phaseBlock_append rec_0_2_2369_0_part2 rec_0_2_2369_0_part3 rfl rfl rfl
private theorem rec_0_2_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 0) 0 493 = 322635354983230913284016608 :=
  phaseBlock_append rec_0_2_2369_0_join0 rec_0_2_2369_0_join1 rfl rfl rfl

private theorem rec_0_2_2369_0 : fastPhase (bank 0 2).shape 179798 2369 2 1 0 1 0 = 322635354983230913284016608 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_2_2369_0_join2

private theorem rec_0_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 1) 0 128 = 154115076709703873114674752 := by decide +kernel
private theorem rec_0_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 1) 128 128 = 100343485661199768754394688 := by decide +kernel
private theorem rec_0_2_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 1) 256 128 = 53432570017302922794385602 := by decide +kernel
private theorem rec_0_2_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 1) 384 109 = 13321920199858242142158945 := by decide +kernel
private theorem rec_0_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 1) 0 256 = 254458562370903641869069440 :=
  phaseBlock_append rec_0_2_2369_1_part0 rec_0_2_2369_1_part1 rfl rfl rfl
private theorem rec_0_2_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 1) 256 237 = 66754490217161164936544547 :=
  phaseBlock_append rec_0_2_2369_1_part2 rec_0_2_2369_1_part3 rfl rfl rfl
private theorem rec_0_2_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 2).shape 179798 2369 2 1 0 1 1) 0 493 = 321213052588064806805613987 :=
  phaseBlock_append rec_0_2_2369_1_join0 rec_0_2_2369_1_join1 rfl rfl rfl

private theorem rec_0_2_2369_1 : fastPhase (bank 0 2).shape 179798 2369 2 1 0 1 1 = 321213052588064806805613987 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_2_2369_1_join2

theorem receipt_0_2 : Checked (bank 0 2) 2 0 1 := by
  refine checked_from_values (bank 0 2) 2 0 1
    (P3_7_1.checked (bank 0 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_2_2368_0 rec_0_2_2368_1 rec_0_2_2369_0 rec_0_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 0) 0 128 = 196638935735931071845962816 := by decide +kernel
private theorem rec_0_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 0) 128 128 = 128183263076980704597464128 := by decide +kernel
private theorem rec_0_3_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 0) 256 128 = 68437759432316927452717540 := by decide +kernel
private theorem rec_0_3_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 0) 384 109 = 17278835642400513599064225 := by decide +kernel
private theorem rec_0_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 0) 0 256 = 324822198812911776443426944 :=
  phaseBlock_append rec_0_3_2368_0_part0 rec_0_3_2368_0_part1 rfl rfl rfl
private theorem rec_0_3_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 0) 256 237 = 85716595074717441051781765 :=
  phaseBlock_append rec_0_3_2368_0_part2 rec_0_3_2368_0_part3 rfl rfl rfl
private theorem rec_0_3_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 0) 0 493 = 410538793887629217495208709 :=
  phaseBlock_append rec_0_3_2368_0_join0 rec_0_3_2368_0_join1 rfl rfl rfl

private theorem rec_0_3_2368_0 : fastPhase (bank 0 3).shape 179798 2368 3 1 0 1 0 = 410538793887629217495208709 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_3_2368_0_join2

private theorem rec_0_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 1) 0 128 = 196076158129757156929868160 := by decide +kernel
private theorem rec_0_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 1) 128 128 = 127688470467410017551200640 := by decide +kernel
private theorem rec_0_3_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 1) 256 128 = 68006474993453158409244839 := by decide +kernel
private theorem rec_0_3_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 1) 384 109 = 16958298655867003110423711 := by decide +kernel
private theorem rec_0_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 1) 0 256 = 323764628597167174481068800 :=
  phaseBlock_append rec_0_3_2368_1_part0 rec_0_3_2368_1_part1 rfl rfl rfl
private theorem rec_0_3_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 1) 256 237 = 84964773649320161519668550 :=
  phaseBlock_append rec_0_3_2368_1_part2 rec_0_3_2368_1_part3 rfl rfl rfl
private theorem rec_0_3_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2368 3 1 0 1 1) 0 493 = 408729402246487336000737350 :=
  phaseBlock_append rec_0_3_2368_1_join0 rec_0_3_2368_1_join1 rfl rfl rfl

private theorem rec_0_3_2368_1 : fastPhase (bank 0 3).shape 179798 2368 3 1 0 1 1 = 408729402246487336000737350 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_3_2368_1_join2

private theorem rec_0_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 0) 0 128 = 196640671320854787409337760 := by decide +kernel
private theorem rec_0_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 0) 128 128 = 128184209332997807492222368 := by decide +kernel
private theorem rec_0_3_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 0) 256 128 = 68438157729700729514655211 := by decide +kernel
private theorem rec_0_3_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 0) 384 109 = 17278910475226983952604325 := by decide +kernel
private theorem rec_0_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 0) 0 256 = 324824880653852594901560128 :=
  phaseBlock_append rec_0_3_2369_0_part0 rec_0_3_2369_0_part1 rfl rfl rfl
private theorem rec_0_3_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 0) 256 237 = 85717068204927713467259536 :=
  phaseBlock_append rec_0_3_2369_0_part2 rec_0_3_2369_0_part3 rfl rfl rfl
private theorem rec_0_3_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 0) 0 493 = 410541948858780308368819664 :=
  phaseBlock_append rec_0_3_2369_0_join0 rec_0_3_2369_0_join1 rfl rfl rfl

private theorem rec_0_3_2369_0 : fastPhase (bank 0 3).shape 179798 2369 3 1 0 1 0 = 410541948858780308368819664 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_3_2369_0_join2

private theorem rec_0_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 1) 0 128 = 196077889646019018393263072 := by decide +kernel
private theorem rec_0_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 1) 128 128 = 127689413630509503856249824 := by decide +kernel
private theorem rec_0_3_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 1) 256 128 = 68006871083353933939029044 := by decide +kernel
private theorem rec_0_3_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 1) 384 109 = 16958372238850311379339524 := by decide +kernel
private theorem rec_0_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 1) 0 256 = 323767303276528522249512896 :=
  phaseBlock_append rec_0_3_2369_1_part0 rec_0_3_2369_1_part1 rfl rfl rfl
private theorem rec_0_3_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 1) 256 237 = 84965243322204245318368568 :=
  phaseBlock_append rec_0_3_2369_1_part2 rec_0_3_2369_1_part3 rfl rfl rfl
private theorem rec_0_3_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 3).shape 179798 2369 3 1 0 1 1) 0 493 = 408732546598732767567881464 :=
  phaseBlock_append rec_0_3_2369_1_join0 rec_0_3_2369_1_join1 rfl rfl rfl

private theorem rec_0_3_2369_1 : fastPhase (bank 0 3).shape 179798 2369 3 1 0 1 1 = 408732546598732767567881464 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_3_2369_1_join2

theorem receipt_0_3 : Checked (bank 0 3) 3 0 1 := by
  refine checked_from_values (bank 0 3) 3 0 1
    (P3_7_1.checked (bank 0 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_3_2368_0 rec_0_3_2368_1 rec_0_3_2369_0 rec_0_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 0) 0 128 = 258569838370136749761419072 := by decide +kernel
private theorem rec_0_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 0) 128 128 = 168586140795020658074621760 := by decide +kernel
private theorem rec_0_4_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 0) 256 128 = 90025871631002806076752672 := by decide +kernel
private theorem rec_0_4_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 0) 384 109 = 22733000969043564629753112 := by decide +kernel
private theorem rec_0_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 0) 0 256 = 427155979165157407836040832 :=
  phaseBlock_append rec_0_4_2368_0_part0 rec_0_4_2368_0_part1 rfl rfl rfl
private theorem rec_0_4_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 0) 256 237 = 112758872600046370706505784 :=
  phaseBlock_append rec_0_4_2368_0_part2 rec_0_4_2368_0_part3 rfl rfl rfl
private theorem rec_0_4_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 0) 0 493 = 539914851765203778542546616 :=
  phaseBlock_append rec_0_4_2368_0_join0 rec_0_4_2368_0_join1 rfl rfl rfl

private theorem rec_0_4_2368_0 : fastPhase (bank 0 4).shape 179798 2368 4 1 0 1 0 = 539914851765203778542546616 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_4_2368_0_join2

private theorem rec_0_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 1) 0 128 = 257830198103265268481257088 := by decide +kernel
private theorem rec_0_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 1) 128 128 = 167935638990775280412135040 := by decide +kernel
private theorem rec_0_4_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 1) 256 128 = 89458670118546008020855128 := by decide +kernel
private theorem rec_0_4_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 1) 384 109 = 22311307169443899430743609 := by decide +kernel
private theorem rec_0_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 1) 0 256 = 425765837094040548893392128 :=
  phaseBlock_append rec_0_4_2368_1_part0 rec_0_4_2368_1_part1 rfl rfl rfl
private theorem rec_0_4_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 1) 256 237 = 111769977287989907451598737 :=
  phaseBlock_append rec_0_4_2368_1_part2 rec_0_4_2368_1_part3 rfl rfl rfl
private theorem rec_0_4_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2368 4 1 0 1 1) 0 493 = 537535814382030456344990865 :=
  phaseBlock_append rec_0_4_2368_1_join0 rec_0_4_2368_1_join1 rfl rfl rfl

private theorem rec_0_4_2368_1 : fastPhase (bank 0 4).shape 179798 2368 4 1 0 1 1 = 537535814382030456344990865 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_4_2368_1_join2

private theorem rec_0_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 0) 0 128 = 258572116578696595178439264 := by decide +kernel
private theorem rec_0_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 0) 128 128 = 168587382588504489050755680 := by decide +kernel
private theorem rec_0_4_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 0) 256 128 = 90026394028141491243697224 := by decide +kernel
private theorem rec_0_4_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 0) 384 109 = 22733099022302996093904150 := by decide +kernel
private theorem rec_0_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 0) 0 256 = 427159499167201084229194944 :=
  phaseBlock_append rec_0_4_2369_0_part0 rec_0_4_2369_0_part1 rfl rfl rfl
private theorem rec_0_4_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 0) 256 237 = 112759493050444487337601374 :=
  phaseBlock_append rec_0_4_2369_0_part2 rec_0_4_2369_0_part3 rfl rfl rfl
private theorem rec_0_4_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 0) 0 493 = 539918992217645571566796318 :=
  phaseBlock_append rec_0_4_2369_0_join0 rec_0_4_2369_0_join1 rfl rfl rfl

private theorem rec_0_4_2369_0 : fastPhase (bank 0 4).shape 179798 2369 4 1 0 1 0 = 539918992217645571566796318 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_4_2369_0_join2

private theorem rec_0_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 1) 0 128 = 257832470975527176431463072 := by decide +kernel
private theorem rec_0_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 1) 128 128 = 167936876728075879953316512 := by decide +kernel
private theorem rec_0_4_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 1) 256 128 = 89459189621921308082373099 := by decide +kernel
private theorem rec_0_4_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 1) 384 109 = 22311403585835494593428325 := by decide +kernel
private theorem rec_0_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 1) 0 256 = 425769347703603056384779584 :=
  phaseBlock_append rec_0_4_2369_1_part0 rec_0_4_2369_1_part1 rfl rfl rfl
private theorem rec_0_4_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 1) 256 237 = 111770593207756802675801424 :=
  phaseBlock_append rec_0_4_2369_1_part2 rec_0_4_2369_1_part3 rfl rfl rfl
private theorem rec_0_4_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 4).shape 179798 2369 4 1 0 1 1) 0 493 = 537539940911359859060581008 :=
  phaseBlock_append rec_0_4_2369_1_join0 rec_0_4_2369_1_join1 rfl rfl rfl

private theorem rec_0_4_2369_1 : fastPhase (bank 0 4).shape 179798 2369 4 1 0 1 1 = 537539940911359859060581008 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_4_2369_1_join2

theorem receipt_0_4 : Checked (bank 0 4) 4 0 1 := by
  refine checked_from_values (bank 0 4) 4 0 1
    (P3_7_1.checked (bank 0 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_4_2368_0 rec_0_4_2368_1 rec_0_4_2369_0 rec_0_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 0) 0 128 = 355127184301273548723903488 := by decide +kernel
private theorem rec_0_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 0) 128 128 = 231584830320215340206439424 := by decide +kernel
private theorem rec_0_5_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 0) 256 128 = 123690559100619163059694972 := by decide +kernel
private theorem rec_0_5_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 0) 384 109 = 31238969272829723379405153 := by decide +kernel
private theorem rec_0_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 0) 0 256 = 586712014621488888930342912 :=
  phaseBlock_append rec_0_5_2368_0_part0 rec_0_5_2368_0_part1 rfl rfl rfl
private theorem rec_0_5_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 0) 256 237 = 154929528373448886439100125 :=
  phaseBlock_append rec_0_5_2368_0_part2 rec_0_5_2368_0_part3 rfl rfl rfl
private theorem rec_0_5_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 0) 0 493 = 741641542994937775369443037 :=
  phaseBlock_append rec_0_5_2368_0_join0 rec_0_5_2368_0_join1 rfl rfl rfl

private theorem rec_0_5_2368_0 : fastPhase (bank 0 5).shape 179798 2368 5 1 0 1 0 = 741641542994937775369443037 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_5_2368_0_join2

private theorem rec_0_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 1) 0 128 = 354111866767979890740073152 := by decide +kernel
private theorem rec_0_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 1) 128 128 = 230691583503722749996470976 := by decide +kernel
private theorem rec_0_5_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 1) 256 128 = 122911431377396351396130462 := by decide +kernel
private theorem rec_0_5_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 1) 384 109 = 30659522000526594970817352 := by decide +kernel
private theorem rec_0_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 1) 0 256 = 584803450271702640736544128 :=
  phaseBlock_append rec_0_5_2368_1_part0 rec_0_5_2368_1_part1 rfl rfl rfl
private theorem rec_0_5_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 1) 256 237 = 153570953377922946366947814 :=
  phaseBlock_append rec_0_5_2368_1_part2 rec_0_5_2368_1_part3 rfl rfl rfl
private theorem rec_0_5_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2368 5 1 0 1 1) 0 493 = 738374403649625587103491942 :=
  phaseBlock_append rec_0_5_2368_1_join0 rec_0_5_2368_1_join1 rfl rfl rfl

private theorem rec_0_5_2368_1 : fastPhase (bank 0 5).shape 179798 2368 5 1 0 1 1 = 738374403649625587103491942 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_5_2368_1_join2

private theorem rec_0_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 0) 0 128 = 355130307771726493907735616 := by decide +kernel
private theorem rec_0_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 0) 128 128 = 231586532422423769378174016 := by decide +kernel
private theorem rec_0_5_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 0) 256 128 = 123691274729427809417856792 := by decide +kernel
private theorem rec_0_5_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 0) 384 109 = 31239103463315134084919889 := by decide +kernel
private theorem rec_0_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 0) 0 256 = 586716840194150263285909632 :=
  phaseBlock_append rec_0_5_2369_0_part0 rec_0_5_2369_0_part1 rfl rfl rfl
private theorem rec_0_5_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 0) 256 237 = 154930378192742943502776681 :=
  phaseBlock_append rec_0_5_2369_0_part2 rec_0_5_2369_0_part3 rfl rfl rfl
private theorem rec_0_5_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 0) 0 493 = 741647218386893206788686313 :=
  phaseBlock_append rec_0_5_2369_0_join0 rec_0_5_2369_0_join1 rfl rfl rfl

private theorem rec_0_5_2369_0 : fastPhase (bank 0 5).shape 179798 2369 5 1 0 1 0 = 741647218386893206788686313 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_5_2369_0_join2

private theorem rec_0_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 1) 0 128 = 354114982928316781342813248 := by decide +kernel
private theorem rec_0_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 1) 128 128 = 230693280049937519759141952 := by decide +kernel
private theorem rec_0_5_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 1) 256 128 = 122912143044138931555239379 := by decide +kernel
private theorem rec_0_5_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 1) 384 109 = 30659653951979821793191913 := by decide +kernel
private theorem rec_0_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 1) 0 256 = 584808262978254301101955200 :=
  phaseBlock_append rec_0_5_2369_1_part0 rec_0_5_2369_1_part1 rfl rfl rfl
private theorem rec_0_5_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 1) 256 237 = 153571796996118753348431292 :=
  phaseBlock_append rec_0_5_2369_1_part2 rec_0_5_2369_1_part3 rfl rfl rfl
private theorem rec_0_5_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 5).shape 179798 2369 5 1 0 1 1) 0 493 = 738380059974373054450386492 :=
  phaseBlock_append rec_0_5_2369_1_join0 rec_0_5_2369_1_join1 rfl rfl rfl

private theorem rec_0_5_2369_1 : fastPhase (bank 0 5).shape 179798 2369 5 1 0 1 1 = 738380059974373054450386492 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_0_5_2369_1_join2

theorem receipt_0_5 : Checked (bank 0 5) 5 0 1 := by
  refine checked_from_values (bank 0 5) 5 0 1
    (P3_7_1.checked (bank 0 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_5_2368_0 rec_0_5_2368_1 rec_0_5_2369_0 rec_0_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 0 128 = 860788947193636641930585888 := by decide +kernel
private theorem rec_0_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 128 128 = 645725851286174762489231136 := by decide +kernel
private theorem rec_0_6_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 256 128 = 450444764370905403280608422 := by decide +kernel
private theorem rec_0_6_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 384 128 = 273990732811595962524535014 := by decide +kernel
private theorem rec_0_6_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 512 128 = 115411884085398231162979989 := by decide +kernel
private theorem rec_0_6_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 640 38 = 6254785883660626880056701 := by decide +kernel
private theorem rec_0_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 128 256 = 1096170615657080165769839558 :=
  phaseBlock_append rec_0_6_2368_0_part1 rec_0_6_2368_0_part2 rfl rfl rfl
private theorem rec_0_6_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 0 384 = 1956959562850716807700425446 :=
  phaseBlock_append rec_0_6_2368_0_part0 rec_0_6_2368_0_join0 rfl rfl rfl
private theorem rec_0_6_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 512 166 = 121666669969058858043036690 :=
  phaseBlock_append rec_0_6_2368_0_part4 rec_0_6_2368_0_part5 rfl rfl rfl
private theorem rec_0_6_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 384 294 = 395657402780654820567571704 :=
  phaseBlock_append rec_0_6_2368_0_part3 rec_0_6_2368_0_join2 rfl rfl rfl
private theorem rec_0_6_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 0) 0 678 = 2352616965631371628267997150 :=
  phaseBlock_append rec_0_6_2368_0_join1 rec_0_6_2368_0_join3 rfl rfl rfl

private theorem rec_0_6_2368_0 : fastPhase (bank 0 6).shape 179798 2368 7 1 0 1 0 = 2352616965631371628267997150 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_6_2368_0_join4

private theorem rec_0_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 0 128 = 859052838242362428901554208 := by decide +kernel
private theorem rec_0_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 128 128 = 644142705549577977593940000 := by decide +kernel
private theorem rec_0_6_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 256 128 = 449007342068452021714737534 := by decide +kernel
private theorem rec_0_6_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 384 128 = 272691823962654627274955087 := by decide +kernel
private theorem rec_0_6_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 512 128 = 114244306541420304827433649 := by decide +kernel
private theorem rec_0_6_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 640 38 = 5932388579593059510448389 := by decide +kernel
private theorem rec_0_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 128 256 = 1093150047618029999308677534 :=
  phaseBlock_append rec_0_6_2368_1_part1 rec_0_6_2368_1_part2 rfl rfl rfl
private theorem rec_0_6_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 0 384 = 1952202885860392428210231742 :=
  phaseBlock_append rec_0_6_2368_1_part0 rec_0_6_2368_1_join0 rfl rfl rfl
private theorem rec_0_6_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 512 166 = 120176695121013364337882038 :=
  phaseBlock_append rec_0_6_2368_1_part4 rec_0_6_2368_1_part5 rfl rfl rfl
private theorem rec_0_6_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 384 294 = 392868519083667991612837125 :=
  phaseBlock_append rec_0_6_2368_1_part3 rec_0_6_2368_1_join2 rfl rfl rfl
private theorem rec_0_6_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2368 7 1 0 1 1) 0 678 = 2345071404944060419823068867 :=
  phaseBlock_append rec_0_6_2368_1_join1 rec_0_6_2368_1_join3 rfl rfl rfl

private theorem rec_0_6_2368_1 : fastPhase (bank 0 6).shape 179798 2368 7 1 0 1 1 = 2345071404944060419823068867 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_6_2368_1_join4

private theorem rec_0_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 0 128 = 860796667662701268524473344 := by decide +kernel
private theorem rec_0_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 128 128 = 645730974670232675069844480 := by decide +kernel
private theorem rec_0_6_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 256 128 = 450447843290916082231778094 := by decide +kernel
private theorem rec_0_6_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 384 128 = 273992282935042476656825774 := by decide +kernel
private theorem rec_0_6_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 512 128 = 115412398141347120275884716 := by decide +kernel
private theorem rec_0_6_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 640 38 = 6254807810716150641705360 := by decide +kernel
private theorem rec_0_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 128 256 = 1096178817961148757301622574 :=
  phaseBlock_append rec_0_6_2369_0_part1 rec_0_6_2369_0_part2 rfl rfl rfl
private theorem rec_0_6_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 0 384 = 1956975485623850025826095918 :=
  phaseBlock_append rec_0_6_2369_0_part0 rec_0_6_2369_0_join0 rfl rfl rfl
private theorem rec_0_6_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 512 166 = 121667205952063270917590076 :=
  phaseBlock_append rec_0_6_2369_0_part4 rec_0_6_2369_0_part5 rfl rfl rfl
private theorem rec_0_6_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 384 294 = 395659488887105747574415850 :=
  phaseBlock_append rec_0_6_2369_0_part3 rec_0_6_2369_0_join2 rfl rfl rfl
private theorem rec_0_6_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 0) 0 678 = 2352634974510955773400511768 :=
  phaseBlock_append rec_0_6_2369_0_join1 rec_0_6_2369_0_join3 rfl rfl rfl

private theorem rec_0_6_2369_0 : fastPhase (bank 0 6).shape 179798 2369 7 1 0 1 0 = 2352634974510955773400511768 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_6_2369_0_join4

private theorem rec_0_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 0 128 = 859060545994143042425579072 := by decide +kernel
private theorem rec_0_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 128 128 = 644147818427760110908900928 := by decide +kernel
private theorem rec_0_6_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 256 128 = 449010412539565327080128204 := by decide +kernel
private theorem rec_0_6_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 384 128 = 272693367560529319890118494 := by decide +kernel
private theorem rec_0_6_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 512 128 = 114244815841456271711934546 := by decide +kernel
private theorem rec_0_6_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 640 38 = 5932409411686757253931250 := by decide +kernel
private theorem rec_0_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 128 256 = 1093158230967325437989029132 :=
  phaseBlock_append rec_0_6_2369_1_part1 rec_0_6_2369_1_part2 rfl rfl rfl
private theorem rec_0_6_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 0 384 = 1952218776961468480414608204 :=
  phaseBlock_append rec_0_6_2369_1_part0 rec_0_6_2369_1_join0 rfl rfl rfl
private theorem rec_0_6_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 512 166 = 120177225253143028965865796 :=
  phaseBlock_append rec_0_6_2369_1_part4 rec_0_6_2369_1_part5 rfl rfl rfl
private theorem rec_0_6_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 384 294 = 392870592813672348855984290 :=
  phaseBlock_append rec_0_6_2369_1_part3 rec_0_6_2369_1_join2 rfl rfl rfl
private theorem rec_0_6_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 6).shape 179798 2369 7 1 0 1 1) 0 678 = 2345089369775140829270592494 :=
  phaseBlock_append rec_0_6_2369_1_join1 rec_0_6_2369_1_join3 rfl rfl rfl

private theorem rec_0_6_2369_1 : fastPhase (bank 0 6).shape 179798 2369 7 1 0 1 1 = 2345089369775140829270592494 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_6_2369_1_join4

theorem receipt_0_6 : Checked (bank 0 6) 7 0 1 := by
  refine checked_from_values (bank 0 6) 7 0 1
    (P3_7_1.checked (bank 0 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_6_2368_0 rec_0_6_2368_1 rec_0_6_2369_0 rec_0_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 0 128 = 1559719474219062855129120768 := by decide +kernel
private theorem rec_0_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 128 128 = 1170386127633272549954822144 := by decide +kernel
private theorem rec_0_7_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 256 128 = 816682737269419053028451060 := by decide +kernel
private theorem rec_0_7_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 384 128 = 496909775706065973307277243 := by decide +kernel
private theorem rec_0_7_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 512 128 = 209371103056959534529260561 := by decide +kernel
private theorem rec_0_7_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 640 38 = 11349383703382936134367420 := by decide +kernel
private theorem rec_0_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 128 256 = 1987068864902691602983273204 :=
  phaseBlock_append rec_0_7_2368_0_part1 rec_0_7_2368_0_part2 rfl rfl rfl
private theorem rec_0_7_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 0 384 = 3546788339121754458112393972 :=
  phaseBlock_append rec_0_7_2368_0_part0 rec_0_7_2368_0_join0 rfl rfl rfl
private theorem rec_0_7_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 512 166 = 220720486760342470663627981 :=
  phaseBlock_append rec_0_7_2368_0_part4 rec_0_7_2368_0_part5 rfl rfl rfl
private theorem rec_0_7_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 384 294 = 717630262466408443970905224 :=
  phaseBlock_append rec_0_7_2368_0_part3 rec_0_7_2368_0_join2 rfl rfl rfl
private theorem rec_0_7_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 0) 0 678 = 4264418601588162902083299196 :=
  phaseBlock_append rec_0_7_2368_0_join1 rec_0_7_2368_0_join3 rfl rfl rfl

private theorem rec_0_7_2368_0 : fastPhase (bank 0 7).shape 179798 2368 10 1 0 1 0 = 4264418601588162902083299196 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_7_2368_0_join4

private theorem rec_0_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 0 128 = 1556577384363945707989137792 := by decide +kernel
private theorem rec_0_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 128 128 = 1167519411709310017356061056 := by decide +kernel
private theorem rec_0_7_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 256 128 = 814078519705537217091221660 := by decide +kernel
private theorem rec_0_7_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 384 128 = 494555219192991101598820945 := by decide +kernel
private theorem rec_0_7_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 512 128 = 207253405436747830644367197 := by decide +kernel
private theorem rec_0_7_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 640 38 = 10764407078537845964323827 := by decide +kernel
private theorem rec_0_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 128 256 = 1981597931414847234447282716 :=
  phaseBlock_append rec_0_7_2368_1_part1 rec_0_7_2368_1_part2 rfl rfl rfl
private theorem rec_0_7_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 0 384 = 3538175315778792942436420508 :=
  phaseBlock_append rec_0_7_2368_1_part0 rec_0_7_2368_1_join0 rfl rfl rfl
private theorem rec_0_7_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 512 166 = 218017812515285676608691024 :=
  phaseBlock_append rec_0_7_2368_1_part4 rec_0_7_2368_1_part5 rfl rfl rfl
private theorem rec_0_7_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 384 294 = 712573031708276778207511969 :=
  phaseBlock_append rec_0_7_2368_1_part3 rec_0_7_2368_1_join2 rfl rfl rfl
private theorem rec_0_7_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2368 10 1 0 1 1) 0 678 = 4250748347487069720643932477 :=
  phaseBlock_append rec_0_7_2368_1_join1 rec_0_7_2368_1_join3 rfl rfl rfl

private theorem rec_0_7_2368_1 : fastPhase (bank 0 7).shape 179798 2368 10 1 0 1 1 = 4250748347487069720643932477 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_7_2368_1_join4

private theorem rec_0_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 0 128 = 1559733411153867652560339456 := by decide +kernel
private theorem rec_0_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 128 128 = 1170395373349479568550396416 := by decide +kernel
private theorem rec_0_7_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 256 128 = 816688290221083353847073142 := by decide +kernel
private theorem rec_0_7_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 384 128 = 496912568438846006029279489 := by decide +kernel
private theorem rec_0_7_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 512 128 = 209372027548199706709686902 := by decide +kernel
private theorem rec_0_7_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 640 38 = 11349423045248519070986624 := by decide +kernel
private theorem rec_0_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 128 256 = 1987083663570562922397469558 :=
  phaseBlock_append rec_0_7_2369_0_part1 rec_0_7_2369_0_part2 rfl rfl rfl
private theorem rec_0_7_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 0 384 = 3546817074724430574957809014 :=
  phaseBlock_append rec_0_7_2369_0_part0 rec_0_7_2369_0_join0 rfl rfl rfl
private theorem rec_0_7_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 512 166 = 220721450593448225780673526 :=
  phaseBlock_append rec_0_7_2369_0_part4 rec_0_7_2369_0_part5 rfl rfl rfl
private theorem rec_0_7_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 384 294 = 717634019032294231809953015 :=
  phaseBlock_append rec_0_7_2369_0_part3 rec_0_7_2369_0_join2 rfl rfl rfl
private theorem rec_0_7_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 0) 0 678 = 4264451093756724806767762029 :=
  phaseBlock_append rec_0_7_2369_0_join1 rec_0_7_2369_0_join3 rfl rfl rfl

private theorem rec_0_7_2369_0 : fastPhase (bank 0 7).shape 179798 2369 10 1 0 1 0 = 4264451093756724806767762029 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_7_2369_0_join4

private theorem rec_0_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 0 128 = 1556591298384011593797603648 := by decide +kernel
private theorem rec_0_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 128 128 = 1167528638496797533430198592 := by decide +kernel
private theorem rec_0_7_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 256 128 = 814084057439786147439168126 := by decide +kernel
private theorem rec_0_7_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 384 128 = 494558000181839659185694509 := by decide +kernel
private theorem rec_0_7_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 512 128 = 207254321382300368203922886 := by decide +kernel
private theorem rec_0_7_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 640 38 = 10764444456491157893229723 := by decide +kernel
private theorem rec_0_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 128 256 = 1981612695936583680869366718 :=
  phaseBlock_append rec_0_7_2369_1_part1 rec_0_7_2369_1_part2 rfl rfl rfl
private theorem rec_0_7_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 0 384 = 3538203994320595274666970366 :=
  phaseBlock_append rec_0_7_2369_1_part0 rec_0_7_2369_1_join0 rfl rfl rfl
private theorem rec_0_7_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 512 166 = 218018765838791526097152609 :=
  phaseBlock_append rec_0_7_2369_1_part4 rec_0_7_2369_1_part5 rfl rfl rfl
private theorem rec_0_7_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 384 294 = 712576766020631185282847118 :=
  phaseBlock_append rec_0_7_2369_1_part3 rec_0_7_2369_1_join2 rfl rfl rfl
private theorem rec_0_7_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 7).shape 179798 2369 10 1 0 1 1) 0 678 = 4250780760341226459949817484 :=
  phaseBlock_append rec_0_7_2369_1_join1 rec_0_7_2369_1_join3 rfl rfl rfl

private theorem rec_0_7_2369_1 : fastPhase (bank 0 7).shape 179798 2369 10 1 0 1 1 = 4250780760341226459949817484 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_7_2369_1_join4

theorem receipt_0_7 : Checked (bank 0 7) 10 0 1 := by
  refine checked_from_values (bank 0 7) 10 0 1
    (P3_7_1.checked (bank 0 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_7_2368_0 rec_0_7_2368_1 rec_0_7_2369_0 rec_0_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 0 128 = 6260515926210576704325700832 := by decide +kernel
private theorem rec_0_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 128 128 = 5125074464903635007947611360 := by decide +kernel
private theorem rec_0_8_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 256 128 = 4065528018556390032650267872 := by decide +kernel
private theorem rec_0_8_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 384 128 = 3079255256282511322943514612 := by decide +kernel
private theorem rec_0_8_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 512 128 = 2163645038175639054260773422 := by decide +kernel
private theorem rec_0_8_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 640 128 = 1316089312296537840256971233 := by decide +kernel
private theorem rec_0_8_2368_0_part6 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 768 128 = 533979496878421971880501948 := by decide +kernel
private theorem rec_0_8_2368_0_part7 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 896 29 = 18840827254740629253738018 := by decide +kernel
private theorem rec_0_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 0 256 = 11385590391114211712273312192 :=
  phaseBlock_append rec_0_8_2368_0_part0 rec_0_8_2368_0_part1 rfl rfl rfl
private theorem rec_0_8_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 256 256 = 7144783274838901355593782484 :=
  phaseBlock_append rec_0_8_2368_0_part2 rec_0_8_2368_0_part3 rfl rfl rfl
private theorem rec_0_8_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 0 512 = 18530373665953113067867094676 :=
  phaseBlock_append rec_0_8_2368_0_join0 rec_0_8_2368_0_join1 rfl rfl rfl
private theorem rec_0_8_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 512 256 = 3479734350472176894517744655 :=
  phaseBlock_append rec_0_8_2368_0_part4 rec_0_8_2368_0_part5 rfl rfl rfl
private theorem rec_0_8_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 768 157 = 552820324133162601134239966 :=
  phaseBlock_append rec_0_8_2368_0_part6 rec_0_8_2368_0_part7 rfl rfl rfl
private theorem rec_0_8_2368_0_join5 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 512 413 = 4032554674605339495651984621 :=
  phaseBlock_append rec_0_8_2368_0_join3 rec_0_8_2368_0_join4 rfl rfl rfl
private theorem rec_0_8_2368_0_join6 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 0) 0 925 = 22562928340558452563519079297 :=
  phaseBlock_append rec_0_8_2368_0_join2 rec_0_8_2368_0_join5 rfl rfl rfl

private theorem rec_0_8_2368_0 : fastPhase (bank 0 8).shape 179798 2368 16 1 0 1 0 = 22562928340558452563519079297 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_0_8_2368_0_join6

private theorem rec_0_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 0 128 = 6251467833248611753641652448 := by decide +kernel
private theorem rec_0_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 128 128 = 5116609219475913159435641056 := by decide +kernel
private theorem rec_0_8_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 256 128 = 4057625779555972158066823392 := by decide +kernel
private theorem rec_0_8_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 384 128 = 3071896236850270648041405843 := by decide +kernel
private theorem rec_0_8_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 512 128 = 2156809496070703395897929039 := by decide +kernel
private theorem rec_0_8_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 640 128 = 1309757547122496781347341022 := by decide +kernel
private theorem rec_0_8_2368_1_part6 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 768 128 = 528131861899519091203159804 := by decide +kernel
private theorem rec_0_8_2368_1_part7 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 896 29 = 17581219132858187112187623 := by decide +kernel
private theorem rec_0_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 0 256 = 11368077052724524913077293504 :=
  phaseBlock_append rec_0_8_2368_1_part0 rec_0_8_2368_1_part1 rfl rfl rfl
private theorem rec_0_8_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 256 256 = 7129522016406242806108229235 :=
  phaseBlock_append rec_0_8_2368_1_part2 rec_0_8_2368_1_part3 rfl rfl rfl
private theorem rec_0_8_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 0 512 = 18497599069130767719185522739 :=
  phaseBlock_append rec_0_8_2368_1_join0 rec_0_8_2368_1_join1 rfl rfl rfl
private theorem rec_0_8_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 512 256 = 3466567043193200177245270061 :=
  phaseBlock_append rec_0_8_2368_1_part4 rec_0_8_2368_1_part5 rfl rfl rfl
private theorem rec_0_8_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 768 157 = 545713081032377278315347427 :=
  phaseBlock_append rec_0_8_2368_1_part6 rec_0_8_2368_1_part7 rfl rfl rfl
private theorem rec_0_8_2368_1_join5 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 512 413 = 4012280124225577455560617488 :=
  phaseBlock_append rec_0_8_2368_1_join3 rec_0_8_2368_1_join4 rfl rfl rfl
private theorem rec_0_8_2368_1_join6 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2368 16 1 0 1 1) 0 925 = 22509879193356345174746140227 :=
  phaseBlock_append rec_0_8_2368_1_join2 rec_0_8_2368_1_join5 rfl rfl rfl

private theorem rec_0_8_2368_1 : fastPhase (bank 0 8).shape 179798 2368 16 1 0 1 1 = 22509879193356345174746140227 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_0_8_2368_1_join6

private theorem rec_0_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 0 128 = 6260572540013660543919223392 := by decide +kernel
private theorem rec_0_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 128 128 = 5125116967821968165977342560 := by decide +kernel
private theorem rec_0_8_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 256 128 = 4065558545804825353256833632 := by decide +kernel
private theorem rec_0_8_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 384 128 = 3079275848173894552637516667 := by decide +kernel
private theorem rec_0_8_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 512 128 = 2163657622468999115879627115 := by decide +kernel
private theorem rec_0_8_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 640 128 = 1316095775081601311591728650 := by decide +kernel
private theorem rec_0_8_2369_0_part6 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 768 128 = 533981638993529866607711601 := by decide +kernel
private theorem rec_0_8_2369_0_part7 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 896 29 = 18840889823585416872027417 := by decide +kernel
private theorem rec_0_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 0 256 = 11385689507835628709896565952 :=
  phaseBlock_append rec_0_8_2369_0_part0 rec_0_8_2369_0_part1 rfl rfl rfl
private theorem rec_0_8_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 256 256 = 7144834393978719905894350299 :=
  phaseBlock_append rec_0_8_2369_0_part2 rec_0_8_2369_0_part3 rfl rfl rfl
private theorem rec_0_8_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 0 512 = 18530523901814348615790916251 :=
  phaseBlock_append rec_0_8_2369_0_join0 rec_0_8_2369_0_join1 rfl rfl rfl
private theorem rec_0_8_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 512 256 = 3479753397550600427471355765 :=
  phaseBlock_append rec_0_8_2369_0_part4 rec_0_8_2369_0_part5 rfl rfl rfl
private theorem rec_0_8_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 768 157 = 552822528817115283479739018 :=
  phaseBlock_append rec_0_8_2369_0_part6 rec_0_8_2369_0_part7 rfl rfl rfl
private theorem rec_0_8_2369_0_join5 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 512 413 = 4032575926367715710951094783 :=
  phaseBlock_append rec_0_8_2369_0_join3 rec_0_8_2369_0_join4 rfl rfl rfl
private theorem rec_0_8_2369_0_join6 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 0) 0 925 = 22563099828182064326742011034 :=
  phaseBlock_append rec_0_8_2369_0_join2 rec_0_8_2369_0_join5 rfl rfl rfl

private theorem rec_0_8_2369_0 : fastPhase (bank 0 8).shape 179798 2369 16 1 0 1 0 = 22563099828182064326742011034 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_0_8_2369_0_join6

private theorem rec_0_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 0 128 = 6251524380434876975887722720 := by decide +kernel
private theorem rec_0_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 128 128 = 5116651664254793730765764832 := by decide +kernel
private theorem rec_0_8_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 256 128 = 4057656256714553097840216288 := by decide +kernel
private theorem rec_0_8_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 384 128 = 3071916786284905406687704665 := by decide +kernel
private theorem rec_0_8_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 512 128 = 2156822045198804374738455624 := by decide +kernel
private theorem rec_0_8_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 640 128 = 1309763981613726305986267467 := by decide +kernel
private theorem rec_0_8_2369_1_part6 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 768 128 = 528133982149250544267534720 := by decide +kernel
private theorem rec_0_8_2369_1_part7 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 896 29 = 17581277595415206833167455 := by decide +kernel
private theorem rec_0_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 0 256 = 11368176044689670706653487552 :=
  phaseBlock_append rec_0_8_2369_1_part0 rec_0_8_2369_1_part1 rfl rfl rfl
private theorem rec_0_8_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 256 256 = 7129573042999458504527920953 :=
  phaseBlock_append rec_0_8_2369_1_part2 rec_0_8_2369_1_part3 rfl rfl rfl
private theorem rec_0_8_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 0 512 = 18497749087689129211181408505 :=
  phaseBlock_append rec_0_8_2369_1_join0 rec_0_8_2369_1_join1 rfl rfl rfl
private theorem rec_0_8_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 512 256 = 3466586026812530680724723091 :=
  phaseBlock_append rec_0_8_2369_1_part4 rec_0_8_2369_1_part5 rfl rfl rfl
private theorem rec_0_8_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 768 157 = 545715259744665751100702175 :=
  phaseBlock_append rec_0_8_2369_1_part6 rec_0_8_2369_1_part7 rfl rfl rfl
private theorem rec_0_8_2369_1_join5 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 512 413 = 4012301286557196431825425266 :=
  phaseBlock_append rec_0_8_2369_1_join3 rec_0_8_2369_1_join4 rfl rfl rfl
private theorem rec_0_8_2369_1_join6 :
    phaseBlock (fastLayerG (bank 0 8).shape 179798 2369 16 1 0 1 1) 0 925 = 22510050374246325643006833771 :=
  phaseBlock_append rec_0_8_2369_1_join2 rec_0_8_2369_1_join5 rfl rfl rfl

private theorem rec_0_8_2369_1 : fastPhase (bank 0 8).shape 179798 2369 16 1 0 1 1 = 22510050374246325643006833771 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_0_8_2369_1_join6

theorem receipt_0_8 : Checked (bank 0 8) 16 0 1 := by
  refine checked_from_values (bank 0 8) 16 0 1
    (P3_7_1.checked (bank 0 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_8_2368_0 rec_0_8_2368_1 rec_0_8_2369_0 rec_0_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 0 128 = 1559719474219062855129120768 := by decide +kernel
private theorem rec_0_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 128 128 = 1170386127633272549954822144 := by decide +kernel
private theorem rec_0_9_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 256 128 = 816682737269419053028451060 := by decide +kernel
private theorem rec_0_9_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 384 128 = 496909775706065973307277243 := by decide +kernel
private theorem rec_0_9_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 512 128 = 209371103056959534529260561 := by decide +kernel
private theorem rec_0_9_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 640 38 = 11349383703382936134367420 := by decide +kernel
private theorem rec_0_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 128 256 = 1987068864902691602983273204 :=
  phaseBlock_append rec_0_9_2368_0_part1 rec_0_9_2368_0_part2 rfl rfl rfl
private theorem rec_0_9_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 0 384 = 3546788339121754458112393972 :=
  phaseBlock_append rec_0_9_2368_0_part0 rec_0_9_2368_0_join0 rfl rfl rfl
private theorem rec_0_9_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 512 166 = 220720486760342470663627981 :=
  phaseBlock_append rec_0_9_2368_0_part4 rec_0_9_2368_0_part5 rfl rfl rfl
private theorem rec_0_9_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 384 294 = 717630262466408443970905224 :=
  phaseBlock_append rec_0_9_2368_0_part3 rec_0_9_2368_0_join2 rfl rfl rfl
private theorem rec_0_9_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 0) 0 678 = 4264418601588162902083299196 :=
  phaseBlock_append rec_0_9_2368_0_join1 rec_0_9_2368_0_join3 rfl rfl rfl

private theorem rec_0_9_2368_0 : fastPhase (bank 0 9).shape 179798 2368 10 1 0 1 0 = 4264418601588162902083299196 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_9_2368_0_join4

private theorem rec_0_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 0 128 = 1556577384363945707989137792 := by decide +kernel
private theorem rec_0_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 128 128 = 1167519411709310017356061056 := by decide +kernel
private theorem rec_0_9_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 256 128 = 814078519705537217091221660 := by decide +kernel
private theorem rec_0_9_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 384 128 = 494555219192991101598820945 := by decide +kernel
private theorem rec_0_9_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 512 128 = 207253405436747830644367197 := by decide +kernel
private theorem rec_0_9_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 640 38 = 10764407078537845964323827 := by decide +kernel
private theorem rec_0_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 128 256 = 1981597931414847234447282716 :=
  phaseBlock_append rec_0_9_2368_1_part1 rec_0_9_2368_1_part2 rfl rfl rfl
private theorem rec_0_9_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 0 384 = 3538175315778792942436420508 :=
  phaseBlock_append rec_0_9_2368_1_part0 rec_0_9_2368_1_join0 rfl rfl rfl
private theorem rec_0_9_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 512 166 = 218017812515285676608691024 :=
  phaseBlock_append rec_0_9_2368_1_part4 rec_0_9_2368_1_part5 rfl rfl rfl
private theorem rec_0_9_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 384 294 = 712573031708276778207511969 :=
  phaseBlock_append rec_0_9_2368_1_part3 rec_0_9_2368_1_join2 rfl rfl rfl
private theorem rec_0_9_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2368 10 1 0 1 1) 0 678 = 4250748347487069720643932477 :=
  phaseBlock_append rec_0_9_2368_1_join1 rec_0_9_2368_1_join3 rfl rfl rfl

private theorem rec_0_9_2368_1 : fastPhase (bank 0 9).shape 179798 2368 10 1 0 1 1 = 4250748347487069720643932477 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_9_2368_1_join4

private theorem rec_0_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 0 128 = 1559733411153867652560339456 := by decide +kernel
private theorem rec_0_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 128 128 = 1170395373349479568550396416 := by decide +kernel
private theorem rec_0_9_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 256 128 = 816688290221083353847073142 := by decide +kernel
private theorem rec_0_9_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 384 128 = 496912568438846006029279489 := by decide +kernel
private theorem rec_0_9_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 512 128 = 209372027548199706709686902 := by decide +kernel
private theorem rec_0_9_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 640 38 = 11349423045248519070986624 := by decide +kernel
private theorem rec_0_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 128 256 = 1987083663570562922397469558 :=
  phaseBlock_append rec_0_9_2369_0_part1 rec_0_9_2369_0_part2 rfl rfl rfl
private theorem rec_0_9_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 0 384 = 3546817074724430574957809014 :=
  phaseBlock_append rec_0_9_2369_0_part0 rec_0_9_2369_0_join0 rfl rfl rfl
private theorem rec_0_9_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 512 166 = 220721450593448225780673526 :=
  phaseBlock_append rec_0_9_2369_0_part4 rec_0_9_2369_0_part5 rfl rfl rfl
private theorem rec_0_9_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 384 294 = 717634019032294231809953015 :=
  phaseBlock_append rec_0_9_2369_0_part3 rec_0_9_2369_0_join2 rfl rfl rfl
private theorem rec_0_9_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 0) 0 678 = 4264451093756724806767762029 :=
  phaseBlock_append rec_0_9_2369_0_join1 rec_0_9_2369_0_join3 rfl rfl rfl

private theorem rec_0_9_2369_0 : fastPhase (bank 0 9).shape 179798 2369 10 1 0 1 0 = 4264451093756724806767762029 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_9_2369_0_join4

private theorem rec_0_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 0 128 = 1556591298384011593797603648 := by decide +kernel
private theorem rec_0_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 128 128 = 1167528638496797533430198592 := by decide +kernel
private theorem rec_0_9_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 256 128 = 814084057439786147439168126 := by decide +kernel
private theorem rec_0_9_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 384 128 = 494558000181839659185694509 := by decide +kernel
private theorem rec_0_9_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 512 128 = 207254321382300368203922886 := by decide +kernel
private theorem rec_0_9_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 640 38 = 10764444456491157893229723 := by decide +kernel
private theorem rec_0_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 128 256 = 1981612695936583680869366718 :=
  phaseBlock_append rec_0_9_2369_1_part1 rec_0_9_2369_1_part2 rfl rfl rfl
private theorem rec_0_9_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 0 384 = 3538203994320595274666970366 :=
  phaseBlock_append rec_0_9_2369_1_part0 rec_0_9_2369_1_join0 rfl rfl rfl
private theorem rec_0_9_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 512 166 = 218018765838791526097152609 :=
  phaseBlock_append rec_0_9_2369_1_part4 rec_0_9_2369_1_part5 rfl rfl rfl
private theorem rec_0_9_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 384 294 = 712576766020631185282847118 :=
  phaseBlock_append rec_0_9_2369_1_part3 rec_0_9_2369_1_join2 rfl rfl rfl
private theorem rec_0_9_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 9).shape 179798 2369 10 1 0 1 1) 0 678 = 4250780760341226459949817484 :=
  phaseBlock_append rec_0_9_2369_1_join1 rec_0_9_2369_1_join3 rfl rfl rfl

private theorem rec_0_9_2369_1 : fastPhase (bank 0 9).shape 179798 2369 10 1 0 1 1 = 4250780760341226459949817484 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_0_9_2369_1_join4

theorem receipt_0_9 : Checked (bank 0 9) 10 0 1 := by
  refine checked_from_values (bank 0 9) 10 0 1
    (P3_7_1.checked (bank 0 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_9_2368_0 rec_0_9_2368_1 rec_0_9_2369_0 rec_0_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 0 128 = 13036630623392464610010058752 := by decide +kernel
private theorem rec_0_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 128 128 = 10674552963277565611730923520 := by decide +kernel
private theorem rec_0_10_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 256 128 = 8469557114732463429481664512 := by decide +kernel
private theorem rec_0_10_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 384 128 = 6416283417533084115636332171 := by decide +kernel
private theorem rec_0_10_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 512 128 = 4509389063930314103377447080 := by decide +kernel
private theorem rec_0_10_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 640 128 = 2743532149371678871980119068 := by decide +kernel
private theorem rec_0_10_2368_0_part6 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 768 128 = 1113365519058996734357871528 := by decide +kernel
private theorem rec_0_10_2368_0_part7 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 896 29 = 39289713944943736172526887 := by decide +kernel
private theorem rec_0_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 0 256 = 23711183586670030221740982272 :=
  phaseBlock_append rec_0_10_2368_0_part0 rec_0_10_2368_0_part1 rfl rfl rfl
private theorem rec_0_10_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 256 256 = 14885840532265547545117996683 :=
  phaseBlock_append rec_0_10_2368_0_part2 rec_0_10_2368_0_part3 rfl rfl rfl
private theorem rec_0_10_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 0 512 = 38597024118935577766858978955 :=
  phaseBlock_append rec_0_10_2368_0_join0 rec_0_10_2368_0_join1 rfl rfl rfl
private theorem rec_0_10_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 512 256 = 7252921213301992975357566148 :=
  phaseBlock_append rec_0_10_2368_0_part4 rec_0_10_2368_0_part5 rfl rfl rfl
private theorem rec_0_10_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 768 157 = 1152655233003940470530398415 :=
  phaseBlock_append rec_0_10_2368_0_part6 rec_0_10_2368_0_part7 rfl rfl rfl
private theorem rec_0_10_2368_0_join5 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 512 413 = 8405576446305933445887964563 :=
  phaseBlock_append rec_0_10_2368_0_join3 rec_0_10_2368_0_join4 rfl rfl rfl
private theorem rec_0_10_2368_0_join6 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 0) 0 925 = 47002600565241511212746943518 :=
  phaseBlock_append rec_0_10_2368_0_join2 rec_0_10_2368_0_join5 rfl rfl rfl

private theorem rec_0_10_2368_0 : fastPhase (bank 0 10).shape 179798 2368 20 1 0 1 0 = 47002600565241511212746943518 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_0_10_2368_0_join6

private theorem rec_0_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 0 128 = 13017811363600214899702958528 := by decide +kernel
private theorem rec_0_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 128 128 = 10656939558921350027155589568 := by decide +kernel
private theorem rec_0_10_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 256 128 = 8453109021801160021944994240 := by decide +kernel
private theorem rec_0_10_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 384 128 = 6400960169642374743723912463 := by decide +kernel
private theorem rec_0_10_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 512 128 = 4495150251451212394140423592 := by decide +kernel
private theorem rec_0_10_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 640 128 = 2730337415541482877185813316 := by decide +kernel
private theorem rec_0_10_2368_1_part6 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 768 128 = 1101174584001609259064331101 := by decide +kernel
private theorem rec_0_10_2368_1_part7 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 896 29 = 36663032248926729510944709 := by decide +kernel
private theorem rec_0_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 0 256 = 23674750922521564926858548096 :=
  phaseBlock_append rec_0_10_2368_1_part0 rec_0_10_2368_1_part1 rfl rfl rfl
private theorem rec_0_10_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 256 256 = 14854069191443534765668906703 :=
  phaseBlock_append rec_0_10_2368_1_part2 rec_0_10_2368_1_part3 rfl rfl rfl
private theorem rec_0_10_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 0 512 = 38528820113965099692527454799 :=
  phaseBlock_append rec_0_10_2368_1_join0 rec_0_10_2368_1_join1 rfl rfl rfl
private theorem rec_0_10_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 512 256 = 7225487666992695271326236908 :=
  phaseBlock_append rec_0_10_2368_1_part4 rec_0_10_2368_1_part5 rfl rfl rfl
private theorem rec_0_10_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 768 157 = 1137837616250535988575275810 :=
  phaseBlock_append rec_0_10_2368_1_part6 rec_0_10_2368_1_part7 rfl rfl rfl
private theorem rec_0_10_2368_1_join5 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 512 413 = 8363325283243231259901512718 :=
  phaseBlock_append rec_0_10_2368_1_join3 rec_0_10_2368_1_join4 rfl rfl rfl
private theorem rec_0_10_2368_1_join6 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2368 20 1 0 1 1) 0 925 = 46892145397208330952428967517 :=
  phaseBlock_append rec_0_10_2368_1_join2 rec_0_10_2368_1_join5 rfl rfl rfl

private theorem rec_0_10_2368_1 : fastPhase (bank 0 10).shape 179798 2368 20 1 0 1 1 = 46892145397208330952428967517 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_0_10_2368_1_join6

private theorem rec_0_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 0 128 = 13036748087846610987377402304 := by decide +kernel
private theorem rec_0_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 128 128 = 10674641132110215457822196160 := by decide +kernel
private theorem rec_0_10_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 256 128 = 8469620421346062240807182784 := by decide +kernel
private theorem rec_0_10_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 384 128 = 6416326099014493402667074820 := by decide +kernel
private theorem rec_0_10_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 512 128 = 4509415127407588055287091707 := by decide +kernel
private theorem rec_0_10_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 640 128 = 2743545519955442035817151957 := by decide +kernel
private theorem rec_0_10_2369_0_part6 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 768 128 = 1113369943092653301357538683 := by decide +kernel
private theorem rec_0_10_2369_0_part7 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 896 29 = 39289842905596587762782114 := by decide +kernel
private theorem rec_0_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 0 256 = 23711389219956826445199598464 :=
  phaseBlock_append rec_0_10_2369_0_part0 rec_0_10_2369_0_part1 rfl rfl rfl
private theorem rec_0_10_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 256 256 = 14885946520360555643474257604 :=
  phaseBlock_append rec_0_10_2369_0_part2 rec_0_10_2369_0_part3 rfl rfl rfl
private theorem rec_0_10_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 0 512 = 38597335740317382088673856068 :=
  phaseBlock_append rec_0_10_2369_0_join0 rec_0_10_2369_0_join1 rfl rfl rfl
private theorem rec_0_10_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 512 256 = 7252960647363030091104243664 :=
  phaseBlock_append rec_0_10_2369_0_part4 rec_0_10_2369_0_part5 rfl rfl rfl
private theorem rec_0_10_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 768 157 = 1152659785998249889120320797 :=
  phaseBlock_append rec_0_10_2369_0_part6 rec_0_10_2369_0_part7 rfl rfl rfl
private theorem rec_0_10_2369_0_join5 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 512 413 = 8405620433361279980224564461 :=
  phaseBlock_append rec_0_10_2369_0_join3 rec_0_10_2369_0_join4 rfl rfl rfl
private theorem rec_0_10_2369_0_join6 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 0) 0 925 = 47002956173678662068898420529 :=
  phaseBlock_append rec_0_10_2369_0_join2 rec_0_10_2369_0_join5 rfl rfl rfl

private theorem rec_0_10_2369_0 : fastPhase (bank 0 10).shape 179798 2369 20 1 0 1 0 = 47002956173678662068898420529 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_0_10_2369_0_join6

private theorem rec_0_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 0 128 = 13017928690090216574721352512 := by decide +kernel
private theorem rec_0_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 128 128 = 10657027607349385663610102592 := by decide +kernel
private theorem rec_0_10_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 256 128 = 8453172224693738310748726080 := by decide +kernel
private theorem rec_0_10_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 384 128 = 6401002763236357317923587706 := by decide +kernel
private theorem rec_0_10_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 512 128 = 4495176242177130562199923545 := by decide +kernel
private theorem rec_0_10_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 640 128 = 2730350727640793419624250989 := by decide +kernel
private theorem rec_0_10_2369_1_part6 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 768 128 = 1101178962909651655214176093 := by decide +kernel
private theorem rec_0_10_2369_1_part7 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 896 29 = 36663152747692474990703496 := by decide +kernel
private theorem rec_0_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 0 256 = 23674956297439602238331455104 :=
  phaseBlock_append rec_0_10_2369_1_part0 rec_0_10_2369_1_part1 rfl rfl rfl
private theorem rec_0_10_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 256 256 = 14854174987930095628672313786 :=
  phaseBlock_append rec_0_10_2369_1_part2 rec_0_10_2369_1_part3 rfl rfl rfl
private theorem rec_0_10_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 0 512 = 38529131285369697867003768890 :=
  phaseBlock_append rec_0_10_2369_1_join0 rec_0_10_2369_1_join1 rfl rfl rfl
private theorem rec_0_10_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 512 256 = 7225526969817923981824174534 :=
  phaseBlock_append rec_0_10_2369_1_part4 rec_0_10_2369_1_part5 rfl rfl rfl
private theorem rec_0_10_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 768 157 = 1137842115657344130204879589 :=
  phaseBlock_append rec_0_10_2369_1_part6 rec_0_10_2369_1_part7 rfl rfl rfl
private theorem rec_0_10_2369_1_join5 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 512 413 = 8363369085475268112029054123 :=
  phaseBlock_append rec_0_10_2369_1_join3 rec_0_10_2369_1_join4 rfl rfl rfl
private theorem rec_0_10_2369_1_join6 :
    phaseBlock (fastLayerG (bank 0 10).shape 179798 2369 20 1 0 1 1) 0 925 = 46892500370844965979032823013 :=
  phaseBlock_append rec_0_10_2369_1_join2 rec_0_10_2369_1_join5 rfl rfl rfl

private theorem rec_0_10_2369_1 : fastPhase (bank 0 10).shape 179798 2369 20 1 0 1 1 = 46892500370844965979032823013 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_0_10_2369_1_join6

theorem receipt_0_10 : Checked (bank 0 10) 20 0 1 := by
  refine checked_from_values (bank 0 10) 20 0 1
    (P3_7_1.checked (bank 0 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_10_2368_0 rec_0_10_2368_1 rec_0_10_2369_0 rec_0_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 0 128 = 67947988781954676663974458592 := by decide +kernel
private theorem rec_0_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 128 128 = 59209500102566124683595007200 := by decide +kernel
private theorem rec_0_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 256 128 = 50884388913198582077757068512 := by decide +kernel
private theorem rec_0_11_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 384 128 = 42962705093730905871956141280 := by decide +kernel
private theorem rec_0_11_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 512 128 = 35434512510263969541791331552 := by decide +kernel
private theorem rec_0_11_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 640 128 = 28289896313030813679208166375 := by decide +kernel
private theorem rec_0_11_2368_0_part6 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 768 128 = 21518971162656511773037997737 := by decide +kernel
private theorem rec_0_11_2368_0_part7 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 896 128 = 15111820722100334082314725779 := by decide +kernel
private theorem rec_0_11_2368_0_part8 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 1024 128 = 9058530045319621234518910161 := by decide +kernel
private theorem rec_0_11_2368_0_part9 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 1152 128 = 3349198164941164595262081371 := by decide +kernel
private theorem rec_0_11_2368_0_part10 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 1280 14 = 34284016590330468646319230 := by decide +kernel
private theorem rec_0_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 0 256 = 127157488884520801347569465792 :=
  phaseBlock_append rec_0_11_2368_0_part0 rec_0_11_2368_0_part1 rfl rfl rfl
private theorem rec_0_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 384 256 = 78397217603994875413747472832 :=
  phaseBlock_append rec_0_11_2368_0_part3 rec_0_11_2368_0_part4 rfl rfl rfl
private theorem rec_0_11_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 256 384 = 129281606517193457491504541344 :=
  phaseBlock_append rec_0_11_2368_0_part2 rec_0_11_2368_0_join1 rfl rfl rfl
private theorem rec_0_11_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 0 640 = 256439095401714258839074007136 :=
  phaseBlock_append rec_0_11_2368_0_join0 rec_0_11_2368_0_join2 rfl rfl rfl
private theorem rec_0_11_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 768 256 = 36630791884756845855352723516 :=
  phaseBlock_append rec_0_11_2368_0_part6 rec_0_11_2368_0_part7 rfl rfl rfl
private theorem rec_0_11_2368_0_join5 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 640 384 = 64920688197787659534560889891 :=
  phaseBlock_append rec_0_11_2368_0_part5 rec_0_11_2368_0_join4 rfl rfl rfl
private theorem rec_0_11_2368_0_join6 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 1152 142 = 3383482181531495063908400601 :=
  phaseBlock_append rec_0_11_2368_0_part9 rec_0_11_2368_0_part10 rfl rfl rfl
private theorem rec_0_11_2368_0_join7 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 1024 270 = 12442012226851116298427310762 :=
  phaseBlock_append rec_0_11_2368_0_part8 rec_0_11_2368_0_join6 rfl rfl rfl
private theorem rec_0_11_2368_0_join8 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 640 654 = 77362700424638775832988200653 :=
  phaseBlock_append rec_0_11_2368_0_join5 rec_0_11_2368_0_join7 rfl rfl rfl
private theorem rec_0_11_2368_0_join9 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 0) 0 1294 = 333801795826353034672062207789 :=
  phaseBlock_append rec_0_11_2368_0_join3 rec_0_11_2368_0_join8 rfl rfl rfl

private theorem rec_0_11_2368_0 : fastPhase (bank 0 11).shape 179798 2368 32 1 0 1 0 = 333801795826353034672062207789 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_0_11_2368_0_join9

private theorem rec_0_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 0 128 = 67879046345641305722315998688 := by decide +kernel
private theorem rec_0_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 128 128 = 59143715482414462878239626720 := by decide +kernel
private theorem rec_0_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 256 128 = 50821686861311054294566315488 := by decide +kernel
private theorem rec_0_11_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 384 128 = 42903010468794886585267074528 := by decide +kernel
private theorem rec_0_11_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 512 128 = 35377750277503656022237660640 := by decide +kernel
private theorem rec_0_11_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 640 128 = 28235991531001153704052920252 := by decide +kernel
private theorem rec_0_11_2368_1_part6 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 768 128 = 21467848935843940633813612915 := by decide +kernel
private theorem rec_0_11_2368_1_part7 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 896 128 = 15063406244730183292051662822 := by decide +kernel
private theorem rec_0_11_2368_1_part8 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 1024 128 = 9012748618117934956390334145 := by decide +kernel
private theorem rec_0_11_2368_1_part9 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 1152 128 = 3305975195136735967593328364 := by decide +kernel
private theorem rec_0_11_2368_1_part10 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 1280 14 = 29708544756139147568905348 := by decide +kernel
private theorem rec_0_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 0 256 = 127022761828055768600555625408 :=
  phaseBlock_append rec_0_11_2368_1_part0 rec_0_11_2368_1_part1 rfl rfl rfl
private theorem rec_0_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 384 256 = 78280760746298542607504735168 :=
  phaseBlock_append rec_0_11_2368_1_part3 rec_0_11_2368_1_part4 rfl rfl rfl
private theorem rec_0_11_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 256 384 = 129102447607609596902071050656 :=
  phaseBlock_append rec_0_11_2368_1_part2 rec_0_11_2368_1_join1 rfl rfl rfl
private theorem rec_0_11_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 0 640 = 256125209435665365502626676064 :=
  phaseBlock_append rec_0_11_2368_1_join0 rec_0_11_2368_1_join2 rfl rfl rfl
private theorem rec_0_11_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 768 256 = 36531255180574123925865275737 :=
  phaseBlock_append rec_0_11_2368_1_part6 rec_0_11_2368_1_part7 rfl rfl rfl
private theorem rec_0_11_2368_1_join5 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 640 384 = 64767246711575277629918195989 :=
  phaseBlock_append rec_0_11_2368_1_part5 rec_0_11_2368_1_join4 rfl rfl rfl
private theorem rec_0_11_2368_1_join6 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 1152 142 = 3335683739892875115162233712 :=
  phaseBlock_append rec_0_11_2368_1_part9 rec_0_11_2368_1_part10 rfl rfl rfl
private theorem rec_0_11_2368_1_join7 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 1024 270 = 12348432358010810071552567857 :=
  phaseBlock_append rec_0_11_2368_1_part8 rec_0_11_2368_1_join6 rfl rfl rfl
private theorem rec_0_11_2368_1_join8 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 640 654 = 77115679069586087701470763846 :=
  phaseBlock_append rec_0_11_2368_1_join5 rec_0_11_2368_1_join7 rfl rfl rfl
private theorem rec_0_11_2368_1_join9 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2368 32 1 0 1 1) 0 1294 = 333240888505251453204097439910 :=
  phaseBlock_append rec_0_11_2368_1_join3 rec_0_11_2368_1_join8 rfl rfl rfl

private theorem rec_0_11_2368_1 : fastPhase (bank 0 11).shape 179798 2368 32 1 0 1 1 = 333240888505251453204097439910 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_0_11_2368_1_join9

private theorem rec_0_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 0 128 = 67948606054385775782194795776 := by decide +kernel
private theorem rec_0_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 128 128 = 59210006587004849218285344000 := by decide +kernel
private theorem rec_0_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 256 128 = 50884796307799695528645678336 := by decide +kernel
private theorem rec_0_11_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 384 128 = 42963024751421289354144748800 := by decide +kernel
private theorem rec_0_11_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 512 128 = 35434755439230921393640985856 := by decide +kernel
private theorem rec_0_11_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 640 128 = 28290073012260077069157710265 := by decide +kernel
private theorem rec_0_11_2369_0_part6 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 768 128 = 21519091875260800730130032931 := by decide +kernel
private theorem rec_0_11_2369_0_part7 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 896 128 = 15111895608020824914564037551 := by decide +kernel
private theorem rec_0_11_2369_0_part8 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 1024 128 = 9058568886357430446988776426 := by decide +kernel
private theorem rec_0_11_2369_0_part9 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 1152 128 = 3349210371051933559942101399 := by decide +kernel
private theorem rec_0_11_2369_0_part10 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 1280 14 = 34284124878598006716343323 := by decide +kernel
private theorem rec_0_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 0 256 = 127158612641390625000480139776 :=
  phaseBlock_append rec_0_11_2369_0_part0 rec_0_11_2369_0_part1 rfl rfl rfl
private theorem rec_0_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 384 256 = 78397780190652210747785734656 :=
  phaseBlock_append rec_0_11_2369_0_part3 rec_0_11_2369_0_part4 rfl rfl rfl
private theorem rec_0_11_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 256 384 = 129282576498451906276431412992 :=
  phaseBlock_append rec_0_11_2369_0_part2 rec_0_11_2369_0_join1 rfl rfl rfl
private theorem rec_0_11_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 0 640 = 256441189139842531276911552768 :=
  phaseBlock_append rec_0_11_2369_0_join0 rec_0_11_2369_0_join2 rfl rfl rfl
private theorem rec_0_11_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 768 256 = 36630987483281625644694070482 :=
  phaseBlock_append rec_0_11_2369_0_part6 rec_0_11_2369_0_part7 rfl rfl rfl
private theorem rec_0_11_2369_0_join5 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 640 384 = 64921060495541702713851780747 :=
  phaseBlock_append rec_0_11_2369_0_part5 rec_0_11_2369_0_join4 rfl rfl rfl
private theorem rec_0_11_2369_0_join6 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 1152 142 = 3383494495930531566658444722 :=
  phaseBlock_append rec_0_11_2369_0_part9 rec_0_11_2369_0_part10 rfl rfl rfl
private theorem rec_0_11_2369_0_join7 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 1024 270 = 12442063382287962013647221148 :=
  phaseBlock_append rec_0_11_2369_0_part8 rec_0_11_2369_0_join6 rfl rfl rfl
private theorem rec_0_11_2369_0_join8 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 640 654 = 77363123877829664727499001895 :=
  phaseBlock_append rec_0_11_2369_0_join5 rec_0_11_2369_0_join7 rfl rfl rfl
private theorem rec_0_11_2369_0_join9 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 0) 0 1294 = 333804313017672196004410554663 :=
  phaseBlock_append rec_0_11_2369_0_join3 rec_0_11_2369_0_join8 rfl rfl rfl

private theorem rec_0_11_2369_0 : fastPhase (bank 0 11).shape 179798 2369 32 1 0 1 0 = 333804313017672196004410554663 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_0_11_2369_0_join9

private theorem rec_0_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 0 128 = 67879663109515063208702440704 := by decide +kernel
private theorem rec_0_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 128 128 = 59144221504449460156663706880 := by decide +kernel
private theorem rec_0_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 256 128 = 50822093838036396187994191104 := by decide +kernel
private theorem rec_0_11_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 384 128 = 42903329751514468163485119744 := by decide +kernel
private theorem rec_0_11_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 512 128 = 35377992872784460904068281600 := by decide +kernel
private theorem rec_0_11_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 640 128 = 28236167936502641037027541032 := by decide +kernel
private theorem rec_0_11_2369_1_part6 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 768 128 = 21467969393375006251641506209 := by decide +kernel
private theorem rec_0_11_2369_1_part7 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 896 128 = 15063480912533286609559058544 := by decide +kernel
private theorem rec_0_11_2369_1_part8 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 1024 128 = 9012787276307136777626711130 := by decide +kernel
private theorem rec_0_11_2369_1_part9 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 1152 128 = 3305987251986816909211833312 := by decide +kernel
private theorem rec_0_11_2369_1_part10 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 1280 14 = 29708638685946996515973642 := by decide +kernel
private theorem rec_0_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 0 256 = 127023884613964523365366147584 :=
  phaseBlock_append rec_0_11_2369_1_part0 rec_0_11_2369_1_part1 rfl rfl rfl
private theorem rec_0_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 384 256 = 78281322624298929067553401344 :=
  phaseBlock_append rec_0_11_2369_1_part3 rec_0_11_2369_1_part4 rfl rfl rfl
private theorem rec_0_11_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 256 384 = 129103416462335325255547592448 :=
  phaseBlock_append rec_0_11_2369_1_part2 rec_0_11_2369_1_join1 rfl rfl rfl
private theorem rec_0_11_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 0 640 = 256127301076299848620913740032 :=
  phaseBlock_append rec_0_11_2369_1_join0 rec_0_11_2369_1_join2 rfl rfl rfl
private theorem rec_0_11_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 768 256 = 36531450305908292861200564753 :=
  phaseBlock_append rec_0_11_2369_1_part6 rec_0_11_2369_1_part7 rfl rfl rfl
private theorem rec_0_11_2369_1_join5 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 640 384 = 64767618242410933898228105785 :=
  phaseBlock_append rec_0_11_2369_1_part5 rec_0_11_2369_1_join4 rfl rfl rfl
private theorem rec_0_11_2369_1_join6 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 1152 142 = 3335695890672763905727806954 :=
  phaseBlock_append rec_0_11_2369_1_part9 rec_0_11_2369_1_part10 rfl rfl rfl
private theorem rec_0_11_2369_1_join7 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 1024 270 = 12348483166979900683354518084 :=
  phaseBlock_append rec_0_11_2369_1_part8 rec_0_11_2369_1_join6 rfl rfl rfl
private theorem rec_0_11_2369_1_join8 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 640 654 = 77116101409390834581582623869 :=
  phaseBlock_append rec_0_11_2369_1_join5 rec_0_11_2369_1_join7 rfl rfl rfl
private theorem rec_0_11_2369_1_join9 :
    phaseBlock (fastLayerG (bank 0 11).shape 179798 2369 32 1 0 1 1) 0 1294 = 333243402485690683202496363901 :=
  phaseBlock_append rec_0_11_2369_1_join3 rec_0_11_2369_1_join8 rfl rfl rfl

private theorem rec_0_11_2369_1 : fastPhase (bank 0 11).shape 179798 2369 32 1 0 1 1 = 333243402485690683202496363901 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_0_11_2369_1_join9

theorem receipt_0_11 : Checked (bank 0 11) 32 0 1 := by
  refine checked_from_values (bank 0 11) 32 0 1
    (P3_7_1.checked (bank 0 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_11_2368_0 rec_0_11_2368_1 rec_0_11_2369_0 rec_0_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 0 128 = 58588827783449523458885892416 := by decide +kernel
private theorem rec_0_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 128 128 = 51052563841924826292667316544 := by decide +kernel
private theorem rec_0_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 256 128 = 43873136876426656357183895872 := by decide +kernel
private theorem rec_0_12_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 384 128 = 37041938435927599886998632768 := by decide +kernel
private theorem rec_0_12_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 512 128 = 30550373067530197982270077248 := by decide +kernel
private theorem rec_0_12_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 640 128 = 24389864451670368203353345142 := by decide +kernel
private theorem rec_0_12_2368_0_part6 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 768 128 = 18551862865677004170035844067 := by decide +kernel
private theorem rec_0_12_2368_0_part7 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 896 128 = 13027792992396161948460851172 := by decide +kernel
private theorem rec_0_12_2368_0_part8 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 1024 128 = 7809081394373471197718974635 := by decide +kernel
private theorem rec_0_12_2368_0_part9 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 1152 128 = 2887167629927811808101954545 := by decide +kernel
private theorem rec_0_12_2368_0_part10 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 1280 14 = 29553892685099039869231807 := by decide +kernel
private theorem rec_0_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 0 256 = 109641391625374349751553208960 :=
  phaseBlock_append rec_0_12_2368_0_part0 rec_0_12_2368_0_part1 rfl rfl rfl
private theorem rec_0_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 384 256 = 67592311503457797869268710016 :=
  phaseBlock_append rec_0_12_2368_0_part3 rec_0_12_2368_0_part4 rfl rfl rfl
private theorem rec_0_12_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 256 384 = 111465448379884454226452605888 :=
  phaseBlock_append rec_0_12_2368_0_part2 rec_0_12_2368_0_join1 rfl rfl rfl
private theorem rec_0_12_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 0 640 = 221106840005258803978005814848 :=
  phaseBlock_append rec_0_12_2368_0_join0 rec_0_12_2368_0_join2 rfl rfl rfl
private theorem rec_0_12_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 768 256 = 31579655858073166118496695239 :=
  phaseBlock_append rec_0_12_2368_0_part6 rec_0_12_2368_0_part7 rfl rfl rfl
private theorem rec_0_12_2368_0_join5 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 640 384 = 55969520309743534321850040381 :=
  phaseBlock_append rec_0_12_2368_0_part5 rec_0_12_2368_0_join4 rfl rfl rfl
private theorem rec_0_12_2368_0_join6 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 1152 142 = 2916721522612910847971186352 :=
  phaseBlock_append rec_0_12_2368_0_part9 rec_0_12_2368_0_part10 rfl rfl rfl
private theorem rec_0_12_2368_0_join7 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 1024 270 = 10725802916986382045690160987 :=
  phaseBlock_append rec_0_12_2368_0_part8 rec_0_12_2368_0_join6 rfl rfl rfl
private theorem rec_0_12_2368_0_join8 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 640 654 = 66695323226729916367540201368 :=
  phaseBlock_append rec_0_12_2368_0_join5 rec_0_12_2368_0_join7 rfl rfl rfl
private theorem rec_0_12_2368_0_join9 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 0) 0 1294 = 287802163231988720345546016216 :=
  phaseBlock_append rec_0_12_2368_0_join3 rec_0_12_2368_0_join8 rfl rfl rfl

private theorem rec_0_12_2368_0 : fastPhase (bank 0 12).shape 179798 2368 31 1 0 1 0 = 287802163231988720345546016216 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_0_12_2368_0_join9

private theorem rec_0_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 0 128 = 58529368795146832087966590272 := by decide +kernel
private theorem rec_0_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 128 128 = 50995830917654165476376880448 := by decide +kernel
private theorem rec_0_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 256 128 = 43819064908982411787594671424 := by decide +kernel
private theorem rec_0_12_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 384 128 = 36990462417161505038276273472 := by decide +kernel
private theorem rec_0_12_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 512 128 = 30501428088303207318494684480 := by decide +kernel
private theorem rec_0_12_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 640 128 = 24343385690734479282660961383 := by decide +kernel
private theorem rec_0_12_2368_1_part6 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 768 128 = 18507785548594043513943392563 := by decide +kernel
private theorem rec_0_12_2368_1_part7 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 896 128 = 12986052428896330384493346027 := by decide +kernel
private theorem rec_0_12_2368_1_part8 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 1024 128 = 7769612993159577678123413073 := by decide +kernel
private theorem rec_0_12_2368_1_part9 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 1152 128 = 2849906898666938950929570782 := by decide +kernel
private theorem rec_0_12_2368_1_part10 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 1280 14 = 25609689399236881512303805 := by decide +kernel
private theorem rec_0_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 0 256 = 109525199712800997564343470720 :=
  phaseBlock_append rec_0_12_2368_1_part0 rec_0_12_2368_1_part1 rfl rfl rfl
private theorem rec_0_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 384 256 = 67491890505464712356770957952 :=
  phaseBlock_append rec_0_12_2368_1_part3 rec_0_12_2368_1_part4 rfl rfl rfl
private theorem rec_0_12_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 256 384 = 111310955414447124144365629376 :=
  phaseBlock_append rec_0_12_2368_1_part2 rec_0_12_2368_1_join1 rfl rfl rfl
private theorem rec_0_12_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 0 640 = 220836155127248121708709100096 :=
  phaseBlock_append rec_0_12_2368_1_join0 rec_0_12_2368_1_join2 rfl rfl rfl
private theorem rec_0_12_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 768 256 = 31493837977490373898436738590 :=
  phaseBlock_append rec_0_12_2368_1_part6 rec_0_12_2368_1_part7 rfl rfl rfl
private theorem rec_0_12_2368_1_join5 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 640 384 = 55837223668224853181097699973 :=
  phaseBlock_append rec_0_12_2368_1_part5 rec_0_12_2368_1_join4 rfl rfl rfl
private theorem rec_0_12_2368_1_join6 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 1152 142 = 2875516588066175832441874587 :=
  phaseBlock_append rec_0_12_2368_1_part9 rec_0_12_2368_1_part10 rfl rfl rfl
private theorem rec_0_12_2368_1_join7 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 1024 270 = 10645129581225753510565287660 :=
  phaseBlock_append rec_0_12_2368_1_part8 rec_0_12_2368_1_join6 rfl rfl rfl
private theorem rec_0_12_2368_1_join8 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 640 654 = 66482353249450606691662987633 :=
  phaseBlock_append rec_0_12_2368_1_join5 rec_0_12_2368_1_join7 rfl rfl rfl
private theorem rec_0_12_2368_1_join9 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2368 31 1 0 1 1) 0 1294 = 287318508376698728400372087729 :=
  phaseBlock_append rec_0_12_2368_1_join3 rec_0_12_2368_1_join8 rfl rfl rfl

private theorem rec_0_12_2368_1 : fastPhase (bank 0 12).shape 179798 2368 31 1 0 1 1 = 287318508376698728400372087729 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_0_12_2368_1_join9

private theorem rec_0_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 0 128 = 58589360373293464352672294592 := by decide +kernel
private theorem rec_0_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 128 128 = 51053000852682292512493045440 := by decide +kernel
private theorem rec_0_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 256 128 = 43873488400506141001557173952 := by decide +kernel
private theorem rec_0_12_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 384 128 = 37042214267245641405388310208 := by decide +kernel
private theorem rec_0_12_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 512 128 = 30550582701965109488146785984 := by decide +kernel
private theorem rec_0_12_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 640 128 = 24390016947464621097271427964 := by decide +kernel
private theorem rec_0_12_2369_0_part6 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 768 128 = 18551967055164374240530677580 := by decide +kernel
private theorem rec_0_12_2369_0_part7 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 896 128 = 13027857637381759901197994646 := by decide +kernel
private theorem rec_0_12_2369_0_part8 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 1024 128 = 7809114930584551642686200589 := by decide +kernel
private theorem rec_0_12_2369_0_part9 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 1152 128 = 2887178171833349649759879360 := by decide +kernel
private theorem rec_0_12_2369_0_part10 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 1280 14 = 29553986240811662160277638 := by decide +kernel
private theorem rec_0_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 0 256 = 109642361225975756865165340032 :=
  phaseBlock_append rec_0_12_2369_0_part0 rec_0_12_2369_0_part1 rfl rfl rfl
private theorem rec_0_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 384 256 = 67592796969210750893535096192 :=
  phaseBlock_append rec_0_12_2369_0_part3 rec_0_12_2369_0_part4 rfl rfl rfl
private theorem rec_0_12_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 256 384 = 111466285369716891895092270144 :=
  phaseBlock_append rec_0_12_2369_0_part2 rec_0_12_2369_0_join1 rfl rfl rfl
private theorem rec_0_12_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 0 640 = 221108646595692648760257610176 :=
  phaseBlock_append rec_0_12_2369_0_join0 rec_0_12_2369_0_join2 rfl rfl rfl
private theorem rec_0_12_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 768 256 = 31579824692546134141728672226 :=
  phaseBlock_append rec_0_12_2369_0_part6 rec_0_12_2369_0_part7 rfl rfl rfl
private theorem rec_0_12_2369_0_join5 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 640 384 = 55969841640010755239000100190 :=
  phaseBlock_append rec_0_12_2369_0_part5 rec_0_12_2369_0_join4 rfl rfl rfl
private theorem rec_0_12_2369_0_join6 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 1152 142 = 2916732158074161311920156998 :=
  phaseBlock_append rec_0_12_2369_0_part9 rec_0_12_2369_0_part10 rfl rfl rfl
private theorem rec_0_12_2369_0_join7 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 1024 270 = 10725847088658712954606357587 :=
  phaseBlock_append rec_0_12_2369_0_part8 rec_0_12_2369_0_join6 rfl rfl rfl
private theorem rec_0_12_2369_0_join8 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 640 654 = 66695688728669468193606457777 :=
  phaseBlock_append rec_0_12_2369_0_join5 rec_0_12_2369_0_join7 rfl rfl rfl
private theorem rec_0_12_2369_0_join9 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 0) 0 1294 = 287804335324362116953864067953 :=
  phaseBlock_append rec_0_12_2369_0_join3 rec_0_12_2369_0_join8 rfl rfl rfl

private theorem rec_0_12_2369_0 : fastPhase (bank 0 12).shape 179798 2369 31 1 0 1 0 = 287804335324362116953864067953 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_0_12_2369_0_join9

private theorem rec_0_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 0 128 = 58529900946054721151957444352 := by decide +kernel
private theorem rec_0_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 128 128 = 50996267529310648112485033728 := by decide +kernel
private theorem rec_0_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 256 128 = 43819416072389918923351533312 := by decide +kernel
private theorem rec_0_12_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 384 128 = 36990737924832996528287082240 := by decide +kernel
private theorem rec_0_12_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 512 128 = 30501637434715899951809603328 := by decide +kernel
private theorem rec_0_12_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 640 128 = 24343537932979819166863625568 := by decide +kernel
private theorem rec_0_12_2369_1_part6 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 768 128 = 18507889517881145470304640627 := by decide +kernel
private theorem rec_0_12_2369_1_part7 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 896 128 = 12986116885563055304759774298 := by decide +kernel
private theorem rec_0_12_2369_1_part8 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 1024 128 = 7769646371475212006814017364 := by decide +kernel
private theorem rec_0_12_2369_1_part9 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 1152 128 = 2849917311648700334668384770 := by decide +kernel
private theorem rec_0_12_2369_1_part10 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 1280 14 = 25609770549976413094560504 := by decide +kernel
private theorem rec_0_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 0 256 = 109526168475365369264442478080 :=
  phaseBlock_append rec_0_12_2369_1_part0 rec_0_12_2369_1_part1 rfl rfl rfl
private theorem rec_0_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 384 256 = 67492375359548896480096685568 :=
  phaseBlock_append rec_0_12_2369_1_part3 rec_0_12_2369_1_part4 rfl rfl rfl
private theorem rec_0_12_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 256 384 = 111311791431938815403448218880 :=
  phaseBlock_append rec_0_12_2369_1_part2 rec_0_12_2369_1_join1 rfl rfl rfl
private theorem rec_0_12_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 0 640 = 220837959907304184667890696960 :=
  phaseBlock_append rec_0_12_2369_1_join0 rec_0_12_2369_1_join2 rfl rfl rfl
private theorem rec_0_12_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 768 256 = 31494006403444200775064414925 :=
  phaseBlock_append rec_0_12_2369_1_part6 rec_0_12_2369_1_part7 rfl rfl rfl
private theorem rec_0_12_2369_1_join5 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 640 384 = 55837544336424019941928040493 :=
  phaseBlock_append rec_0_12_2369_1_part5 rec_0_12_2369_1_join4 rfl rfl rfl
private theorem rec_0_12_2369_1_join6 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 1152 142 = 2875527082198676747762945274 :=
  phaseBlock_append rec_0_12_2369_1_part9 rec_0_12_2369_1_part10 rfl rfl rfl
private theorem rec_0_12_2369_1_join7 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 1024 270 = 10645173453673888754576962638 :=
  phaseBlock_append rec_0_12_2369_1_part8 rec_0_12_2369_1_join6 rfl rfl rfl
private theorem rec_0_12_2369_1_join8 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 640 654 = 66482717790097908696505003131 :=
  phaseBlock_append rec_0_12_2369_1_join5 rec_0_12_2369_1_join7 rfl rfl rfl
private theorem rec_0_12_2369_1_join9 :
    phaseBlock (fastLayerG (bank 0 12).shape 179798 2369 31 1 0 1 1) 0 1294 = 287320677697402093364395700091 :=
  phaseBlock_append rec_0_12_2369_1_join3 rec_0_12_2369_1_join8 rfl rfl rfl

private theorem rec_0_12_2369_1 : fastPhase (bank 0 12).shape 179798 2369 31 1 0 1 1 = 287320677697402093364395700091 :=
  phase_of_blockG (n := 1294) (by decide +kernel) rec_0_12_2369_1_join9

theorem receipt_0_12 : Checked (bank 0 12) 31 0 1 := by
  refine checked_from_values (bank 0 12) 31 0 1
    (P3_7_1.checked (bank 0 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_12_2368_0 rec_0_12_2368_1 rec_0_12_2369_0 rec_0_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 0 128 = 231357995021825845291575994880 := by decide +kernel
private theorem rec_0_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 128 128 = 209901546901764337240812259840 := by decide +kernel
private theorem rec_0_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 256 128 = 189179831655353226831322556928 := by decide +kernel
private theorem rec_0_13_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 384 128 = 169180073511648035378954291712 := by decide +kernel
private theorem rec_0_13_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 512 128 = 149889512507360821332656744960 := by decide +kernel
private theorem rec_0_13_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 640 128 = 131295404480574975985927457280 := by decide +kernel
private theorem rec_0_13_2368_0_part6 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 768 128 = 113385021064460019188258613760 := by decide +kernel
private theorem rec_0_13_2368_0_part7 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 896 128 = 96145660088789419616866320072 := by decide +kernel
private theorem rec_0_13_2368_0_part8 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 1024 128 = 79564672223261573572857947406 := by decide +kernel
private theorem rec_0_13_2368_0_part9 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 1152 128 = 63629358105140481250990118684 := by decide +kernel
private theorem rec_0_13_2368_0_part10 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 1280 128 = 48327008359528965578787893170 := by decide +kernel
private theorem rec_0_13_2368_0_part11 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 1408 128 = 33644929439230772353315725978 := by decide +kernel
private theorem rec_0_13_2368_0_part12 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 1536 128 = 19570443653854160275143486231 := by decide +kernel
private theorem rec_0_13_2368_0_part13 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 1664 123 = 6098768548987412958746635428 := by decide +kernel
private theorem rec_0_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 128 256 = 399081378557117564072134816768 :=
  phaseBlock_append rec_0_13_2368_0_part1 rec_0_13_2368_0_part2 rfl rfl rfl
private theorem rec_0_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 0 384 = 630439373578943409363710811648 :=
  phaseBlock_append rec_0_13_2368_0_part0 rec_0_13_2368_0_join0 rfl rfl rfl
private theorem rec_0_13_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 384 256 = 319069586019008856711611036672 :=
  phaseBlock_append rec_0_13_2368_0_part3 rec_0_13_2368_0_part4 rfl rfl rfl
private theorem rec_0_13_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 640 256 = 244680425545034995174186071040 :=
  phaseBlock_append rec_0_13_2368_0_part5 rec_0_13_2368_0_part6 rfl rfl rfl
private theorem rec_0_13_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 384 512 = 563750011564043851885797107712 :=
  phaseBlock_append rec_0_13_2368_0_join2 rec_0_13_2368_0_join3 rfl rfl rfl
private theorem rec_0_13_2368_0_join5 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 0 896 = 1194189385142987261249507919360 :=
  phaseBlock_append rec_0_13_2368_0_join1 rec_0_13_2368_0_join4 rfl rfl rfl
private theorem rec_0_13_2368_0_join6 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 1024 256 = 143194030328402054823848066090 :=
  phaseBlock_append rec_0_13_2368_0_part8 rec_0_13_2368_0_part9 rfl rfl rfl
private theorem rec_0_13_2368_0_join7 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 896 384 = 239339690417191474440714386162 :=
  phaseBlock_append rec_0_13_2368_0_part7 rec_0_13_2368_0_join6 rfl rfl rfl
private theorem rec_0_13_2368_0_join8 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 1280 256 = 81971937798759737932103619148 :=
  phaseBlock_append rec_0_13_2368_0_part10 rec_0_13_2368_0_part11 rfl rfl rfl
private theorem rec_0_13_2368_0_join9 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 1536 251 = 25669212202841573233890121659 :=
  phaseBlock_append rec_0_13_2368_0_part12 rec_0_13_2368_0_part13 rfl rfl rfl
private theorem rec_0_13_2368_0_join10 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 1280 507 = 107641150001601311165993740807 :=
  phaseBlock_append rec_0_13_2368_0_join8 rec_0_13_2368_0_join9 rfl rfl rfl
private theorem rec_0_13_2368_0_join11 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 896 891 = 346980840418792785606708126969 :=
  phaseBlock_append rec_0_13_2368_0_join7 rec_0_13_2368_0_join10 rfl rfl rfl
private theorem rec_0_13_2368_0_join12 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 0) 0 1787 = 1541170225561780046856216046329 :=
  phaseBlock_append rec_0_13_2368_0_join5 rec_0_13_2368_0_join11 rfl rfl rfl

private theorem rec_0_13_2368_0 : fastPhase (bank 0 13).shape 179798 2368 44 1 0 1 0 = 1541170225561780046856216046329 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_0_13_2368_0_join12

private theorem rec_0_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 0 128 = 231189835993547470098218402880 := by decide +kernel
private theorem rec_0_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 128 128 = 209738982723594648955495334976 := by decide +kernel
private theorem rec_0_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 256 128 = 189022765707824576700538012736 := by decide +kernel
private theorem rec_0_13_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 384 128 = 169028409295757867682959737920 := by decide +kernel
private theorem rec_0_13_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 512 128 = 149743153644523546593296827456 := by decide +kernel
private theorem rec_0_13_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 640 128 = 131154254712573844174454998080 := by decide +kernel
private theorem rec_0_13_2368_1_part6 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 768 128 = 113248984253398992933155750976 := by decide +kernel
private theorem rec_0_13_2368_1_part7 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 896 128 = 96014640203838642464079837434 := by decide +kernel
private theorem rec_0_13_2368_1_part8 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 1024 128 = 79438573278226021359411407980 := by decide +kernel
private theorem rec_0_13_2368_1_part9 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 1152 128 = 63508084207969498769955410785 := by decide +kernel
private theorem rec_0_13_2368_1_part10 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 1280 128 = 48210463738542960946094808834 := by decide +kernel
private theorem rec_0_13_2368_1_part11 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 1408 128 = 33533018443098978531936090310 := by decide +kernel
private theorem rec_0_13_2368_1_part12 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 1536 128 = 19463070751437604128579282248 := by decide +kernel
private theorem rec_0_13_2368_1_part13 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 1664 123 = 5999776828793979526182500114 := by decide +kernel
private theorem rec_0_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 128 256 = 398761748431419225656033347712 :=
  phaseBlock_append rec_0_13_2368_1_part1 rec_0_13_2368_1_part2 rfl rfl rfl
private theorem rec_0_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 0 384 = 629951584424966695754251750592 :=
  phaseBlock_append rec_0_13_2368_1_part0 rec_0_13_2368_1_join0 rfl rfl rfl
private theorem rec_0_13_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 384 256 = 318771562940281414276256565376 :=
  phaseBlock_append rec_0_13_2368_1_part3 rec_0_13_2368_1_part4 rfl rfl rfl
private theorem rec_0_13_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 640 256 = 244403238965972837107610749056 :=
  phaseBlock_append rec_0_13_2368_1_part5 rec_0_13_2368_1_part6 rfl rfl rfl
private theorem rec_0_13_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 384 512 = 563174801906254251383867314432 :=
  phaseBlock_append rec_0_13_2368_1_join2 rec_0_13_2368_1_join3 rfl rfl rfl
private theorem rec_0_13_2368_1_join5 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 0 896 = 1193126386331220947138119065024 :=
  phaseBlock_append rec_0_13_2368_1_join1 rec_0_13_2368_1_join4 rfl rfl rfl
private theorem rec_0_13_2368_1_join6 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 1024 256 = 142946657486195520129366818765 :=
  phaseBlock_append rec_0_13_2368_1_part8 rec_0_13_2368_1_part9 rfl rfl rfl
private theorem rec_0_13_2368_1_join7 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 896 384 = 238961297690034162593446656199 :=
  phaseBlock_append rec_0_13_2368_1_part7 rec_0_13_2368_1_join6 rfl rfl rfl
private theorem rec_0_13_2368_1_join8 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 1280 256 = 81743482181641939478030899144 :=
  phaseBlock_append rec_0_13_2368_1_part10 rec_0_13_2368_1_part11 rfl rfl rfl
private theorem rec_0_13_2368_1_join9 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 1536 251 = 25462847580231583654761782362 :=
  phaseBlock_append rec_0_13_2368_1_part12 rec_0_13_2368_1_part13 rfl rfl rfl
private theorem rec_0_13_2368_1_join10 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 1280 507 = 107206329761873523132792681506 :=
  phaseBlock_append rec_0_13_2368_1_join8 rec_0_13_2368_1_join9 rfl rfl rfl
private theorem rec_0_13_2368_1_join11 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 896 891 = 346167627451907685726239337705 :=
  phaseBlock_append rec_0_13_2368_1_join7 rec_0_13_2368_1_join10 rfl rfl rfl
private theorem rec_0_13_2368_1_join12 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2368 44 1 0 1 1) 0 1787 = 1539294013783128632864358402729 :=
  phaseBlock_append rec_0_13_2368_1_join5 rec_0_13_2368_1_join11 rfl rfl rfl

private theorem rec_0_13_2368_1 : fastPhase (bank 0 13).shape 179798 2368 44 1 0 1 1 = 1539294013783128632864358402729 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_0_13_2368_1_join12

private theorem rec_0_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 0 128 = 231360112747371683525148229440 := by decide +kernel
private theorem rec_0_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 128 128 = 209903388279762960547099041600 := by decide +kernel
private theorem rec_0_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 256 128 = 189181417483654543076215258944 := by decide +kernel
private theorem rec_0_13_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 384 128 = 169181424145640791345262174016 := by decide +kernel
private theorem rec_0_13_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 512 128 = 149890647860524232685924237120 := by decide +kernel
private theorem rec_0_13_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 640 128 = 131296344025030137337925885760 := by decide +kernel
private theorem rec_0_13_2369_0_part6 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 768 128 = 113385783831521094258152374080 := by decide +kernel
private theorem rec_0_13_2369_0_part7 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 896 128 = 96146264315921010663245412915 := by decide +kernel
private theorem rec_0_13_2369_0_part8 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 1024 128 = 79565135720852003381617072101 := by decide +kernel
private theorem rec_0_13_2369_0_part9 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 1152 128 = 63629698913578968938002830209 := by decide +kernel
private theorem rec_0_13_2369_0_part10 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 1280 128 = 48327244042174663346083531185 := by decide +kernel
private theorem rec_0_13_2369_0_part11 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 1408 128 = 33645077092874347537461221085 := by decide +kernel
private theorem rec_0_13_2369_0_part12 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 1536 128 = 19570519895989262983152128692 := by decide +kernel
private theorem rec_0_13_2369_0_part13 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 1664 123 = 6098789545383304658301300415 := by decide +kernel
private theorem rec_0_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 128 256 = 399084805763417503623314300544 :=
  phaseBlock_append rec_0_13_2369_0_part1 rec_0_13_2369_0_part2 rfl rfl rfl
private theorem rec_0_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 0 384 = 630444918510789187148462529984 :=
  phaseBlock_append rec_0_13_2369_0_part0 rec_0_13_2369_0_join0 rfl rfl rfl
private theorem rec_0_13_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 384 256 = 319072072006165024031186411136 :=
  phaseBlock_append rec_0_13_2369_0_part3 rec_0_13_2369_0_part4 rfl rfl rfl
private theorem rec_0_13_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 640 256 = 244682127856551231596078259840 :=
  phaseBlock_append rec_0_13_2369_0_part5 rec_0_13_2369_0_part6 rfl rfl rfl
private theorem rec_0_13_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 384 512 = 563754199862716255627264670976 :=
  phaseBlock_append rec_0_13_2369_0_join2 rec_0_13_2369_0_join3 rfl rfl rfl
private theorem rec_0_13_2369_0_join5 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 0 896 = 1194199118373505442775727200960 :=
  phaseBlock_append rec_0_13_2369_0_join1 rec_0_13_2369_0_join4 rfl rfl rfl
private theorem rec_0_13_2369_0_join6 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 1024 256 = 143194834634430972319619902310 :=
  phaseBlock_append rec_0_13_2369_0_part8 rec_0_13_2369_0_part9 rfl rfl rfl
private theorem rec_0_13_2369_0_join7 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 896 384 = 239341098950351982982865315225 :=
  phaseBlock_append rec_0_13_2369_0_part7 rec_0_13_2369_0_join6 rfl rfl rfl
private theorem rec_0_13_2369_0_join8 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 1280 256 = 81972321135049010883544752270 :=
  phaseBlock_append rec_0_13_2369_0_part10 rec_0_13_2369_0_part11 rfl rfl rfl
private theorem rec_0_13_2369_0_join9 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 1536 251 = 25669309441372567641453429107 :=
  phaseBlock_append rec_0_13_2369_0_part12 rec_0_13_2369_0_part13 rfl rfl rfl
private theorem rec_0_13_2369_0_join10 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 1280 507 = 107641630576421578524998181377 :=
  phaseBlock_append rec_0_13_2369_0_join8 rec_0_13_2369_0_join9 rfl rfl rfl
private theorem rec_0_13_2369_0_join11 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 896 891 = 346982729526773561507863496602 :=
  phaseBlock_append rec_0_13_2369_0_join7 rec_0_13_2369_0_join10 rfl rfl rfl
private theorem rec_0_13_2369_0_join12 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 0) 0 1787 = 1541181847900279004283590697562 :=
  phaseBlock_append rec_0_13_2369_0_join5 rec_0_13_2369_0_join11 rfl rfl rfl

private theorem rec_0_13_2369_0 : fastPhase (bank 0 13).shape 179798 2369 44 1 0 1 0 = 1541181847900279004283590697562 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_0_13_2369_0_join12

private theorem rec_0_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 0 128 = 231191952470785280220631869120 := by decide +kernel
private theorem rec_0_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 128 128 = 209740822935218413143515178688 := by decide +kernel
private theorem rec_0_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 256 128 = 189024350449598869097420433088 := by decide +kernel
private theorem rec_0_13_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 384 128 = 169029758920989121023346779840 := by decide +kernel
private theorem rec_0_13_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 512 128 = 149744288064611680863363606208 := by decide +kernel
private theorem rec_0_13_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 640 128 = 131155193397563675369731368640 := by decide +kernel
private theorem rec_0_13_2369_1_part6 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 768 128 = 113249746232531421914022422208 := by decide +kernel
private theorem rec_0_13_2369_1_part7 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 896 128 = 96015243712951165746726789811 := by decide +kernel
private theorem rec_0_13_2369_1_part8 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 1024 128 = 79439036126271212321828953891 := by decide +kernel
private theorem rec_0_13_2369_1_part9 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 1152 128 = 63508424433176467324655183658 := by decide +kernel
private theorem rec_0_13_2369_1_part10 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 1280 128 = 48210698902120303545678598813 := by decide +kernel
private theorem rec_0_13_2369_1_part11 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 1408 128 = 33533165639673641434853703908 := by decide +kernel
private theorem rec_0_13_2369_1_part12 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 1536 128 = 19463146596346265017718400608 := by decide +kernel
private theorem rec_0_13_2369_1_part13 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 1664 123 = 5999797497867318989175962237 := by decide +kernel
private theorem rec_0_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 128 256 = 398765173384817282240935611776 :=
  phaseBlock_append rec_0_13_2369_1_part1 rec_0_13_2369_1_part2 rfl rfl rfl
private theorem rec_0_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 0 384 = 629957125855602562461567480896 :=
  phaseBlock_append rec_0_13_2369_1_part0 rec_0_13_2369_1_join0 rfl rfl rfl
private theorem rec_0_13_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 384 256 = 318774046985600801886710386048 :=
  phaseBlock_append rec_0_13_2369_1_part3 rec_0_13_2369_1_part4 rfl rfl rfl
private theorem rec_0_13_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 640 256 = 244404939630095097283753790848 :=
  phaseBlock_append rec_0_13_2369_1_part5 rec_0_13_2369_1_part6 rfl rfl rfl
private theorem rec_0_13_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 384 512 = 563178986615695899170464176896 :=
  phaseBlock_append rec_0_13_2369_1_join2 rec_0_13_2369_1_join3 rfl rfl rfl
private theorem rec_0_13_2369_1_join5 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 0 896 = 1193136112471298461632031657792 :=
  phaseBlock_append rec_0_13_2369_1_join1 rec_0_13_2369_1_join4 rfl rfl rfl
private theorem rec_0_13_2369_1_join6 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 1024 256 = 142947460559447679646484137549 :=
  phaseBlock_append rec_0_13_2369_1_part8 rec_0_13_2369_1_part9 rfl rfl rfl
private theorem rec_0_13_2369_1_join7 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 896 384 = 238962704272398845393210927360 :=
  phaseBlock_append rec_0_13_2369_1_part7 rec_0_13_2369_1_join6 rfl rfl rfl
private theorem rec_0_13_2369_1_join8 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 1280 256 = 81743864541793944980532302721 :=
  phaseBlock_append rec_0_13_2369_1_part10 rec_0_13_2369_1_part11 rfl rfl rfl
private theorem rec_0_13_2369_1_join9 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 1536 251 = 25462944094213584006894362845 :=
  phaseBlock_append rec_0_13_2369_1_part12 rec_0_13_2369_1_part13 rfl rfl rfl
private theorem rec_0_13_2369_1_join10 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 1280 507 = 107206808636007528987426665566 :=
  phaseBlock_append rec_0_13_2369_1_join8 rec_0_13_2369_1_join9 rfl rfl rfl
private theorem rec_0_13_2369_1_join11 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 896 891 = 346169512908406374380637592926 :=
  phaseBlock_append rec_0_13_2369_1_join7 rec_0_13_2369_1_join10 rfl rfl rfl
private theorem rec_0_13_2369_1_join12 :
    phaseBlock (fastLayerG (bank 0 13).shape 179798 2369 44 1 0 1 1) 0 1787 = 1539305625379704836012669250718 :=
  phaseBlock_append rec_0_13_2369_1_join5 rec_0_13_2369_1_join11 rfl rfl rfl

private theorem rec_0_13_2369_1 : fastPhase (bank 0 13).shape 179798 2369 44 1 0 1 1 = 1539305625379704836012669250718 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_0_13_2369_1_join12

theorem receipt_0_13 : Checked (bank 0 13) 44 0 1 := by
  refine checked_from_values (bank 0 13) 44 0 1
    (P3_7_1.checked (bank 0 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_13_2368_0 rec_0_13_2368_1 rec_0_13_2369_0 rec_0_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 0 128 = 2715915751440253011891869147328 := by decide +kernel
private theorem rec_0_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 128 128 = 2577392133976841883562248298688 := by decide +kernel
private theorem rec_0_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 256 128 = 2441491017318269171237037170880 := by decide +kernel
private theorem rec_0_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 384 128 = 2308187200485103173632425713856 := by decide +kernel
private theorem rec_0_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 512 128 = 2177455504608217591622269231296 := by decide +kernel
private theorem rec_0_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 640 128 = 2049270772922506323949534765248 := by decide +kernel
private theorem rec_0_14_2368_0_part6 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 768 128 = 1923607870760598262937747480768 := by decide +kernel
private theorem rec_0_14_2368_0_part7 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 896 128 = 1800441685546572090202437050560 := by decide +kernel
private theorem rec_0_14_2368_0_part8 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1024 128 = 1679747126789671072362584039616 := by decide +kernel
private theorem rec_0_14_2368_0_part9 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1152 128 = 1561499126078017856752066289856 := by decide +kernel
private theorem rec_0_14_2368_0_part10 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1280 128 = 1445672637072329267131105304768 := by decide +kernel
private theorem rec_0_14_2368_0_part11 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1408 128 = 1332242635499631099397712634048 := by decide +kernel
private theorem rec_0_14_2368_0_part12 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1536 128 = 1221184119563452703066442212076 := by decide +kernel
private theorem rec_0_14_2368_0_part13 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1664 128 = 1112472204488788976163873900037 := by decide +kernel
private theorem rec_0_14_2368_0_part14 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1792 128 = 1006082101350526996093271255050 := by decide +kernel
private theorem rec_0_14_2368_0_part15 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1920 128 = 901988818130716317585410440132 := by decide +kernel
private theorem rec_0_14_2368_0_part16 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2048 128 = 800167355397798569565844996412 := by decide +kernel
private theorem rec_0_14_2368_0_part17 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2176 128 = 700592735743161951810688186932 := by decide +kernel
private theorem rec_0_14_2368_0_part18 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2304 128 = 603240003743026635353369261608 := by decide +kernel
private theorem rec_0_14_2368_0_part19 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2432 128 = 508084226118136792757342586632 := by decide +kernel
private theorem rec_0_14_2368_0_part20 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2560 128 = 415100491799433625728100646152 := by decide +kernel
private theorem rec_0_14_2368_0_part21 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2688 128 = 324263911676852912460105477986 := by decide +kernel
private theorem rec_0_14_2368_0_part22 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2816 128 = 235549618693559712814825727840 := by decide +kernel
private theorem rec_0_14_2368_0_part23 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2944 128 = 148932767974567606514679784775 := by decide +kernel
private theorem rec_0_14_2368_0_part24 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 3072 128 = 64388536641476408028612021258 := by decide +kernel
private theorem rec_0_14_2368_0_part25 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 3200 35 = 3157632098305951116790282899 := by decide +kernel
private theorem rec_0_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 128 256 = 5018883151295111054799285469568 :=
  phaseBlock_append rec_0_14_2368_0_part1 rec_0_14_2368_0_part2 rfl rfl rfl
private theorem rec_0_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 0 384 = 7734798902735364066691154616896 :=
  phaseBlock_append rec_0_14_2368_0_part0 rec_0_14_2368_0_join0 rfl rfl rfl
private theorem rec_0_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 512 256 = 4226726277530723915571803996544 :=
  phaseBlock_append rec_0_14_2368_0_part4 rec_0_14_2368_0_part5 rfl rfl rfl
private theorem rec_0_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 384 384 = 6534913478015827089204229710400 :=
  phaseBlock_append rec_0_14_2368_0_part3 rec_0_14_2368_0_join2 rfl rfl rfl
private theorem rec_0_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 0 768 = 14269712380751191155895384327296 :=
  phaseBlock_append rec_0_14_2368_0_join1 rec_0_14_2368_0_join3 rfl rfl rfl
private theorem rec_0_14_2368_0_join5 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 896 256 = 3480188812336243162565021090176 :=
  phaseBlock_append rec_0_14_2368_0_part7 rec_0_14_2368_0_part8 rfl rfl rfl
private theorem rec_0_14_2368_0_join6 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 768 384 = 5403796683096841425502768570944 :=
  phaseBlock_append rec_0_14_2368_0_part6 rec_0_14_2368_0_join5 rfl rfl rfl
private theorem rec_0_14_2368_0_join7 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1152 256 = 3007171763150347123883171594624 :=
  phaseBlock_append rec_0_14_2368_0_part9 rec_0_14_2368_0_part10 rfl rfl rfl
private theorem rec_0_14_2368_0_join8 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1408 256 = 2553426755063083802464154846124 :=
  phaseBlock_append rec_0_14_2368_0_part11 rec_0_14_2368_0_part12 rfl rfl rfl
private theorem rec_0_14_2368_0_join9 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1152 512 = 5560598518213430926347326440748 :=
  phaseBlock_append rec_0_14_2368_0_join7 rec_0_14_2368_0_join8 rfl rfl rfl
private theorem rec_0_14_2368_0_join10 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 768 896 = 10964395201310272351850095011692 :=
  phaseBlock_append rec_0_14_2368_0_join6 rec_0_14_2368_0_join9 rfl rfl rfl
private theorem rec_0_14_2368_0_join11 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 0 1664 = 25234107582061463507745479338988 :=
  phaseBlock_append rec_0_14_2368_0_join4 rec_0_14_2368_0_join10 rfl rfl rfl
private theorem rec_0_14_2368_0_join12 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1792 256 = 1908070919481243313678681695182 :=
  phaseBlock_append rec_0_14_2368_0_part14 rec_0_14_2368_0_part15 rfl rfl rfl
private theorem rec_0_14_2368_0_join13 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1664 384 = 3020543123970032289842555595219 :=
  phaseBlock_append rec_0_14_2368_0_part13 rec_0_14_2368_0_join12 rfl rfl rfl
private theorem rec_0_14_2368_0_join14 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2176 256 = 1303832739486188587164057448540 :=
  phaseBlock_append rec_0_14_2368_0_part17 rec_0_14_2368_0_part18 rfl rfl rfl
private theorem rec_0_14_2368_0_join15 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2048 384 = 2104000094883987156729902444952 :=
  phaseBlock_append rec_0_14_2368_0_part16 rec_0_14_2368_0_join14 rfl rfl rfl
private theorem rec_0_14_2368_0_join16 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1664 768 = 5124543218854019446572458040171 :=
  phaseBlock_append rec_0_14_2368_0_join13 rec_0_14_2368_0_join15 rfl rfl rfl
private theorem rec_0_14_2368_0_join17 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2560 256 = 739364403476286538188206124138 :=
  phaseBlock_append rec_0_14_2368_0_part20 rec_0_14_2368_0_part21 rfl rfl rfl
private theorem rec_0_14_2368_0_join18 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2432 384 = 1247448629594423330945548710770 :=
  phaseBlock_append rec_0_14_2368_0_part19 rec_0_14_2368_0_join17 rfl rfl rfl
private theorem rec_0_14_2368_0_join19 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2816 256 = 384482386668127319329505512615 :=
  phaseBlock_append rec_0_14_2368_0_part22 rec_0_14_2368_0_part23 rfl rfl rfl
private theorem rec_0_14_2368_0_join20 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 3072 163 = 67546168739782359145402304157 :=
  phaseBlock_append rec_0_14_2368_0_part24 rec_0_14_2368_0_part25 rfl rfl rfl
private theorem rec_0_14_2368_0_join21 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2816 419 = 452028555407909678474907816772 :=
  phaseBlock_append rec_0_14_2368_0_join19 rec_0_14_2368_0_join20 rfl rfl rfl
private theorem rec_0_14_2368_0_join22 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 2432 803 = 1699477185002333009420456527542 :=
  phaseBlock_append rec_0_14_2368_0_join18 rec_0_14_2368_0_join21 rfl rfl rfl
private theorem rec_0_14_2368_0_join23 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 1664 1571 = 6824020403856352455992914567713 :=
  phaseBlock_append rec_0_14_2368_0_join16 rec_0_14_2368_0_join22 rfl rfl rfl
private theorem rec_0_14_2368_0_join24 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 0) 0 3235 = 32058127985917815963738393906701 :=
  phaseBlock_append rec_0_14_2368_0_join11 rec_0_14_2368_0_join23 rfl rfl rfl

private theorem rec_0_14_2368_0 : fastPhase (bank 0 14).shape 179798 2368 76 1 0 1 0 = 32058127985917815963738393906701 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_0_14_2368_0_join24

private theorem rec_0_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 0 128 = 2714838515150698124416183177344 := by decide +kernel
private theorem rec_0_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 128 128 = 2576334794262763844823083561088 := by decide +kernel
private theorem rec_0_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 256 128 = 2440453383592301919287644606592 := by decide +kernel
private theorem rec_0_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 384 128 = 2307169082328372704654561112192 := by decide +kernel
private theorem rec_0_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 512 128 = 2176456711770293833134014369920 := by decide +kernel
private theorem rec_0_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 640 128 = 2048291115321355008013118550144 := by decide +kernel
private theorem rec_0_14_2368_1_part6 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 768 128 = 1922647158482532799367367086208 := by decide +kernel
private theorem rec_0_14_2368_1_part7 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 896 128 = 1799499728846205439772079059072 := by decide +kernel
private theorem rec_0_14_2368_1_part8 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1024 128 = 1678823736089867620013845581952 := by decide +kernel
private theorem rec_0_14_2368_1_part9 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1152 128 = 1560594111969845284801976184960 := by decide +kernel
private theorem rec_0_14_2368_1_part10 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1280 128 = 1444785810315010428479945199744 := by decide +kernel
private theorem rec_0_14_2368_1_part11 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1408 128 = 1331373807020495890736838144128 := by decide +kernel
private theorem rec_0_14_2368_1_part12 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1536 128 = 1220333100457618264265558629479 := by decide +kernel
private theorem rec_0_14_2368_1_part13 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1664 128 = 1111638805954607091659693597740 := by decide +kernel
private theorem rec_0_14_2368_1_part14 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1792 128 = 1005266134614180453207520955739 := by decide +kernel
private theorem rec_0_14_2368_1_part15 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1920 128 = 901190094568967973669437931069 := by decide +kernel
private theorem rec_0_14_2368_1_part16 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2048 128 = 799385686555510285178254595204 := by decide +kernel
private theorem rec_0_14_2368_1_part17 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2176 128 = 699827933333274915042786160843 := by decide +kernel
private theorem rec_0_14_2368_1_part18 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2304 128 = 602491879646623146096575692866 := by decide +kernel
private theorem rec_0_14_2368_1_part19 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2432 128 = 507352592384385466998244102017 := by decide +kernel
private theorem rec_0_14_2368_1_part20 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2560 128 = 414385160645372251032693865181 := by decide +kernel
private theorem rec_0_14_2368_1_part21 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2688 128 = 323564695487465453700179006925 := by decide +kernel
private theorem rec_0_14_2368_1_part22 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2816 128 = 234866330021835941218363003252 := by decide +kernel
private theorem rec_0_14_2368_1_part23 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2944 128 = 148265219541236380011661492521 := by decide +kernel
private theorem rec_0_14_2368_1_part24 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 3072 128 = 63736541335023297004579962183 := by decide +kernel
private theorem rec_0_14_2368_1_part25 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 3200 35 = 2982035305534009590793017111 := by decide +kernel
private theorem rec_0_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 128 256 = 5016788177855065764110728167680 :=
  phaseBlock_append rec_0_14_2368_1_part1 rec_0_14_2368_1_part2 rfl rfl rfl
private theorem rec_0_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 0 384 = 7731626693005763888526911345024 :=
  phaseBlock_append rec_0_14_2368_1_part0 rec_0_14_2368_1_join0 rfl rfl rfl
private theorem rec_0_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 512 256 = 4224747827091648841147132920064 :=
  phaseBlock_append rec_0_14_2368_1_part4 rec_0_14_2368_1_part5 rfl rfl rfl
private theorem rec_0_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 384 384 = 6531916909420021545801694032256 :=
  phaseBlock_append rec_0_14_2368_1_part3 rec_0_14_2368_1_join2 rfl rfl rfl
private theorem rec_0_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 0 768 = 14263543602425785434328605377280 :=
  phaseBlock_append rec_0_14_2368_1_join1 rec_0_14_2368_1_join3 rfl rfl rfl
private theorem rec_0_14_2368_1_join5 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 896 256 = 3478323464936073059785924641024 :=
  phaseBlock_append rec_0_14_2368_1_part7 rec_0_14_2368_1_part8 rfl rfl rfl
private theorem rec_0_14_2368_1_join6 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 768 384 = 5400970623418605859153291727232 :=
  phaseBlock_append rec_0_14_2368_1_part6 rec_0_14_2368_1_join5 rfl rfl rfl
private theorem rec_0_14_2368_1_join7 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1152 256 = 3005379922284855713281921384704 :=
  phaseBlock_append rec_0_14_2368_1_part9 rec_0_14_2368_1_part10 rfl rfl rfl
private theorem rec_0_14_2368_1_join8 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1408 256 = 2551706907478114155002396773607 :=
  phaseBlock_append rec_0_14_2368_1_part11 rec_0_14_2368_1_part12 rfl rfl rfl
private theorem rec_0_14_2368_1_join9 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1152 512 = 5557086829762969868284318158311 :=
  phaseBlock_append rec_0_14_2368_1_join7 rec_0_14_2368_1_join8 rfl rfl rfl
private theorem rec_0_14_2368_1_join10 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 768 896 = 10958057453181575727437609885543 :=
  phaseBlock_append rec_0_14_2368_1_join6 rec_0_14_2368_1_join9 rfl rfl rfl
private theorem rec_0_14_2368_1_join11 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 0 1664 = 25221601055607361161766215262823 :=
  phaseBlock_append rec_0_14_2368_1_join4 rec_0_14_2368_1_join10 rfl rfl rfl
private theorem rec_0_14_2368_1_join12 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1792 256 = 1906456229183148426876958886808 :=
  phaseBlock_append rec_0_14_2368_1_part14 rec_0_14_2368_1_part15 rfl rfl rfl
private theorem rec_0_14_2368_1_join13 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1664 384 = 3018095035137755518536652484548 :=
  phaseBlock_append rec_0_14_2368_1_part13 rec_0_14_2368_1_join12 rfl rfl rfl
private theorem rec_0_14_2368_1_join14 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2176 256 = 1302319812979898061139361853709 :=
  phaseBlock_append rec_0_14_2368_1_part17 rec_0_14_2368_1_part18 rfl rfl rfl
private theorem rec_0_14_2368_1_join15 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2048 384 = 2101705499535408346317616448913 :=
  phaseBlock_append rec_0_14_2368_1_part16 rec_0_14_2368_1_join14 rfl rfl rfl
private theorem rec_0_14_2368_1_join16 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1664 768 = 5119800534673163864854268933461 :=
  phaseBlock_append rec_0_14_2368_1_join13 rec_0_14_2368_1_join15 rfl rfl rfl
private theorem rec_0_14_2368_1_join17 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2560 256 = 737949856132837704732872872106 :=
  phaseBlock_append rec_0_14_2368_1_part20 rec_0_14_2368_1_part21 rfl rfl rfl
private theorem rec_0_14_2368_1_join18 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2432 384 = 1245302448517223171731116974123 :=
  phaseBlock_append rec_0_14_2368_1_part19 rec_0_14_2368_1_join17 rfl rfl rfl
private theorem rec_0_14_2368_1_join19 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2816 256 = 383131549563072321230024495773 :=
  phaseBlock_append rec_0_14_2368_1_part22 rec_0_14_2368_1_part23 rfl rfl rfl
private theorem rec_0_14_2368_1_join20 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 3072 163 = 66718576640557306595372979294 :=
  phaseBlock_append rec_0_14_2368_1_part24 rec_0_14_2368_1_part25 rfl rfl rfl
private theorem rec_0_14_2368_1_join21 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2816 419 = 449850126203629627825397475067 :=
  phaseBlock_append rec_0_14_2368_1_join19 rec_0_14_2368_1_join20 rfl rfl rfl
private theorem rec_0_14_2368_1_join22 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 2432 803 = 1695152574720852799556514449190 :=
  phaseBlock_append rec_0_14_2368_1_join18 rec_0_14_2368_1_join21 rfl rfl rfl
private theorem rec_0_14_2368_1_join23 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 1664 1571 = 6814953109394016664410783382651 :=
  phaseBlock_append rec_0_14_2368_1_join16 rec_0_14_2368_1_join22 rfl rfl rfl
private theorem rec_0_14_2368_1_join24 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2368 76 1 0 1 1) 0 3235 = 32036554165001377826176998645474 :=
  phaseBlock_append rec_0_14_2368_1_join11 rec_0_14_2368_1_join23 rfl rfl rfl

private theorem rec_0_14_2368_1 : fastPhase (bank 0 14).shape 179798 2368 76 1 0 1 1 = 32036554165001377826176998645474 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_0_14_2368_1_join24

private theorem rec_0_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 0 128 = 2715940860691211905898468200064 := by decide +kernel
private theorem rec_0_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 128 128 = 2577415425806146344471837445760 := by decide +kernel
private theorem rec_0_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 256 128 = 2441512565938619374668096687744 := by decide +kernel
private theorem rec_0_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 384 128 = 2308207079238948044891071975040 := by decide +kernel
private theorem rec_0_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 512 128 = 2177473785968525785763912142464 := by decide +kernel
private theorem rec_0_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 640 128 = 2049287528493536985938209640064 := by decide +kernel
private theorem rec_0_14_2369_0_part6 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 768 128 = 1923623171278671567903121362560 := by decide +kernel
private theorem rec_0_14_2369_0_part7 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 896 128 = 1800455600880839563794489478784 := by decide +kernel
private theorem rec_0_14_2369_0_part8 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1024 128 = 1679759725942885691203962261120 := by decide +kernel
private theorem rec_0_14_2369_0_part9 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1152 128 = 1561510477187303928988114914944 := by decide +kernel
private theorem rec_0_14_2369_0_part10 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1280 128 = 1445682807409952093077570408064 := by decide +kernel
private theorem rec_0_14_2369_0_part11 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1408 128 = 1332251691473766412286120300160 := by decide +kernel
private theorem rec_0_14_2369_0_part12 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1536 128 = 1221192126586905048708213359630 := by decide +kernel
private theorem rec_0_14_2369_0_part13 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1664 128 = 1112479223300538931870503654462 := by decide +kernel
private theorem rec_0_14_2369_0_part14 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1792 128 = 1006088194850093414319793483218 := by decide +kernel
private theorem rec_0_14_2369_0_part15 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1920 128 = 901994050503479714903814683978 := by decide +kernel
private theorem rec_0_14_2369_0_part16 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2048 128 = 800171789936490564427538673611 := by decide +kernel
private theorem rec_0_14_2369_0_part17 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2176 128 = 700596434764223453810674482670 := by decide +kernel
private theorem rec_0_14_2369_0_part18 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2304 128 = 603243028599040261661277235064 := by decide +kernel
private theorem rec_0_14_2369_0_part19 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2432 128 = 508086637309390660305565611926 := by decide +kernel
private theorem rec_0_14_2369_0_part20 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2560 128 = 415102348851590931822022869510 := by decide +kernel
private theorem rec_0_14_2369_0_part21 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2688 128 = 324265273175508697785576606957 := by decide +kernel
private theorem rec_0_14_2369_0_part22 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2816 128 = 235550542314560642455853352176 := by decide +kernel
private theorem rec_0_14_2369_0_part23 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2944 128 = 148933310467151163798070548728 := by decide +kernel
private theorem rec_0_14_2369_0_part24 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 3072 128 = 64388753816669781226443661518 := by decide +kernel
private theorem rec_0_14_2369_0_part25 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 3200 35 = 3157642107258806412723439458 := by decide +kernel
private theorem rec_0_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 128 256 = 5018927991744765719139934133504 :=
  phaseBlock_append rec_0_14_2369_0_part1 rec_0_14_2369_0_part2 rfl rfl rfl
private theorem rec_0_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 0 384 = 7734868852435977625038402333568 :=
  phaseBlock_append rec_0_14_2369_0_part0 rec_0_14_2369_0_join0 rfl rfl rfl
private theorem rec_0_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 512 256 = 4226761314462062771702121782528 :=
  phaseBlock_append rec_0_14_2369_0_part4 rec_0_14_2369_0_part5 rfl rfl rfl
private theorem rec_0_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 384 384 = 6534968393701010816593193757568 :=
  phaseBlock_append rec_0_14_2369_0_part3 rec_0_14_2369_0_join2 rfl rfl rfl
private theorem rec_0_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 0 768 = 14269837246136988441631596091136 :=
  phaseBlock_append rec_0_14_2369_0_join1 rec_0_14_2369_0_join3 rfl rfl rfl
private theorem rec_0_14_2369_0_join5 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 896 256 = 3480215326823725254998451739904 :=
  phaseBlock_append rec_0_14_2369_0_part7 rec_0_14_2369_0_part8 rfl rfl rfl
private theorem rec_0_14_2369_0_join6 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 768 384 = 5403838498102396822901573102464 :=
  phaseBlock_append rec_0_14_2369_0_part6 rec_0_14_2369_0_join5 rfl rfl rfl
private theorem rec_0_14_2369_0_join7 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1152 256 = 3007193284597256022065685323008 :=
  phaseBlock_append rec_0_14_2369_0_part9 rec_0_14_2369_0_part10 rfl rfl rfl
private theorem rec_0_14_2369_0_join8 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1408 256 = 2553443818060671460994333659790 :=
  phaseBlock_append rec_0_14_2369_0_part11 rec_0_14_2369_0_part12 rfl rfl rfl
private theorem rec_0_14_2369_0_join9 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1152 512 = 5560637102657927483060018982798 :=
  phaseBlock_append rec_0_14_2369_0_join7 rec_0_14_2369_0_join8 rfl rfl rfl
private theorem rec_0_14_2369_0_join10 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 768 896 = 10964475600760324305961592085262 :=
  phaseBlock_append rec_0_14_2369_0_join6 rec_0_14_2369_0_join9 rfl rfl rfl
private theorem rec_0_14_2369_0_join11 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 0 1664 = 25234312846897312747593188176398 :=
  phaseBlock_append rec_0_14_2369_0_join4 rec_0_14_2369_0_join10 rfl rfl rfl
private theorem rec_0_14_2369_0_join12 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1792 256 = 1908082245353573129223608167196 :=
  phaseBlock_append rec_0_14_2369_0_part14 rec_0_14_2369_0_part15 rfl rfl rfl
private theorem rec_0_14_2369_0_join13 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1664 384 = 3020561468654112061094111821658 :=
  phaseBlock_append rec_0_14_2369_0_part13 rec_0_14_2369_0_join12 rfl rfl rfl
private theorem rec_0_14_2369_0_join14 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2176 256 = 1303839463363263715471951717734 :=
  phaseBlock_append rec_0_14_2369_0_part17 rec_0_14_2369_0_part18 rfl rfl rfl
private theorem rec_0_14_2369_0_join15 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2048 384 = 2104011253299754279899490391345 :=
  phaseBlock_append rec_0_14_2369_0_part16 rec_0_14_2369_0_join14 rfl rfl rfl
private theorem rec_0_14_2369_0_join16 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1664 768 = 5124572721953866340993602213003 :=
  phaseBlock_append rec_0_14_2369_0_join13 rec_0_14_2369_0_join15 rfl rfl rfl
private theorem rec_0_14_2369_0_join17 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2560 256 = 739367622027099629607599476467 :=
  phaseBlock_append rec_0_14_2369_0_part20 rec_0_14_2369_0_part21 rfl rfl rfl
private theorem rec_0_14_2369_0_join18 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2432 384 = 1247454259336490289913165088393 :=
  phaseBlock_append rec_0_14_2369_0_part19 rec_0_14_2369_0_join17 rfl rfl rfl
private theorem rec_0_14_2369_0_join19 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2816 256 = 384483852781711806253923900904 :=
  phaseBlock_append rec_0_14_2369_0_part22 rec_0_14_2369_0_part23 rfl rfl rfl
private theorem rec_0_14_2369_0_join20 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 3072 163 = 67546395923928587639167100976 :=
  phaseBlock_append rec_0_14_2369_0_part24 rec_0_14_2369_0_part25 rfl rfl rfl
private theorem rec_0_14_2369_0_join21 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2816 419 = 452030248705640393893091001880 :=
  phaseBlock_append rec_0_14_2369_0_join19 rec_0_14_2369_0_join20 rfl rfl rfl
private theorem rec_0_14_2369_0_join22 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 2432 803 = 1699484508042130683806256090273 :=
  phaseBlock_append rec_0_14_2369_0_join18 rec_0_14_2369_0_join21 rfl rfl rfl
private theorem rec_0_14_2369_0_join23 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 1664 1571 = 6824057229995997024799858303276 :=
  phaseBlock_append rec_0_14_2369_0_join16 rec_0_14_2369_0_join22 rfl rfl rfl
private theorem rec_0_14_2369_0_join24 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 0) 0 3235 = 32058370076893309772393046479674 :=
  phaseBlock_append rec_0_14_2369_0_join11 rec_0_14_2369_0_join23 rfl rfl rfl

private theorem rec_0_14_2369_0 : fastPhase (bank 0 14).shape 179798 2369 76 1 0 1 0 = 32058370076893309772393046479674 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_0_14_2369_0_join24

private theorem rec_0_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 0 128 = 2714863616335683173875686737856 := by decide +kernel
private theorem rec_0_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 128 128 = 2576358078318106858081726146496 := by decide +kernel
private theorem rec_0_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 256 128 = 2440474924726595922568182941632 := by decide +kernel
private theorem rec_0_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 384 128 = 2307188953879963695187806054336 := by decide +kernel
private theorem rec_0_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 512 128 = 2176474986208051757914818283456 := by decide +kernel
private theorem rec_0_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 640 128 = 2048307864245444522654037125056 := by decide +kernel
private theorem rec_0_14_2369_1_part6 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 768 128 = 1922662452625183807049995601856 := by decide +kernel
private theorem rec_0_14_2369_1_part7 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 896 128 = 1799513638072483410296063092672 := by decide +kernel
private theorem rec_0_14_2369_1_part8 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1024 128 = 1678836329398443688943566161856 := by decide +kernel
private theorem rec_0_14_2369_1_part9 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1152 128 = 1560605457493766132710909388736 := by decide +kernel
private theorem rec_0_14_2369_1_part10 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1280 128 = 1444795975322467940292696197056 := by decide +kernel
private theorem rec_0_14_2369_1_part11 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1408 128 = 1331382857915596595168849684416 := by decide +kernel
private theorem rec_0_14_2369_1_part12 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1536 128 = 1220341102649187030516332160030 := by decide +kernel
private theorem rec_0_14_2369_1_part13 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1664 128 = 1111645820180225161946976268555 := by decide +kernel
private theorem rec_0_14_2369_1_part14 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1792 128 = 1005272223770452209210464687006 := by decide +kernel
private theorem rec_0_14_2369_1_part15 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1920 128 = 901195322837037228967918431728 := by decide +kernel
private theorem rec_0_14_2369_1_part16 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2048 128 = 799390117223837035125713972596 := by decide +kernel
private theorem rec_0_14_2369_1_part17 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2176 128 = 699831628714064700945755141070 := by decide +kernel
private theorem rec_0_14_2369_1_part18 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2304 128 = 602494901088269209649060527125 := by decide +kernel
private theorem rec_0_14_2369_1_part19 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2432 128 = 507355000382906109635644808322 := by decide +kernel
private theorem rec_0_14_2369_1_part20 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2560 128 = 414387014722205736894436931716 := by decide +kernel
private theorem rec_0_14_2369_1_part21 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2688 128 = 323566054224010079581415027378 := by decide +kernel
private theorem rec_0_14_2369_1_part22 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2816 128 = 234867251089721967403708655828 := by decide +kernel
private theorem rec_0_14_2369_1_part23 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2944 128 = 148265759685470801622240672610 := by decide +kernel
private theorem rec_0_14_2369_1_part24 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 3072 128 = 63736756362431000348726326850 := by decide +kernel
private theorem rec_0_14_2369_1_part25 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 3200 35 = 2982044761582871022368748676 := by decide +kernel
private theorem rec_0_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 128 256 = 5016833003044702780649909088128 :=
  phaseBlock_append rec_0_14_2369_1_part1 rec_0_14_2369_1_part2 rfl rfl rfl
private theorem rec_0_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 0 384 = 7731696619380385954525595825984 :=
  phaseBlock_append rec_0_14_2369_1_part0 rec_0_14_2369_1_join0 rfl rfl rfl
private theorem rec_0_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 512 256 = 4224782850453496280568855408512 :=
  phaseBlock_append rec_0_14_2369_1_part4 rec_0_14_2369_1_part5 rfl rfl rfl
private theorem rec_0_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 384 384 = 6531971804333459975756661462848 :=
  phaseBlock_append rec_0_14_2369_1_part3 rec_0_14_2369_1_join2 rfl rfl rfl
private theorem rec_0_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 0 768 = 14263668423713845930282257288832 :=
  phaseBlock_append rec_0_14_2369_1_join1 rec_0_14_2369_1_join3 rfl rfl rfl
private theorem rec_0_14_2369_1_join5 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 896 256 = 3478349967470927099239629254528 :=
  phaseBlock_append rec_0_14_2369_1_part7 rec_0_14_2369_1_part8 rfl rfl rfl
private theorem rec_0_14_2369_1_join6 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 768 384 = 5401012420096110906289624856384 :=
  phaseBlock_append rec_0_14_2369_1_part6 rec_0_14_2369_1_join5 rfl rfl rfl
private theorem rec_0_14_2369_1_join7 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1152 256 = 3005401432816234073003605585792 :=
  phaseBlock_append rec_0_14_2369_1_part9 rec_0_14_2369_1_part10 rfl rfl rfl
private theorem rec_0_14_2369_1_join8 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1408 256 = 2551723960564783625685181844446 :=
  phaseBlock_append rec_0_14_2369_1_part11 rec_0_14_2369_1_part12 rfl rfl rfl
private theorem rec_0_14_2369_1_join9 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1152 512 = 5557125393381017698688787430238 :=
  phaseBlock_append rec_0_14_2369_1_join7 rec_0_14_2369_1_join8 rfl rfl rfl
private theorem rec_0_14_2369_1_join10 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 768 896 = 10958137813477128604978412286622 :=
  phaseBlock_append rec_0_14_2369_1_join6 rec_0_14_2369_1_join9 rfl rfl rfl
private theorem rec_0_14_2369_1_join11 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 0 1664 = 25221806237190974535260669575454 :=
  phaseBlock_append rec_0_14_2369_1_join4 rec_0_14_2369_1_join10 rfl rfl rfl
private theorem rec_0_14_2369_1_join12 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1792 256 = 1906467546607489438178383118734 :=
  phaseBlock_append rec_0_14_2369_1_part14 rec_0_14_2369_1_part15 rfl rfl rfl
private theorem rec_0_14_2369_1_join13 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1664 384 = 3018113366787714600125359387289 :=
  phaseBlock_append rec_0_14_2369_1_part13 rec_0_14_2369_1_join12 rfl rfl rfl
private theorem rec_0_14_2369_1_join14 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2176 256 = 1302326529802333910594815668195 :=
  phaseBlock_append rec_0_14_2369_1_part17 rec_0_14_2369_1_part18 rfl rfl rfl
private theorem rec_0_14_2369_1_join15 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2048 384 = 2101716647026170945720529640791 :=
  phaseBlock_append rec_0_14_2369_1_part16 rec_0_14_2369_1_join14 rfl rfl rfl
private theorem rec_0_14_2369_1_join16 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1664 768 = 5119830013813885545845889028080 :=
  phaseBlock_append rec_0_14_2369_1_join13 rec_0_14_2369_1_join15 rfl rfl rfl
private theorem rec_0_14_2369_1_join17 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2560 256 = 737953068946215816475851959094 :=
  phaseBlock_append rec_0_14_2369_1_part20 rec_0_14_2369_1_part21 rfl rfl rfl
private theorem rec_0_14_2369_1_join18 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2432 384 = 1245308069329121926111496767416 :=
  phaseBlock_append rec_0_14_2369_1_part19 rec_0_14_2369_1_join17 rfl rfl rfl
private theorem rec_0_14_2369_1_join19 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2816 256 = 383133010775192769025949328438 :=
  phaseBlock_append rec_0_14_2369_1_part22 rec_0_14_2369_1_part23 rfl rfl rfl
private theorem rec_0_14_2369_1_join20 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 3072 163 = 66718801124013871371095075526 :=
  phaseBlock_append rec_0_14_2369_1_part24 rec_0_14_2369_1_part25 rfl rfl rfl
private theorem rec_0_14_2369_1_join21 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2816 419 = 449851811899206640397044403964 :=
  phaseBlock_append rec_0_14_2369_1_join19 rec_0_14_2369_1_join20 rfl rfl rfl
private theorem rec_0_14_2369_1_join22 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 2432 803 = 1695159881228328566508541171380 :=
  phaseBlock_append rec_0_14_2369_1_join18 rec_0_14_2369_1_join21 rfl rfl rfl
private theorem rec_0_14_2369_1_join23 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 1664 1571 = 6814989895042214112354430199460 :=
  phaseBlock_append rec_0_14_2369_1_join16 rec_0_14_2369_1_join22 rfl rfl rfl
private theorem rec_0_14_2369_1_join24 :
    phaseBlock (fastLayerG (bank 0 14).shape 179798 2369 76 1 0 1 1) 0 3235 = 32036796132233188647615099774914 :=
  phaseBlock_append rec_0_14_2369_1_join11 rec_0_14_2369_1_join23 rfl rfl rfl

private theorem rec_0_14_2369_1 : fastPhase (bank 0 14).shape 179798 2369 76 1 0 1 1 = 32036796132233188647615099774914 :=
  phase_of_blockG (n := 3235) (by decide +kernel) rec_0_14_2369_1_join24

theorem receipt_0_14 : Checked (bank 0 14) 76 0 1 := by
  refine checked_from_values (bank 0 14) 76 0 1
    (P3_7_1.checked (bank 0 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_14605_3234)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_14_2368_0 rec_0_14_2368_1 rec_0_14_2369_0 rec_0_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 0 128 = 10961751800010571427813840774880 := by decide +kernel
private theorem rec_0_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 128 128 = 10527624606605790075160542787296 := by decide +kernel
private theorem rec_0_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 256 128 = 10099875450087021713473254754016 := by decide +kernel
private theorem rec_0_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 384 128 = 9678456936813007678917604660960 := by decide +kernel
private theorem rec_0_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 512 128 = 9263321703496252124354256512736 := by decide +kernel
private theorem rec_0_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 640 128 = 8854422417196736815050356717280 := by decide +kernel
private theorem rec_0_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 768 128 = 8451711775315635924390980470496 := by decide +kernel
private theorem rec_0_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 896 128 = 8055142505589030829590578140896 := by decide +kernel
private theorem rec_0_15_2368_0_part8 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1024 128 = 7664667366081624907404421654240 := by decide +kernel
private theorem rec_0_15_2368_0_part9 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1152 128 = 7280239145180458329840050878176 := by decide +kernel
private theorem rec_0_15_2368_0_part10 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1280 128 = 6901810661588622859868720006880 := by decide +kernel
private theorem rec_0_15_2368_0_part11 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1408 128 = 6529334764318976647136843945696 := by decide +kernel
private theorem rec_0_15_2368_0_part12 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1536 128 = 6162764332687859023677444695776 := by decide +kernel
private theorem rec_0_15_2368_0_part13 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1664 128 = 5802052276308805299621597738720 := by decide +kernel
private theorem rec_0_15_2368_0_part14 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1792 128 = 5447151535086261558909878421216 := by decide +kernel
private theorem rec_0_15_2368_0_part15 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1920 128 = 5098015079209299455003808339680 := by decide +kernel
private theorem rec_0_15_2368_0_part16 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2048 128 = 4754595940976878704847944408544 := by decide +kernel
private theorem rec_0_15_2368_0_part17 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2176 128 = 4416847585292728408108122328489 := by decide +kernel
private theorem rec_0_15_2368_0_part18 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2304 128 = 4084723285880458988355038395752 := by decide +kernel
private theorem rec_0_15_2368_0_part19 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2432 128 = 3758175979639384084090823307602 := by decide +kernel
private theorem rec_0_15_2368_0_part20 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2560 128 = 3437158626938408006535991706228 := by decide +kernel
private theorem rec_0_15_2368_0_part21 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2688 128 = 3121624218083287818645358052113 := by decide +kernel
private theorem rec_0_15_2368_0_part22 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2816 128 = 2811525773432366915560831828512 := by decide +kernel
private theorem rec_0_15_2368_0_part23 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2944 128 = 2506816344167785711032043787054 := by decide +kernel
private theorem rec_0_15_2368_0_part24 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3072 128 = 2207449011756025926722722296065 := by decide +kernel
private theorem rec_0_15_2368_0_part25 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3200 128 = 1913376887748759659043113649924 := by decide +kernel
private theorem rec_0_15_2368_0_part26 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3328 128 = 1624553114039132464788179624957 := by decide +kernel
private theorem rec_0_15_2368_0_part27 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3456 128 = 1340930863146435549834073401330 := by decide +kernel
private theorem rec_0_15_2368_0_part28 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3584 128 = 1062463337656544221496966786994 := by decide +kernel
private theorem rec_0_15_2368_0_part29 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3712 128 = 789103770390815019008517033002 := by decide +kernel
private theorem rec_0_15_2368_0_part30 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3840 128 = 520805424685988789999471757586 := by decide +kernel
private theorem rec_0_15_2368_0_part31 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3968 128 = 257521594069456434806084403078 := by decide +kernel
private theorem rec_0_15_2368_0_part32 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 4096 63 = 31583632657021375683336567441 := by decide +kernel
private theorem rec_0_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 0 256 = 21489376406616361502974383562176 :=
  phaseBlock_append rec_0_15_2368_0_part0 rec_0_15_2368_0_part1 rfl rfl rfl
private theorem rec_0_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 256 256 = 19778332386900029392390859414976 :=
  phaseBlock_append rec_0_15_2368_0_part2 rec_0_15_2368_0_part3 rfl rfl rfl
private theorem rec_0_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 0 512 = 41267708793516390895365242977152 :=
  phaseBlock_append rec_0_15_2368_0_join0 rec_0_15_2368_0_join1 rfl rfl rfl
private theorem rec_0_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 512 256 = 18117744120692988939404613230016 :=
  phaseBlock_append rec_0_15_2368_0_part4 rec_0_15_2368_0_part5 rfl rfl rfl
private theorem rec_0_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 768 256 = 16506854280904666753981558611392 :=
  phaseBlock_append rec_0_15_2368_0_part6 rec_0_15_2368_0_part7 rfl rfl rfl
private theorem rec_0_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 512 512 = 34624598401597655693386171841408 :=
  phaseBlock_append rec_0_15_2368_0_join3 rec_0_15_2368_0_join4 rfl rfl rfl
private theorem rec_0_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 0 1024 = 75892307195114046588751414818560 :=
  phaseBlock_append rec_0_15_2368_0_join2 rec_0_15_2368_0_join5 rfl rfl rfl
private theorem rec_0_15_2368_0_join7 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1024 256 = 14944906511262083237244472532416 :=
  phaseBlock_append rec_0_15_2368_0_part8 rec_0_15_2368_0_part9 rfl rfl rfl
private theorem rec_0_15_2368_0_join8 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1280 256 = 13431145425907599507005563952576 :=
  phaseBlock_append rec_0_15_2368_0_part10 rec_0_15_2368_0_part11 rfl rfl rfl
private theorem rec_0_15_2368_0_join9 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1024 512 = 28376051937169682744250036484992 :=
  phaseBlock_append rec_0_15_2368_0_join7 rec_0_15_2368_0_join8 rfl rfl rfl
private theorem rec_0_15_2368_0_join10 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1536 256 = 11964816608996664323299042434496 :=
  phaseBlock_append rec_0_15_2368_0_part12 rec_0_15_2368_0_part13 rfl rfl rfl
private theorem rec_0_15_2368_0_join11 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1792 256 = 10545166614295561013913686760896 :=
  phaseBlock_append rec_0_15_2368_0_part14 rec_0_15_2368_0_part15 rfl rfl rfl
private theorem rec_0_15_2368_0_join12 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1536 512 = 22509983223292225337212729195392 :=
  phaseBlock_append rec_0_15_2368_0_join10 rec_0_15_2368_0_join11 rfl rfl rfl
private theorem rec_0_15_2368_0_join13 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 1024 1024 = 50886035160461908081462765680384 :=
  phaseBlock_append rec_0_15_2368_0_join9 rec_0_15_2368_0_join12 rfl rfl rfl
private theorem rec_0_15_2368_0_join14 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 0 2048 = 126778342355575954670214180498944 :=
  phaseBlock_append rec_0_15_2368_0_join6 rec_0_15_2368_0_join13 rfl rfl rfl
private theorem rec_0_15_2368_0_join15 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2048 256 = 9171443526269607112956066737033 :=
  phaseBlock_append rec_0_15_2368_0_part16 rec_0_15_2368_0_part17 rfl rfl rfl
private theorem rec_0_15_2368_0_join16 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2304 256 = 7842899265519843072445861703354 :=
  phaseBlock_append rec_0_15_2368_0_part18 rec_0_15_2368_0_part19 rfl rfl rfl
private theorem rec_0_15_2368_0_join17 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2048 512 = 17014342791789450185401928440387 :=
  phaseBlock_append rec_0_15_2368_0_join15 rec_0_15_2368_0_join16 rfl rfl rfl
private theorem rec_0_15_2368_0_join18 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2560 256 = 6558782845021695825181349758341 :=
  phaseBlock_append rec_0_15_2368_0_part20 rec_0_15_2368_0_part21 rfl rfl rfl
private theorem rec_0_15_2368_0_join19 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2816 256 = 5318342117600152626592875615566 :=
  phaseBlock_append rec_0_15_2368_0_part22 rec_0_15_2368_0_part23 rfl rfl rfl
private theorem rec_0_15_2368_0_join20 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2560 512 = 11877124962621848451774225373907 :=
  phaseBlock_append rec_0_15_2368_0_join18 rec_0_15_2368_0_join19 rfl rfl rfl
private theorem rec_0_15_2368_0_join21 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2048 1024 = 28891467754411298637176153814294 :=
  phaseBlock_append rec_0_15_2368_0_join17 rec_0_15_2368_0_join20 rfl rfl rfl
private theorem rec_0_15_2368_0_join22 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3072 256 = 4120825899504785585765835945989 :=
  phaseBlock_append rec_0_15_2368_0_part24 rec_0_15_2368_0_part25 rfl rfl rfl
private theorem rec_0_15_2368_0_join23 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3328 256 = 2965483977185568014622253026287 :=
  phaseBlock_append rec_0_15_2368_0_part26 rec_0_15_2368_0_part27 rfl rfl rfl
private theorem rec_0_15_2368_0_join24 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3072 512 = 7086309876690353600388088972276 :=
  phaseBlock_append rec_0_15_2368_0_join22 rec_0_15_2368_0_join23 rfl rfl rfl
private theorem rec_0_15_2368_0_join25 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3584 256 = 1851567108047359240505483819996 :=
  phaseBlock_append rec_0_15_2368_0_part28 rec_0_15_2368_0_part29 rfl rfl rfl
private theorem rec_0_15_2368_0_join26 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3968 191 = 289105226726477810489420970519 :=
  phaseBlock_append rec_0_15_2368_0_part31 rec_0_15_2368_0_part32 rfl rfl rfl
private theorem rec_0_15_2368_0_join27 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3840 319 = 809910651412466600488892728105 :=
  phaseBlock_append rec_0_15_2368_0_part30 rec_0_15_2368_0_join26 rfl rfl rfl
private theorem rec_0_15_2368_0_join28 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3584 575 = 2661477759459825840994376548101 :=
  phaseBlock_append rec_0_15_2368_0_join25 rec_0_15_2368_0_join27 rfl rfl rfl
private theorem rec_0_15_2368_0_join29 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 3072 1087 = 9747787636150179441382465520377 :=
  phaseBlock_append rec_0_15_2368_0_join24 rec_0_15_2368_0_join28 rfl rfl rfl
private theorem rec_0_15_2368_0_join30 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 2048 2111 = 38639255390561478078558619334671 :=
  phaseBlock_append rec_0_15_2368_0_join21 rec_0_15_2368_0_join29 rfl rfl rfl
private theorem rec_0_15_2368_0_join31 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 0) 0 4159 = 165417597746137432748772799833615 :=
  phaseBlock_append rec_0_15_2368_0_join14 rec_0_15_2368_0_join30 rfl rfl rfl

private theorem rec_0_15_2368_0 : fastPhase (bank 0 15).shape 179798 2368 105 1 0 1 0 = 165417597746137432748772799833615 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_0_15_2368_0_join31

private theorem rec_0_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 0 128 = 10958383057070059583036804248032 := by decide +kernel
private theorem rec_0_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 128 128 = 10524304198889049728858765558240 := by decide +kernel
private theorem rec_0_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 256 128 = 10096603019228510763899138200032 := by decide +kernel
private theorem rec_0_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 384 128 = 9675232124678484636962452480480 := by decide +kernel
private theorem rec_0_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 512 128 = 9260144152182727986756095865312 := by decide +kernel
private theorem rec_0_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 640 128 = 8851291769032426937601759363552 := by decide +kernel
private theorem rec_0_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 768 128 = 8448627672859911895146883912160 := by decide +kernel
private theorem rec_0_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 896 128 = 8052104591632372342076106760672 := by decide +kernel
private theorem rec_0_15_2368_1_part8 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1024 128 = 7661675283645571633822707855840 := by decide +kernel
private theorem rec_0_15_2368_1_part9 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1152 128 = 7277292537517561794280056226272 := by decide +kernel
private theorem rec_0_15_2368_1_part10 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1280 128 = 6898909172182398311513056367072 := by decide +kernel
private theorem rec_0_15_2368_1_part11 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1408 128 = 6526478036883854933469594624480 := by decide +kernel
private theorem rec_0_15_2368_1_part12 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1536 128 = 6159952011169138463691985580512 := by decide +kernel
private theorem rec_0_15_2368_1_part13 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1664 128 = 5799284004882603557028418437600 := by decide +kernel
private theorem rec_0_15_2368_1_part14 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1792 128 = 5444426958159467515344403403232 := by decide +kernel
private theorem rec_0_15_2368_1_part15 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1920 128 = 5095333841419525083234218074592 := by decide +kernel
private theorem rec_0_15_2368_1_part16 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2048 128 = 4751957687176342493582087955817 := by decide +kernel
private theorem rec_0_15_2368_1_part17 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2176 128 = 4414251960332505117376226086698 := by decide +kernel
private theorem rec_0_15_2368_1_part18 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2304 128 = 4082169934672684877957215044051 := by decide +kernel
private theorem rec_0_15_2368_1_part19 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2432 128 = 3755664547323761750031255996035 := by decide +kernel
private theorem rec_0_15_2368_1_part20 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2560 128 = 3434688758885323531853920912905 := by decide +kernel
private theorem rec_0_15_2368_1_part21 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2688 128 = 3119195559893962347068320220212 := by decide +kernel
private theorem rec_0_15_2368_1_part22 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2816 128 = 2809137970939043685314068282107 := by decide +kernel
private theorem rec_0_15_2368_1_part23 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2944 128 = 2504469043433379362039812577928 := by decide +kernel
private theorem rec_0_15_2368_1_part24 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3072 128 = 2205141859074043772931998595260 := by decide +kernel
private theorem rec_0_15_2368_1_part25 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3200 128 = 1911109529643462408068601320764 := by decide +kernel
private theorem rec_0_15_2368_1_part26 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3328 128 = 1622325197265553310349838788486 := by decide +kernel
private theorem rec_0_15_2368_1_part27 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3456 128 = 1338742034689951958483338188561 := by decide +kernel
private theorem rec_0_15_2368_1_part28 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3584 128 = 1060313244733054759663153408853 := by decide +kernel
private theorem rec_0_15_2368_1_part29 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3712 128 = 786992060446917481711055972349 := by decide +kernel
private theorem rec_0_15_2368_1_part30 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3840 128 = 518731745398557563024553965989 := by decide +kernel
private theorem rec_0_15_2368_1_part31 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3968 128 = 255485593345654547557315348416 := by decide +kernel
private theorem rec_0_15_2368_1_part32 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 4096 63 = 30595267450634203314045596919 := by decide +kernel
private theorem rec_0_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 0 256 = 21482687255959109311895569806272 :=
  phaseBlock_append rec_0_15_2368_1_part0 rec_0_15_2368_1_part1 rfl rfl rfl
private theorem rec_0_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 256 256 = 19771835143906995400861590680512 :=
  phaseBlock_append rec_0_15_2368_1_part2 rec_0_15_2368_1_part3 rfl rfl rfl
private theorem rec_0_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 0 512 = 41254522399866104712757160486784 :=
  phaseBlock_append rec_0_15_2368_1_join0 rec_0_15_2368_1_join1 rfl rfl rfl
private theorem rec_0_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 512 256 = 18111435921215154924357855228864 :=
  phaseBlock_append rec_0_15_2368_1_part4 rec_0_15_2368_1_part5 rfl rfl rfl
private theorem rec_0_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 768 256 = 16500732264492284237222990672832 :=
  phaseBlock_append rec_0_15_2368_1_part6 rec_0_15_2368_1_part7 rfl rfl rfl
private theorem rec_0_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 512 512 = 34612168185707439161580845901696 :=
  phaseBlock_append rec_0_15_2368_1_join3 rec_0_15_2368_1_join4 rfl rfl rfl
private theorem rec_0_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 0 1024 = 75866690585573543874338006388480 :=
  phaseBlock_append rec_0_15_2368_1_join2 rec_0_15_2368_1_join5 rfl rfl rfl
private theorem rec_0_15_2368_1_join7 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1024 256 = 14938967821163133428102764082112 :=
  phaseBlock_append rec_0_15_2368_1_part8 rec_0_15_2368_1_part9 rfl rfl rfl
private theorem rec_0_15_2368_1_join8 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1280 256 = 13425387209066253244982650991552 :=
  phaseBlock_append rec_0_15_2368_1_part10 rec_0_15_2368_1_part11 rfl rfl rfl
private theorem rec_0_15_2368_1_join9 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1024 512 = 28364355030229386673085415073664 :=
  phaseBlock_append rec_0_15_2368_1_join7 rec_0_15_2368_1_join8 rfl rfl rfl
private theorem rec_0_15_2368_1_join10 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1536 256 = 11959236016051742020720404018112 :=
  phaseBlock_append rec_0_15_2368_1_part12 rec_0_15_2368_1_part13 rfl rfl rfl
private theorem rec_0_15_2368_1_join11 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1792 256 = 10539760799578992598578621477824 :=
  phaseBlock_append rec_0_15_2368_1_part14 rec_0_15_2368_1_part15 rfl rfl rfl
private theorem rec_0_15_2368_1_join12 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1536 512 = 22498996815630734619299025495936 :=
  phaseBlock_append rec_0_15_2368_1_join10 rec_0_15_2368_1_join11 rfl rfl rfl
private theorem rec_0_15_2368_1_join13 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 1024 1024 = 50863351845860121292384440569600 :=
  phaseBlock_append rec_0_15_2368_1_join9 rec_0_15_2368_1_join12 rfl rfl rfl
private theorem rec_0_15_2368_1_join14 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 0 2048 = 126730042431433665166722446958080 :=
  phaseBlock_append rec_0_15_2368_1_join6 rec_0_15_2368_1_join13 rfl rfl rfl
private theorem rec_0_15_2368_1_join15 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2048 256 = 9166209647508847610958314042515 :=
  phaseBlock_append rec_0_15_2368_1_part16 rec_0_15_2368_1_part17 rfl rfl rfl
private theorem rec_0_15_2368_1_join16 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2304 256 = 7837834481996446627988471040086 :=
  phaseBlock_append rec_0_15_2368_1_part18 rec_0_15_2368_1_part19 rfl rfl rfl
private theorem rec_0_15_2368_1_join17 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2048 512 = 17004044129505294238946785082601 :=
  phaseBlock_append rec_0_15_2368_1_join15 rec_0_15_2368_1_join16 rfl rfl rfl
private theorem rec_0_15_2368_1_join18 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2560 256 = 6553884318779285878922241133117 :=
  phaseBlock_append rec_0_15_2368_1_part20 rec_0_15_2368_1_part21 rfl rfl rfl
private theorem rec_0_15_2368_1_join19 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2816 256 = 5313607014372423047353880860035 :=
  phaseBlock_append rec_0_15_2368_1_part22 rec_0_15_2368_1_part23 rfl rfl rfl
private theorem rec_0_15_2368_1_join20 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2560 512 = 11867491333151708926276121993152 :=
  phaseBlock_append rec_0_15_2368_1_join18 rec_0_15_2368_1_join19 rfl rfl rfl
private theorem rec_0_15_2368_1_join21 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2048 1024 = 28871535462657003165222907075753 :=
  phaseBlock_append rec_0_15_2368_1_join17 rec_0_15_2368_1_join20 rfl rfl rfl
private theorem rec_0_15_2368_1_join22 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3072 256 = 4116251388717506181000599916024 :=
  phaseBlock_append rec_0_15_2368_1_part24 rec_0_15_2368_1_part25 rfl rfl rfl
private theorem rec_0_15_2368_1_join23 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3328 256 = 2961067231955505268833176977047 :=
  phaseBlock_append rec_0_15_2368_1_part26 rec_0_15_2368_1_part27 rfl rfl rfl
private theorem rec_0_15_2368_1_join24 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3072 512 = 7077318620673011449833776893071 :=
  phaseBlock_append rec_0_15_2368_1_join22 rec_0_15_2368_1_join23 rfl rfl rfl
private theorem rec_0_15_2368_1_join25 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3584 256 = 1847305305179972241374209381202 :=
  phaseBlock_append rec_0_15_2368_1_part28 rec_0_15_2368_1_part29 rfl rfl rfl
private theorem rec_0_15_2368_1_join26 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3968 191 = 286080860796288750871360945335 :=
  phaseBlock_append rec_0_15_2368_1_part31 rec_0_15_2368_1_part32 rfl rfl rfl
private theorem rec_0_15_2368_1_join27 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3840 319 = 804812606194846313895914911324 :=
  phaseBlock_append rec_0_15_2368_1_part30 rec_0_15_2368_1_join26 rfl rfl rfl
private theorem rec_0_15_2368_1_join28 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3584 575 = 2652117911374818555270124292526 :=
  phaseBlock_append rec_0_15_2368_1_join25 rec_0_15_2368_1_join27 rfl rfl rfl
private theorem rec_0_15_2368_1_join29 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 3072 1087 = 9729436532047830005103901185597 :=
  phaseBlock_append rec_0_15_2368_1_join24 rec_0_15_2368_1_join28 rfl rfl rfl
private theorem rec_0_15_2368_1_join30 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 2048 2111 = 38600971994704833170326808261350 :=
  phaseBlock_append rec_0_15_2368_1_join21 rec_0_15_2368_1_join29 rfl rfl rfl
private theorem rec_0_15_2368_1_join31 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2368 105 1 0 1 1) 0 4159 = 165331014426138498337049255219430 :=
  phaseBlock_append rec_0_15_2368_1_join14 rec_0_15_2368_1_join30 rfl rfl rfl

private theorem rec_0_15_2368_1 : fastPhase (bank 0 15).shape 179798 2368 105 1 0 1 1 = 165331014426138498337049255219430 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_0_15_2368_1_join31

private theorem rec_0_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 0 128 = 10961853248448239116030487392320 := by decide +kernel
private theorem rec_0_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 128 128 = 10527720336171539721452626202688 := by decide +kernel
private theorem rec_0_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 256 128 = 10099965641514437066764272349248 := by decide +kernel
private theorem rec_0_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 384 128 = 9678541769197741293770367635520 := by decide +kernel
private theorem rec_0_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 512 128 = 9263401354297084011894719443008 := by decide +kernel
private theorem rec_0_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 640 128 = 8854497062236632873989121560640 := by decide +kernel
private theorem rec_0_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 768 128 = 8451781588782806152142475014208 := by decide +kernel
private theorem rec_0_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 896 128 = 8055207660037987313489908895808 := by decide +kernel
private theorem rec_0_15_2369_0_part8 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1024 128 = 7664728032434239596021901193280 := by decide +kernel
private theorem rec_0_15_2369_0_part9 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1152 128 = 7280295492727020584393399619648 := by decide +kernel
private theorem rec_0_15_2369_0_part10 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1280 128 = 6901862857988896785732942442560 := by decide +kernel
private theorem rec_0_15_2369_0_part11 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1408 128 = 6529382975603258205451779313728 := by decide +kernel
private theorem rec_0_15_2369_0_part12 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1536 128 = 6162808723258032923052992098368 := by decide +kernel
private theorem rec_0_15_2369_0_part13 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1664 128 = 5802093008939401667940615704640 := by decide +kernel
private theorem rec_0_15_2369_0_part14 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1792 128 = 5447188770925512395228758913088 := by decide +kernel
private theorem rec_0_15_2369_0_part15 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1920 128 = 5098048977780194861550725206080 := by decide +kernel
private theorem rec_0_15_2369_0_part16 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2048 128 = 4754626656558290225945852879541 := by decide +kernel
private theorem rec_0_15_2369_0_part17 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2176 128 = 4416875260893427504719665349432 := by decide +kernel
private theorem rec_0_15_2369_0_part18 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2304 128 = 4084748077476053067621479777601 := by decide +kernel
private theorem rec_0_15_2369_0_part19 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2432 128 = 3758198043414255836827670869233 := by decide +kernel
private theorem rec_0_15_2369_0_part20 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2560 128 = 3437178117199527815664471816967 := by decide +kernel
private theorem rec_0_15_2369_0_part21 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2688 128 = 3121641287279968531041833968413 := by decide +kernel
private theorem rec_0_15_2369_0_part22 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2816 128 = 2811540572289833398738476561750 := by decide +kernel
private theorem rec_0_15_2369_0_part23 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2944 128 = 2506829021792588995847153607625 := by decide +kernel
private theorem rec_0_15_2369_0_part24 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3072 128 = 2207459715386475891408633292335 := by decide +kernel
private theorem rec_0_15_2369_0_part25 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3200 128 = 1913385762791848680674929482891 := by decide +kernel
private theorem rec_0_15_2369_0_part26 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3328 128 = 1624560304328382739351660633197 := by decide +kernel
private theorem rec_0_15_2369_0_part27 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3456 128 = 1340936510677570770684476396788 := by decide +kernel
private theorem rec_0_15_2369_0_part28 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3584 128 = 1062467582645313248172199984599 := by decide +kernel
private theorem rec_0_15_2369_0_part29 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3712 128 = 789106751337609965599587657846 := by decide +kernel
private theorem rec_0_15_2369_0_part30 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3840 128 = 520807278363065007116549742489 := by decide +kernel
private theorem rec_0_15_2369_0_part31 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3968 128 = 257522455470134024941905466488 := by decide +kernel
private theorem rec_0_15_2369_0_part32 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 4096 63 = 31583732962698283910547332097 := by decide +kernel
private theorem rec_0_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 0 256 = 21489573584619778837483113595008 :=
  phaseBlock_append rec_0_15_2369_0_part0 rec_0_15_2369_0_part1 rfl rfl rfl
private theorem rec_0_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 256 256 = 19778507410712178360534639984768 :=
  phaseBlock_append rec_0_15_2369_0_part2 rec_0_15_2369_0_part3 rfl rfl rfl
private theorem rec_0_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 0 512 = 41268080995331957198017753579776 :=
  phaseBlock_append rec_0_15_2369_0_join0 rec_0_15_2369_0_join1 rfl rfl rfl
private theorem rec_0_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 512 256 = 18117898416533716885883841003648 :=
  phaseBlock_append rec_0_15_2369_0_part4 rec_0_15_2369_0_part5 rfl rfl rfl
private theorem rec_0_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 768 256 = 16506989248820793465632383910016 :=
  phaseBlock_append rec_0_15_2369_0_part6 rec_0_15_2369_0_part7 rfl rfl rfl
private theorem rec_0_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 512 512 = 34624887665354510351516224913664 :=
  phaseBlock_append rec_0_15_2369_0_join3 rec_0_15_2369_0_join4 rfl rfl rfl
private theorem rec_0_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 0 1024 = 75892968660686467549533978493440 :=
  phaseBlock_append rec_0_15_2369_0_join2 rec_0_15_2369_0_join5 rfl rfl rfl
private theorem rec_0_15_2369_0_join7 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1024 256 = 14945023525161260180415300812928 :=
  phaseBlock_append rec_0_15_2369_0_part8 rec_0_15_2369_0_part9 rfl rfl rfl
private theorem rec_0_15_2369_0_join8 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1280 256 = 13431245833592154991184721756288 :=
  phaseBlock_append rec_0_15_2369_0_part10 rec_0_15_2369_0_part11 rfl rfl rfl
private theorem rec_0_15_2369_0_join9 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1024 512 = 28376269358753415171600022569216 :=
  phaseBlock_append rec_0_15_2369_0_join7 rec_0_15_2369_0_join8 rfl rfl rfl
private theorem rec_0_15_2369_0_join10 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1536 256 = 11964901732197434590993607803008 :=
  phaseBlock_append rec_0_15_2369_0_part12 rec_0_15_2369_0_part13 rfl rfl rfl
private theorem rec_0_15_2369_0_join11 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1792 256 = 10545237748705707256779484119168 :=
  phaseBlock_append rec_0_15_2369_0_part14 rec_0_15_2369_0_part15 rfl rfl rfl
private theorem rec_0_15_2369_0_join12 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1536 512 = 22510139480903141847773091922176 :=
  phaseBlock_append rec_0_15_2369_0_join10 rec_0_15_2369_0_join11 rfl rfl rfl
private theorem rec_0_15_2369_0_join13 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 1024 1024 = 50886408839656557019373114491392 :=
  phaseBlock_append rec_0_15_2369_0_join9 rec_0_15_2369_0_join12 rfl rfl rfl
private theorem rec_0_15_2369_0_join14 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 0 2048 = 126779377500343024568907092984832 :=
  phaseBlock_append rec_0_15_2369_0_join6 rec_0_15_2369_0_join13 rfl rfl rfl
private theorem rec_0_15_2369_0_join15 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2048 256 = 9171501917451717730665518228973 :=
  phaseBlock_append rec_0_15_2369_0_part16 rec_0_15_2369_0_part17 rfl rfl rfl
private theorem rec_0_15_2369_0_join16 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2304 256 = 7842946120890308904449150646834 :=
  phaseBlock_append rec_0_15_2369_0_part18 rec_0_15_2369_0_part19 rfl rfl rfl
private theorem rec_0_15_2369_0_join17 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2048 512 = 17014448038342026635114668875807 :=
  phaseBlock_append rec_0_15_2369_0_join15 rec_0_15_2369_0_join16 rfl rfl rfl
private theorem rec_0_15_2369_0_join18 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2560 256 = 6558819404479496346706305785380 :=
  phaseBlock_append rec_0_15_2369_0_part20 rec_0_15_2369_0_part21 rfl rfl rfl
private theorem rec_0_15_2369_0_join19 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2816 256 = 5318369594082422394585630169375 :=
  phaseBlock_append rec_0_15_2369_0_part22 rec_0_15_2369_0_part23 rfl rfl rfl
private theorem rec_0_15_2369_0_join20 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2560 512 = 11877188998561918741291935954755 :=
  phaseBlock_append rec_0_15_2369_0_join18 rec_0_15_2369_0_join19 rfl rfl rfl
private theorem rec_0_15_2369_0_join21 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2048 1024 = 28891637036903945376406604830562 :=
  phaseBlock_append rec_0_15_2369_0_join17 rec_0_15_2369_0_join20 rfl rfl rfl
private theorem rec_0_15_2369_0_join22 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3072 256 = 4120845478178324572083562775226 :=
  phaseBlock_append rec_0_15_2369_0_part24 rec_0_15_2369_0_part25 rfl rfl rfl
private theorem rec_0_15_2369_0_join23 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3328 256 = 2965496815005953510036137029985 :=
  phaseBlock_append rec_0_15_2369_0_part26 rec_0_15_2369_0_part27 rfl rfl rfl
private theorem rec_0_15_2369_0_join24 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3072 512 = 7086342293184278082119699805211 :=
  phaseBlock_append rec_0_15_2369_0_join22 rec_0_15_2369_0_join23 rfl rfl rfl
private theorem rec_0_15_2369_0_join25 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3584 256 = 1851574333982923213771787642445 :=
  phaseBlock_append rec_0_15_2369_0_part28 rec_0_15_2369_0_part29 rfl rfl rfl
private theorem rec_0_15_2369_0_join26 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3968 191 = 289106188432832308852452798585 :=
  phaseBlock_append rec_0_15_2369_0_part31 rec_0_15_2369_0_part32 rfl rfl rfl
private theorem rec_0_15_2369_0_join27 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3840 319 = 809913466795897315969002541074 :=
  phaseBlock_append rec_0_15_2369_0_part30 rec_0_15_2369_0_join26 rfl rfl rfl
private theorem rec_0_15_2369_0_join28 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3584 575 = 2661487800778820529740790183519 :=
  phaseBlock_append rec_0_15_2369_0_join25 rec_0_15_2369_0_join27 rfl rfl rfl
private theorem rec_0_15_2369_0_join29 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 3072 1087 = 9747830093963098611860489988730 :=
  phaseBlock_append rec_0_15_2369_0_join24 rec_0_15_2369_0_join28 rfl rfl rfl
private theorem rec_0_15_2369_0_join30 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 2048 2111 = 38639467130867043988267094819292 :=
  phaseBlock_append rec_0_15_2369_0_join21 rec_0_15_2369_0_join29 rfl rfl rfl
private theorem rec_0_15_2369_0_join31 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 0) 0 4159 = 165418844631210068557174187804124 :=
  phaseBlock_append rec_0_15_2369_0_join14 rec_0_15_2369_0_join30 rfl rfl rfl

private theorem rec_0_15_2369_0 : fastPhase (bank 0 15).shape 179798 2369 105 1 0 1 0 = 165418844631210068557174187804124 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_0_15_2369_0_join31

private theorem rec_0_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 0 128 = 10958484480275259565975460651136 := by decide +kernel
private theorem rec_0_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 128 128 = 10524399903932491147442354593920 := by decide +kernel
private theorem rec_0_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 256 128 = 10096693186836050802447181815936 := by decide +kernel
private theorem rec_0_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 384 128 = 9675316933938055081270424707200 := by decide +kernel
private theorem rec_0_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 512 128 = 9260223780545393873713582317696 := by decide +kernel
private theorem rec_0_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 640 128 = 8851366392313444984908291186816 := by decide +kernel
private theorem rec_0_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 768 128 = 8448697465239788711125446172800 := by decide +kernel
private theorem rec_0_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 896 128 = 8052169725657922415584321282176 := by decide +kernel
private theorem rec_0_15_2369_1_part8 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1024 128 = 7661735930230975104261690499200 := by decide +kernel
private theorem rec_0_15_2369_1_part9 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1152 128 = 7277348865945422001700948615296 := by decide +kernel
private theorem rec_0_15_2369_1_part10 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1280 128 = 6898961350104799126821232058496 := by decide +kernel
private theorem rec_0_15_2369_1_part11 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1408 128 = 6526526230323417868726539722880 := by decide +kernel
private theorem rec_0_15_2369_1_part12 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1536 128 = 6159996384520079562514853798016 := by decide +kernel
private theorem rec_0_15_2369_1_part13 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1664 128 = 5799324720911790065087260598400 := by decide +kernel
private theorem rec_0_15_2369_1_part14 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1792 128 = 5444464178007474330957071392896 := by decide +kernel
private theorem rec_0_15_2369_1_part15 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1920 128 = 5095367724601690988058943234176 := by decide +kernel
private theorem rec_0_15_2369_1_part16 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2048 128 = 4751988387965711015651801867736 := by decide +kernel
private theorem rec_0_15_2369_1_part17 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2176 128 = 4414279621737352437838328392548 := by decide +kernel
private theorem rec_0_15_2369_1_part18 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2304 128 = 4082194712661490951563456894204 := by decide +kernel
private theorem rec_0_15_2369_1_part19 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2432 128 = 3755686598072845980302829569463 := by decide +kernel
private theorem rec_0_15_2369_1_part20 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2560 128 = 3434708236693642343649183752202 := by decide +kernel
private theorem rec_0_15_2369_1_part21 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2688 128 = 3119212617202887446004602832987 := by decide +kernel
private theorem rec_0_15_2369_1_part22 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2816 128 = 2809152758465864278211724845244 := by decide +kernel
private theorem rec_0_15_2369_1_part23 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2944 128 = 2504481710276599041879391198782 := by decide +kernel
private theorem rec_0_15_2369_1_part24 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3072 128 = 2205152552464011897204780143535 := by decide +kernel
private theorem rec_0_15_2369_1_part25 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3200 128 = 1911118394979311498999869244256 := by decide +kernel
private theorem rec_0_15_2369_1_part26 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3328 128 = 1622332378372771549288927199370 := by decide +kernel
private theorem rec_0_15_2369_1_part27 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3456 128 = 1338747673556306607811626973176 := by decide +kernel
private theorem rec_0_15_2369_1_part28 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3584 128 = 1060317481566400375296136776873 := by decide +kernel
private theorem rec_0_15_2369_1_part29 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3712 128 = 786995033739728863026326680542 := by decide +kernel
private theorem rec_0_15_2369_1_part30 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3840 128 = 518733591915106905126355456785 := by decide +kernel
private theorem rec_0_15_2369_1_part31 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3968 128 = 255486448071346131250949938653 := by decide +kernel
private theorem rec_0_15_2369_1_part32 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 4096 63 = 30595364646907288983263881596 := by decide +kernel
private theorem rec_0_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 0 256 = 21482884384207750713417815245056 :=
  phaseBlock_append rec_0_15_2369_1_part0 rec_0_15_2369_1_part1 rfl rfl rfl
private theorem rec_0_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 256 256 = 19772010120774105883717606523136 :=
  phaseBlock_append rec_0_15_2369_1_part2 rec_0_15_2369_1_part3 rfl rfl rfl
private theorem rec_0_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 0 512 = 41254894504981856597135421768192 :=
  phaseBlock_append rec_0_15_2369_1_join0 rec_0_15_2369_1_join1 rfl rfl rfl
private theorem rec_0_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 512 256 = 18111590172858838858621873504512 :=
  phaseBlock_append rec_0_15_2369_1_part4 rec_0_15_2369_1_part5 rfl rfl rfl
private theorem rec_0_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 768 256 = 16500867190897711126709767454976 :=
  phaseBlock_append rec_0_15_2369_1_part6 rec_0_15_2369_1_part7 rfl rfl rfl
private theorem rec_0_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 512 512 = 34612457363756549985331640959488 :=
  phaseBlock_append rec_0_15_2369_1_join3 rec_0_15_2369_1_join4 rfl rfl rfl
private theorem rec_0_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 0 1024 = 75867351868738406582467062727680 :=
  phaseBlock_append rec_0_15_2369_1_join2 rec_0_15_2369_1_join5 rfl rfl rfl
private theorem rec_0_15_2369_1_join7 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1024 256 = 14939084796176397105962639114496 :=
  phaseBlock_append rec_0_15_2369_1_part8 rec_0_15_2369_1_part9 rfl rfl rfl
private theorem rec_0_15_2369_1_join8 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1280 256 = 13425487580428216995547771781376 :=
  phaseBlock_append rec_0_15_2369_1_part10 rec_0_15_2369_1_part11 rfl rfl rfl
private theorem rec_0_15_2369_1_join9 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1024 512 = 28364572376604614101510410895872 :=
  phaseBlock_append rec_0_15_2369_1_join7 rec_0_15_2369_1_join8 rfl rfl rfl
private theorem rec_0_15_2369_1_join10 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1536 256 = 11959321105431869627602114396416 :=
  phaseBlock_append rec_0_15_2369_1_part12 rec_0_15_2369_1_part13 rfl rfl rfl
private theorem rec_0_15_2369_1_join11 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1792 256 = 10539831902609165319016014627072 :=
  phaseBlock_append rec_0_15_2369_1_part14 rec_0_15_2369_1_part15 rfl rfl rfl
private theorem rec_0_15_2369_1_join12 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1536 512 = 22499153008041034946618129023488 :=
  phaseBlock_append rec_0_15_2369_1_join10 rec_0_15_2369_1_join11 rfl rfl rfl
private theorem rec_0_15_2369_1_join13 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 1024 1024 = 50863725384645649048128539919360 :=
  phaseBlock_append rec_0_15_2369_1_join9 rec_0_15_2369_1_join12 rfl rfl rfl
private theorem rec_0_15_2369_1_join14 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 0 2048 = 126731077253384055630595602647040 :=
  phaseBlock_append rec_0_15_2369_1_join6 rec_0_15_2369_1_join13 rfl rfl rfl
private theorem rec_0_15_2369_1_join15 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2048 256 = 9166268009703063453490130260284 :=
  phaseBlock_append rec_0_15_2369_1_part16 rec_0_15_2369_1_part17 rfl rfl rfl
private theorem rec_0_15_2369_1_join16 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2304 256 = 7837881310734336931866286463667 :=
  phaseBlock_append rec_0_15_2369_1_part18 rec_0_15_2369_1_part19 rfl rfl rfl
private theorem rec_0_15_2369_1_join17 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2048 512 = 17004149320437400385356416723951 :=
  phaseBlock_append rec_0_15_2369_1_join15 rec_0_15_2369_1_join16 rfl rfl rfl
private theorem rec_0_15_2369_1_join18 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2560 256 = 6553920853896529789653786585189 :=
  phaseBlock_append rec_0_15_2369_1_part20 rec_0_15_2369_1_part21 rfl rfl rfl
private theorem rec_0_15_2369_1_join19 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2816 256 = 5313634468742463320091116044026 :=
  phaseBlock_append rec_0_15_2369_1_part22 rec_0_15_2369_1_part23 rfl rfl rfl
private theorem rec_0_15_2369_1_join20 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2560 512 = 11867555322638993109744902629215 :=
  phaseBlock_append rec_0_15_2369_1_join18 rec_0_15_2369_1_join19 rfl rfl rfl
private theorem rec_0_15_2369_1_join21 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2048 1024 = 28871704643076393495101319353166 :=
  phaseBlock_append rec_0_15_2369_1_join17 rec_0_15_2369_1_join20 rfl rfl rfl
private theorem rec_0_15_2369_1_join22 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3072 256 = 4116270947443323396204649387791 :=
  phaseBlock_append rec_0_15_2369_1_part24 rec_0_15_2369_1_part25 rfl rfl rfl
private theorem rec_0_15_2369_1_join23 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3328 256 = 2961080051929078157100554172546 :=
  phaseBlock_append rec_0_15_2369_1_part26 rec_0_15_2369_1_part27 rfl rfl rfl
private theorem rec_0_15_2369_1_join24 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3072 512 = 7077350999372401553305203560337 :=
  phaseBlock_append rec_0_15_2369_1_join22 rec_0_15_2369_1_join23 rfl rfl rfl
private theorem rec_0_15_2369_1_join25 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3584 256 = 1847312515306129238322463457415 :=
  phaseBlock_append rec_0_15_2369_1_part28 rec_0_15_2369_1_part29 rfl rfl rfl
private theorem rec_0_15_2369_1_join26 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3968 191 = 286081812718253420234213820249 :=
  phaseBlock_append rec_0_15_2369_1_part31 rec_0_15_2369_1_part32 rfl rfl rfl
private theorem rec_0_15_2369_1_join27 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3840 319 = 804815404633360325360569277034 :=
  phaseBlock_append rec_0_15_2369_1_part30 rec_0_15_2369_1_join26 rfl rfl rfl
private theorem rec_0_15_2369_1_join28 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3584 575 = 2652127919939489563683032734449 :=
  phaseBlock_append rec_0_15_2369_1_join25 rec_0_15_2369_1_join27 rfl rfl rfl
private theorem rec_0_15_2369_1_join29 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 3072 1087 = 9729478919311891116988236294786 :=
  phaseBlock_append rec_0_15_2369_1_join24 rec_0_15_2369_1_join28 rfl rfl rfl
private theorem rec_0_15_2369_1_join30 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 2048 2111 = 38601183562388284612089555647952 :=
  phaseBlock_append rec_0_15_2369_1_join21 rec_0_15_2369_1_join29 rfl rfl rfl
private theorem rec_0_15_2369_1_join31 :
    phaseBlock (fastLayerG (bank 0 15).shape 179798 2369 105 1 0 1 1) 0 4159 = 165332260815772340242685158294992 :=
  phaseBlock_append rec_0_15_2369_1_join14 rec_0_15_2369_1_join30 rfl rfl rfl

private theorem rec_0_15_2369_1 : fastPhase (bank 0 15).shape 179798 2369 105 1 0 1 1 = 165332260815772340242685158294992 :=
  phase_of_blockG (n := 4159) (by decide +kernel) rec_0_15_2369_1_join31

theorem receipt_0_15 : Checked (bank 0 15) 105 0 1 := by
  refine checked_from_values (bank 0 15) 105 0 1
    (P3_7_1.checked (bank 0 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_18778_4158)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_15_2368_0 rec_0_15_2368_1 rec_0_15_2369_0 rec_0_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_0_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 0 128 = 36742947903681058680566707870944 := by decide +kernel
private theorem rec_0_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 128 128 = 35553882830286254109839137606880 := by decide +kernel
private theorem rec_0_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 256 128 = 34379076462355683830901543910624 := by decide +kernel
private theorem rec_0_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 384 128 = 33218442634368208547947003571424 := by decide +kernel
private theorem rec_0_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 512 128 = 32071895221793919963182368562400 := by decide +kernel
private theorem rec_0_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 640 128 = 30939348141087855572539712425184 := by decide +kernel
private theorem rec_0_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 768 128 = 29820715349683713461387776654560 := by decide +kernel
private theorem rec_0_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 896 128 = 28715910845987567100243417083104 := by decide +kernel
private theorem rec_0_16_2368_0_part8 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1024 128 = 27624848669371580140483050265824 := by decide +kernel
private theorem rec_0_16_2368_0_part9 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1152 128 = 26547442900167721210054099864800 := by decide +kernel
private theorem rec_0_16_2368_0_part10 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1280 128 = 25483607659661478709186443033824 := by decide +kernel
private theorem rec_0_16_2368_0_part11 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1408 128 = 24433257110085575606103856803040 := by decide +kernel
private theorem rec_0_16_2368_0_part12 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1536 128 = 23396305454613684232735464463584 := by decide +kernel
private theorem rec_0_16_2368_0_part13 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1664 128 = 22372666937354141080427181952224 := by decide +kernel
private theorem rec_0_16_2368_0_part14 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1792 128 = 21362255843343661595653164236000 := by decide +kernel
private theorem rec_0_16_2368_0_part15 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1920 128 = 20364986498541054975727251696864 := by decide +kernel
private theorem rec_0_16_2368_0_part16 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2048 128 = 19380773269820938964514416516320 := by decide +kernel
private theorem rec_0_16_2368_0_part17 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2176 128 = 18409530564967454648142209060064 := by decide +kernel
private theorem rec_0_16_2368_0_part18 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2304 128 = 17451172832667981250712204262624 := by decide +kernel
private theorem rec_0_16_2368_0_part19 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2432 128 = 16505614562506850930011448012000 := by decide +kernel
private theorem rec_0_16_2368_0_part20 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2560 128 = 15572770643571279755356581027553 := by decide +kernel
private theorem rec_0_16_2368_0_part21 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2688 128 = 14652556788901031942372016701691 := by decide +kernel
private theorem rec_0_16_2368_0_part22 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2816 128 = 13744887597505460913708245084838 := by decide +kernel
private theorem rec_0_16_2368_0_part23 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2944 128 = 12849677425827354255659149058849 := by decide +kernel
private theorem rec_0_16_2368_0_part24 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3072 128 = 11966840673037660793819903388711 := by decide +kernel
private theorem rec_0_16_2368_0_part25 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3200 128 = 11096291778605404737777191660635 := by decide +kernel
private theorem rec_0_16_2368_0_part26 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3328 128 = 10237945222281113212804778973657 := by decide +kernel
private theorem rec_0_16_2368_0_part27 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3456 128 = 9391715525452076268950632992480 := by decide +kernel
private theorem rec_0_16_2368_0_part28 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3584 128 = 8557517250940668939946787248466 := by decide +kernel
private theorem rec_0_16_2368_0_part29 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3712 128 = 7735265001841618527093991109806 := by decide +kernel
private theorem rec_0_16_2368_0_part30 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3840 128 = 6924873421975417383783544735731 := by decide +kernel
private theorem rec_0_16_2368_0_part31 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3968 128 = 6126257197134655530718024036563 := by decide +kernel
private theorem rec_0_16_2368_0_part32 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4096 128 = 5339331053518892486301019078928 := by decide +kernel
private theorem rec_0_16_2368_0_part33 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4224 128 = 4564009757936907633574797588126 := by decide +kernel
private theorem rec_0_16_2368_0_part34 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4352 128 = 3800208118675737120395004505396 := by decide +kernel
private theorem rec_0_16_2368_0_part35 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4480 128 = 3047840984947493118147264721314 := by decide +kernel
private theorem rec_0_16_2368_0_part36 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4608 128 = 2306823246609215459320624981146 := by decide +kernel
private theorem rec_0_16_2368_0_part37 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4736 128 = 1577069834499160794404695586675 := by decide +kernel
private theorem rec_0_16_2368_0_part38 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4864 128 = 858495720646335493801010752999 := by decide +kernel
private theorem rec_0_16_2368_0_part39 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4992 91 = 179411563610870268697400322411 := by decide +kernel
private theorem rec_0_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 0 256 = 72296830733967312790405845477824 :=
  phaseBlock_append rec_0_16_2368_0_part0 rec_0_16_2368_0_part1 rfl rfl rfl
private theorem rec_0_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 384 256 = 65290337856162128511129372133824 :=
  phaseBlock_append rec_0_16_2368_0_part3 rec_0_16_2368_0_part4 rfl rfl rfl
private theorem rec_0_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 256 384 = 99669414318517812342030916044448 :=
  phaseBlock_append rec_0_16_2368_0_part2 rec_0_16_2368_0_join1 rfl rfl rfl
private theorem rec_0_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 0 640 = 171966245052485125132436761522272 :=
  phaseBlock_append rec_0_16_2368_0_join0 rec_0_16_2368_0_join2 rfl rfl rfl
private theorem rec_0_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 640 256 = 60760063490771569033927489079744 :=
  phaseBlock_append rec_0_16_2368_0_part5 rec_0_16_2368_0_part6 rfl rfl rfl
private theorem rec_0_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1024 256 = 54172291569539301350537150130624 :=
  phaseBlock_append rec_0_16_2368_0_part8 rec_0_16_2368_0_part9 rfl rfl rfl
private theorem rec_0_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 896 384 = 82888202415526868450780567213728 :=
  phaseBlock_append rec_0_16_2368_0_part7 rec_0_16_2368_0_join5 rfl rfl rfl
private theorem rec_0_16_2368_0_join7 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 640 640 = 143648265906298437484708056293472 :=
  phaseBlock_append rec_0_16_2368_0_join4 rec_0_16_2368_0_join6 rfl rfl rfl
private theorem rec_0_16_2368_0_join8 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 0 1280 = 315614510958783562617144817815744 :=
  phaseBlock_append rec_0_16_2368_0_join3 rec_0_16_2368_0_join7 rfl rfl rfl
private theorem rec_0_16_2368_0_join9 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1280 256 = 49916864769747054315290299836864 :=
  phaseBlock_append rec_0_16_2368_0_part10 rec_0_16_2368_0_part11 rfl rfl rfl
private theorem rec_0_16_2368_0_join10 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1664 256 = 43734922780697802676080346188224 :=
  phaseBlock_append rec_0_16_2368_0_part13 rec_0_16_2368_0_part14 rfl rfl rfl
private theorem rec_0_16_2368_0_join11 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1536 384 = 67131228235311486908815810651808 :=
  phaseBlock_append rec_0_16_2368_0_part12 rec_0_16_2368_0_join10 rfl rfl rfl
private theorem rec_0_16_2368_0_join12 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1280 640 = 117048093005058541224106110488672 :=
  phaseBlock_append rec_0_16_2368_0_join9 rec_0_16_2368_0_join11 rfl rfl rfl
private theorem rec_0_16_2368_0_join13 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1920 256 = 39745759768361993940241668213184 :=
  phaseBlock_append rec_0_16_2368_0_part15 rec_0_16_2368_0_part16 rfl rfl rfl
private theorem rec_0_16_2368_0_join14 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2304 256 = 33956787395174832180723652274624 :=
  phaseBlock_append rec_0_16_2368_0_part18 rec_0_16_2368_0_part19 rfl rfl rfl
private theorem rec_0_16_2368_0_join15 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2176 384 = 52366317960142286828865861334688 :=
  phaseBlock_append rec_0_16_2368_0_part17 rec_0_16_2368_0_join14 rfl rfl rfl
private theorem rec_0_16_2368_0_join16 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1920 640 = 92112077728504280769107529547872 :=
  phaseBlock_append rec_0_16_2368_0_join13 rec_0_16_2368_0_join15 rfl rfl rfl
private theorem rec_0_16_2368_0_join17 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 1280 1280 = 209160170733562821993213640036544 :=
  phaseBlock_append rec_0_16_2368_0_join12 rec_0_16_2368_0_join16 rfl rfl rfl
private theorem rec_0_16_2368_0_join18 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 0 2560 = 524774681692346384610358457852288 :=
  phaseBlock_append rec_0_16_2368_0_join8 rec_0_16_2368_0_join17 rfl rfl rfl
private theorem rec_0_16_2368_0_join19 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2560 256 = 30225327432472311697728597729244 :=
  phaseBlock_append rec_0_16_2368_0_part20 rec_0_16_2368_0_part21 rfl rfl rfl
private theorem rec_0_16_2368_0_join20 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2944 256 = 24816518098865015049479052447560 :=
  phaseBlock_append rec_0_16_2368_0_part23 rec_0_16_2368_0_part24 rfl rfl rfl
private theorem rec_0_16_2368_0_join21 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2816 384 = 38561405696370475963187297532398 :=
  phaseBlock_append rec_0_16_2368_0_part22 rec_0_16_2368_0_join20 rfl rfl rfl
private theorem rec_0_16_2368_0_join22 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2560 640 = 68786733128842787660915895261642 :=
  phaseBlock_append rec_0_16_2368_0_join19 rec_0_16_2368_0_join21 rfl rfl rfl
private theorem rec_0_16_2368_0_join23 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3200 256 = 21334237000886517950581970634292 :=
  phaseBlock_append rec_0_16_2368_0_part25 rec_0_16_2368_0_part26 rfl rfl rfl
private theorem rec_0_16_2368_0_join24 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3584 256 = 16292782252782287467040778358272 :=
  phaseBlock_append rec_0_16_2368_0_part28 rec_0_16_2368_0_part29 rfl rfl rfl
private theorem rec_0_16_2368_0_join25 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3456 384 = 25684497778234363735991411350752 :=
  phaseBlock_append rec_0_16_2368_0_part27 rec_0_16_2368_0_join24 rfl rfl rfl
private theorem rec_0_16_2368_0_join26 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3200 640 = 47018734779120881686573381985044 :=
  phaseBlock_append rec_0_16_2368_0_join23 rec_0_16_2368_0_join25 rfl rfl rfl
private theorem rec_0_16_2368_0_join27 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2560 1280 = 115805467907963669347489277246686 :=
  phaseBlock_append rec_0_16_2368_0_join22 rec_0_16_2368_0_join26 rfl rfl rfl
private theorem rec_0_16_2368_0_join28 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3840 256 = 13051130619110072914501568772294 :=
  phaseBlock_append rec_0_16_2368_0_part30 rec_0_16_2368_0_part31 rfl rfl rfl
private theorem rec_0_16_2368_0_join29 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4224 256 = 8364217876612644753969802093522 :=
  phaseBlock_append rec_0_16_2368_0_part33 rec_0_16_2368_0_part34 rfl rfl rfl
private theorem rec_0_16_2368_0_join30 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4096 384 = 13703548930131537240270821172450 :=
  phaseBlock_append rec_0_16_2368_0_part32 rec_0_16_2368_0_join29 rfl rfl rfl
private theorem rec_0_16_2368_0_join31 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3840 640 = 26754679549241610154772389944744 :=
  phaseBlock_append rec_0_16_2368_0_join28 rec_0_16_2368_0_join30 rfl rfl rfl
private theorem rec_0_16_2368_0_join32 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4480 256 = 5354664231556708577467889702460 :=
  phaseBlock_append rec_0_16_2368_0_part35 rec_0_16_2368_0_part36 rfl rfl rfl
private theorem rec_0_16_2368_0_join33 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4864 219 = 1037907284257205762498411075410 :=
  phaseBlock_append rec_0_16_2368_0_part38 rec_0_16_2368_0_part39 rfl rfl rfl
private theorem rec_0_16_2368_0_join34 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4736 347 = 2614977118756366556903106662085 :=
  phaseBlock_append rec_0_16_2368_0_part37 rec_0_16_2368_0_join33 rfl rfl rfl
private theorem rec_0_16_2368_0_join35 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 4480 603 = 7969641350313075134370996364545 :=
  phaseBlock_append rec_0_16_2368_0_join32 rec_0_16_2368_0_join34 rfl rfl rfl
private theorem rec_0_16_2368_0_join36 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 3840 1243 = 34724320899554685289143386309289 :=
  phaseBlock_append rec_0_16_2368_0_join31 rec_0_16_2368_0_join35 rfl rfl rfl
private theorem rec_0_16_2368_0_join37 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 2560 2523 = 150529788807518354636632663555975 :=
  phaseBlock_append rec_0_16_2368_0_join27 rec_0_16_2368_0_join36 rfl rfl rfl
private theorem rec_0_16_2368_0_join38 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 0) 0 5083 = 675304470499864739246991121408263 :=
  phaseBlock_append rec_0_16_2368_0_join18 rec_0_16_2368_0_join37 rfl rfl rfl

private theorem rec_0_16_2368_0 : fastPhase (bank 0 16).shape 179798 2368 138 1 0 1 0 = 675304470499864739246991121408263 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_0_16_2368_0_join38

private theorem rec_0_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 0 128 = 36733733669858646626425182278880 := by decide +kernel
private theorem rec_0_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 128 128 = 35544776573786181703547189503200 := by decide +kernel
private theorem rec_0_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 256 128 = 34370077531735822680709532906720 := by decide +kernel
private theorem rec_0_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 384 128 = 33209550378498777769767287407840 := by decide +kernel
private theorem rec_0_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 512 128 = 32063108989857438053797124248800 := by decide +kernel
private theorem rec_0_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 640 128 = 30930667282579092282808757380320 := by decide +kernel
private theorem rec_0_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 768 128 = 29812139214409641669456389846240 := by decide +kernel
private theorem rec_0_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 896 128 = 28707438784067314684750160168160 := by decide +kernel
private theorem rec_0_16_2368_1_part8 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1024 128 = 27616480031236381853767588730080 := by decide +kernel
private theorem rec_0_16_2368_1_part9 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1152 128 = 26539177036560870551365024163040 := by decide +kernel
private theorem rec_0_16_2368_1_part10 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1280 128 = 25475443921638279797889089729760 := by decide +kernel
private theorem rec_0_16_2368_1_part11 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1408 128 = 24425194849013295054888129709280 := by decide +kernel
private theorem rec_0_16_2368_1_part12 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1536 128 = 23388344022171503020823655781600 := by decide +kernel
private theorem rec_0_16_2368_1_part13 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1664 128 = 22364805685533106426781793412320 := by decide +kernel
private theorem rec_0_16_2368_1_part14 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1792 128 = 21354494124446638832184728237280 := by decide +kernel
private theorem rec_0_16_2368_1_part15 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1920 128 = 20357323665182679420502152447200 := by decide +kernel
private theorem rec_0_16_2368_1_part16 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2048 128 = 19373208674927567794962711172320 := by decide +kernel
private theorem rec_0_16_2368_1_part17 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2176 128 = 18402063561777118774265448867040 := by decide +kernel
private theorem rec_0_16_2368_1_part18 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2304 128 = 17443802774730337188291255694560 := by decide +kernel
private theorem rec_0_16_2368_1_part19 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2432 128 = 16498340803683132673814313911520 := by decide +kernel
private theorem rec_0_16_2368_1_part20 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2560 128 = 15565592537885394903494233499199 := by decide +kernel
private theorem rec_0_16_2368_1_part21 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2688 128 = 14645473690173922024558720019122 := by decide +kernel
private theorem rec_0_16_2368_1_part22 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2816 128 = 13737898859762661152185569772300 := by decide +kernel
private theorem rec_0_16_2368_1_part23 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2944 128 = 12842782403406771689061900836844 := by decide +kernel
private theorem rec_0_16_2368_1_part24 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3072 128 = 11960038720588761498867022553293 := by decide +kernel
private theorem rec_0_16_2368_1_part25 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3200 128 = 11089582251089409528949021336149 := by decide +kernel
private theorem rec_0_16_2368_1_part26 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3328 128 = 10231327474971352202772543992808 := by decide +kernel
private theorem rec_0_16_2368_1_part27 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3456 128 = 9385188913933685470671912017947 := by decide +kernel
private theorem rec_0_16_2368_1_part28 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3584 128 = 8551081131110173799138965093504 := by decide +kernel
private theorem rec_0_16_2368_1_part29 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3712 128 = 7728918729907303585757491937435 := by decide +kernel
private theorem rec_0_16_2368_1_part30 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3840 128 = 6918616354457569384528623184917 := by decide +kernel
private theorem rec_0_16_2368_1_part31 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3968 128 = 6120088690864737320345211574559 := by decide +kernel
private theorem rec_0_16_2368_1_part32 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4096 128 = 5333250465639827865218439294906 := by decide +kernel
private theorem rec_0_16_2368_1_part33 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4224 128 = 4558016445903461147071106632239 := by decide +kernel
private theorem rec_0_16_2368_1_part34 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4352 128 = 3794301440253994785319539319638 := by decide +kernel
private theorem rec_0_16_2368_1_part35 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4480 128 = 3042020298214667877484779964125 := by decide +kernel
private theorem rec_0_16_2368_1_part36 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4608 128 = 2301087909953987103980718561855 := by decide +kernel
private theorem rec_0_16_2368_1_part37 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4736 128 = 1571419206621813174927384793445 := by decide +kernel
private theorem rec_0_16_2368_1_part38 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4864 128 = 852929160557974415991226255950 := by decide +kernel
private theorem rec_0_16_2368_1_part39 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4992 91 = 175504863932277458174123625534 := by decide +kernel
private theorem rec_0_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 0 256 = 72278510243644828329972371782080 :=
  phaseBlock_append rec_0_16_2368_1_part0 rec_0_16_2368_1_part1 rfl rfl rfl
private theorem rec_0_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 384 256 = 65272659368356215823564411656640 :=
  phaseBlock_append rec_0_16_2368_1_part3 rec_0_16_2368_1_part4 rfl rfl rfl
private theorem rec_0_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 256 384 = 99642736900092038504273944563360 :=
  phaseBlock_append rec_0_16_2368_1_part2 rec_0_16_2368_1_join1 rfl rfl rfl
private theorem rec_0_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 0 640 = 171921247143736866834246316345440 :=
  phaseBlock_append rec_0_16_2368_1_join0 rec_0_16_2368_1_join2 rfl rfl rfl
private theorem rec_0_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 640 256 = 60742806496988733952265147226560 :=
  phaseBlock_append rec_0_16_2368_1_part5 rec_0_16_2368_1_part6 rfl rfl rfl
private theorem rec_0_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1024 256 = 54155657067797252405132612893120 :=
  phaseBlock_append rec_0_16_2368_1_part8 rec_0_16_2368_1_part9 rfl rfl rfl
private theorem rec_0_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 896 384 = 82863095851864567089882773061280 :=
  phaseBlock_append rec_0_16_2368_1_part7 rec_0_16_2368_1_join5 rfl rfl rfl
private theorem rec_0_16_2368_1_join7 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 640 640 = 143605902348853301042147920287840 :=
  phaseBlock_append rec_0_16_2368_1_join4 rec_0_16_2368_1_join6 rfl rfl rfl
private theorem rec_0_16_2368_1_join8 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 0 1280 = 315527149492590167876394236633280 :=
  phaseBlock_append rec_0_16_2368_1_join3 rec_0_16_2368_1_join7 rfl rfl rfl
private theorem rec_0_16_2368_1_join9 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1280 256 = 49900638770651574852777219439040 :=
  phaseBlock_append rec_0_16_2368_1_part10 rec_0_16_2368_1_part11 rfl rfl rfl
private theorem rec_0_16_2368_1_join10 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1664 256 = 43719299809979745258966521649600 :=
  phaseBlock_append rec_0_16_2368_1_part13 rec_0_16_2368_1_part14 rfl rfl rfl
private theorem rec_0_16_2368_1_join11 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1536 384 = 67107643832151248279790177431200 :=
  phaseBlock_append rec_0_16_2368_1_part12 rec_0_16_2368_1_join10 rfl rfl rfl
private theorem rec_0_16_2368_1_join12 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1280 640 = 117008282602802823132567396870240 :=
  phaseBlock_append rec_0_16_2368_1_join9 rec_0_16_2368_1_join11 rfl rfl rfl
private theorem rec_0_16_2368_1_join13 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1920 256 = 39730532340110247215464863619520 :=
  phaseBlock_append rec_0_16_2368_1_part15 rec_0_16_2368_1_part16 rfl rfl rfl
private theorem rec_0_16_2368_1_join14 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2304 256 = 33942143578413469862105569606080 :=
  phaseBlock_append rec_0_16_2368_1_part18 rec_0_16_2368_1_part19 rfl rfl rfl
private theorem rec_0_16_2368_1_join15 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2176 384 = 52344207140190588636371018473120 :=
  phaseBlock_append rec_0_16_2368_1_part17 rec_0_16_2368_1_join14 rfl rfl rfl
private theorem rec_0_16_2368_1_join16 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1920 640 = 92074739480300835851835882092640 :=
  phaseBlock_append rec_0_16_2368_1_join13 rec_0_16_2368_1_join15 rfl rfl rfl
private theorem rec_0_16_2368_1_join17 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 1280 1280 = 209083022083103658984403278962880 :=
  phaseBlock_append rec_0_16_2368_1_join12 rec_0_16_2368_1_join16 rfl rfl rfl
private theorem rec_0_16_2368_1_join18 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 0 2560 = 524610171575693826860797515596160 :=
  phaseBlock_append rec_0_16_2368_1_join8 rec_0_16_2368_1_join17 rfl rfl rfl
private theorem rec_0_16_2368_1_join19 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2560 256 = 30211066228059316928052953518321 :=
  phaseBlock_append rec_0_16_2368_1_part20 rec_0_16_2368_1_part21 rfl rfl rfl
private theorem rec_0_16_2368_1_join20 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2944 256 = 24802821123995533187928923390137 :=
  phaseBlock_append rec_0_16_2368_1_part23 rec_0_16_2368_1_part24 rfl rfl rfl
private theorem rec_0_16_2368_1_join21 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2816 384 = 38540719983758194340114493162437 :=
  phaseBlock_append rec_0_16_2368_1_part22 rec_0_16_2368_1_join20 rfl rfl rfl
private theorem rec_0_16_2368_1_join22 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2560 640 = 68751786211817511268167446680758 :=
  phaseBlock_append rec_0_16_2368_1_join19 rec_0_16_2368_1_join21 rfl rfl rfl
private theorem rec_0_16_2368_1_join23 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3200 256 = 21320909726060761731721565328957 :=
  phaseBlock_append rec_0_16_2368_1_part25 rec_0_16_2368_1_part26 rfl rfl rfl
private theorem rec_0_16_2368_1_join24 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3584 256 = 16279999861017477384896457030939 :=
  phaseBlock_append rec_0_16_2368_1_part28 rec_0_16_2368_1_part29 rfl rfl rfl
private theorem rec_0_16_2368_1_join25 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3456 384 = 25665188774951162855568369048886 :=
  phaseBlock_append rec_0_16_2368_1_part27 rec_0_16_2368_1_join24 rfl rfl rfl
private theorem rec_0_16_2368_1_join26 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3200 640 = 46986098501011924587289934377843 :=
  phaseBlock_append rec_0_16_2368_1_join23 rec_0_16_2368_1_join25 rfl rfl rfl
private theorem rec_0_16_2368_1_join27 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2560 1280 = 115737884712829435855457381058601 :=
  phaseBlock_append rec_0_16_2368_1_join22 rec_0_16_2368_1_join26 rfl rfl rfl
private theorem rec_0_16_2368_1_join28 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3840 256 = 13038705045322306704873834759476 :=
  phaseBlock_append rec_0_16_2368_1_part30 rec_0_16_2368_1_part31 rfl rfl rfl
private theorem rec_0_16_2368_1_join29 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4224 256 = 8352317886157455932390645951877 :=
  phaseBlock_append rec_0_16_2368_1_part33 rec_0_16_2368_1_part34 rfl rfl rfl
private theorem rec_0_16_2368_1_join30 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4096 384 = 13685568351797283797609085246783 :=
  phaseBlock_append rec_0_16_2368_1_part32 rec_0_16_2368_1_join29 rfl rfl rfl
private theorem rec_0_16_2368_1_join31 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3840 640 = 26724273397119590502482920006259 :=
  phaseBlock_append rec_0_16_2368_1_join28 rec_0_16_2368_1_join30 rfl rfl rfl
private theorem rec_0_16_2368_1_join32 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4480 256 = 5343108208168654981465498525980 :=
  phaseBlock_append rec_0_16_2368_1_part35 rec_0_16_2368_1_part36 rfl rfl rfl
private theorem rec_0_16_2368_1_join33 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4864 219 = 1028434024490251874165349881484 :=
  phaseBlock_append rec_0_16_2368_1_part38 rec_0_16_2368_1_part39 rfl rfl rfl
private theorem rec_0_16_2368_1_join34 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4736 347 = 2599853231112065049092734674929 :=
  phaseBlock_append rec_0_16_2368_1_part37 rec_0_16_2368_1_join33 rfl rfl rfl
private theorem rec_0_16_2368_1_join35 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 4480 603 = 7942961439280720030558233200909 :=
  phaseBlock_append rec_0_16_2368_1_join32 rec_0_16_2368_1_join34 rfl rfl rfl
private theorem rec_0_16_2368_1_join36 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 3840 1243 = 34667234836400310533041153207168 :=
  phaseBlock_append rec_0_16_2368_1_join31 rec_0_16_2368_1_join35 rfl rfl rfl
private theorem rec_0_16_2368_1_join37 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 2560 2523 = 150405119549229746388498534265769 :=
  phaseBlock_append rec_0_16_2368_1_join27 rec_0_16_2368_1_join36 rfl rfl rfl
private theorem rec_0_16_2368_1_join38 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2368 138 1 0 1 1) 0 5083 = 675015291124923573249296049861929 :=
  phaseBlock_append rec_0_16_2368_1_join18 rec_0_16_2368_1_join37 rfl rfl rfl

private theorem rec_0_16_2368_1 : fastPhase (bank 0 16).shape 179798 2368 138 1 0 1 1 = 675015291124923573249296049861929 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_0_16_2368_1_join38

private theorem rec_0_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 0 128 = 36743287959156170351421841303392 := by decide +kernel
private theorem rec_0_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 128 128 = 35554207186777387429298440836960 := by decide +kernel
private theorem rec_0_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 256 128 = 34379385524483951535494660933472 := by decide +kernel
private theorem rec_0_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 384 128 = 33218736803773458906788933957472 := by decide +kernel
private theorem rec_0_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 512 128 = 32072174897136166858218810910560 := by decide +kernel
private theorem rec_0_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 640 128 = 30939613718048708358890082260832 := by decide +kernel
private theorem rec_0_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 768 128 = 29820967220967806607785898772320 := by decide +kernel
private theorem rec_0_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 896 128 = 28716149401323989609575892334432 := by decide +kernel
private theorem rec_0_16_2369_0_part8 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1024 128 = 27625074295515304750425296791392 := by decide +kernel
private theorem rec_0_16_2369_0_part9 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1152 128 = 26547655980901033373804068771680 := by decide +kernel
private theorem rec_0_16_2369_0_part10 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1280 128 = 25483808575795405356296008517472 := by decide +kernel
private theorem rec_0_16_2369_0_part11 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1408 128 = 24433446239461313683407880714080 := by decide +kernel
private theorem rec_0_16_2369_0_part12 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1536 128 = 23396483172104029025378535319392 := by decide +kernel
private theorem rec_0_16_2369_0_part13 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1664 128 = 22372833614864914312988028393312 := by decide +kernel
private theorem rec_0_16_2369_0_part14 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1792 128 = 21362411849815139313366742927200 := by decide +kernel
private theorem rec_0_16_2369_0_part15 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1920 128 = 20365132199949395205804509673312 := by decide +kernel
private theorem rec_0_16_2369_0_part16 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2048 128 = 19380909029179609157559727974240 := by decide +kernel
private theorem rec_0_16_2369_0_part17 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2176 128 = 18409656742328658899668486592352 := by decide +kernel
private theorem rec_0_16_2369_0_part18 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2304 128 = 17451289785124087302753684539232 := by decide +kernel
private theorem rec_0_16_2369_0_part19 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2432 128 = 16505722644191816952834151905120 := by decide +kernel
private theorem rec_0_16_2369_0_part20 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2560 128 = 15572870176714793267566745238564 := by decide +kernel
private theorem rec_0_16_2369_0_part21 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2688 128 = 14652648101986808348123981774241 := by decide +kernel
private theorem rec_0_16_2369_0_part22 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2816 128 = 13744971042354128116487213354945 := by decide +kernel
private theorem rec_0_16_2369_0_part23 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2944 128 = 12849753351723223555955675957336 := by decide +kernel
private theorem rec_0_16_2369_0_part24 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3072 128 = 11966909425998941333893316877741 := by decide +kernel
private theorem rec_0_16_2369_0_part25 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3200 128 = 11096353701137598385370285190090 := by decide +kernel
private theorem rec_0_16_2369_0_part26 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3328 128 = 10238000653561178203927646198250 := by decide +kernel
private theorem rec_0_16_2369_0_part27 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3456 128 = 9391764802082926145046286342510 := by decide +kernel
private theorem rec_0_16_2369_0_part28 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3584 128 = 8557560705924295179688528094468 := by decide +kernel
private theorem rec_0_16_2369_0_part29 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3712 128 = 7735302964754623155424595657282 := by decide +kernel
private theorem rec_0_16_2369_0_part30 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3840 128 = 6924906219648152587944045932926 := by decide +kernel
private theorem rec_0_16_2369_0_part31 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3968 128 = 6126285153068201181553776836649 := by decide +kernel
private theorem rec_0_16_2369_0_part32 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4096 128 = 5339354487878592266702460248922 := by decide +kernel
private theorem rec_0_16_2369_0_part33 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4224 128 = 4564028987719966629753499731315 := by decide +kernel
private theorem rec_0_16_2369_0_part34 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4352 128 = 3800223457891789064465321128815 := by decide +kernel
private theorem rec_0_16_2369_0_part35 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4480 128 = 3047852744252996845800362450505 := by decide +kernel
private theorem rec_0_16_2369_0_part36 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4608 128 = 2306831733414085923905448257424 := by decide +kernel
private theorem rec_0_16_2369_0_part37 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4736 128 = 1577075353197322362826548486642 := by decide +kernel
private theorem rec_0_16_2369_0_part38 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4864 128 = 858498572357885377223103786156 := by decide +kernel
private theorem rec_0_16_2369_0_part39 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4992 91 = 179412132838586397480578161611 := by decide +kernel
private theorem rec_0_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 0 256 = 72297495145933557780720282140352 :=
  phaseBlock_append rec_0_16_2369_0_part0 rec_0_16_2369_0_part1 rfl rfl rfl
private theorem rec_0_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 384 256 = 65290911700909625765007744868032 :=
  phaseBlock_append rec_0_16_2369_0_part3 rec_0_16_2369_0_part4 rfl rfl rfl
private theorem rec_0_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 256 384 = 99670297225393577300502405801504 :=
  phaseBlock_append rec_0_16_2369_0_part2 rec_0_16_2369_0_join1 rfl rfl rfl
private theorem rec_0_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 0 640 = 171967792371327135081222687941856 :=
  phaseBlock_append rec_0_16_2369_0_join0 rec_0_16_2369_0_join2 rfl rfl rfl
private theorem rec_0_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 640 256 = 60760580939016514966675981033152 :=
  phaseBlock_append rec_0_16_2369_0_part5 rec_0_16_2369_0_part6 rfl rfl rfl
private theorem rec_0_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1024 256 = 54172730276416338124229365563072 :=
  phaseBlock_append rec_0_16_2369_0_part8 rec_0_16_2369_0_part9 rfl rfl rfl
private theorem rec_0_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 896 384 = 82888879677740327733805257897504 :=
  phaseBlock_append rec_0_16_2369_0_part7 rec_0_16_2369_0_join5 rfl rfl rfl
private theorem rec_0_16_2369_0_join7 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 640 640 = 143649460616756842700481238930656 :=
  phaseBlock_append rec_0_16_2369_0_join4 rec_0_16_2369_0_join6 rfl rfl rfl
private theorem rec_0_16_2369_0_join8 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 0 1280 = 315617252988083977781703926872512 :=
  phaseBlock_append rec_0_16_2369_0_join3 rec_0_16_2369_0_join7 rfl rfl rfl
private theorem rec_0_16_2369_0_join9 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1280 256 = 49917254815256719039703889231552 :=
  phaseBlock_append rec_0_16_2369_0_part10 rec_0_16_2369_0_part11 rfl rfl rfl
private theorem rec_0_16_2369_0_join10 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1664 256 = 43735245464680053626354771320512 :=
  phaseBlock_append rec_0_16_2369_0_part13 rec_0_16_2369_0_part14 rfl rfl rfl
private theorem rec_0_16_2369_0_join11 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1536 384 = 67131728636784082651733306639904 :=
  phaseBlock_append rec_0_16_2369_0_part12 rec_0_16_2369_0_join10 rfl rfl rfl
private theorem rec_0_16_2369_0_join12 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1280 640 = 117048983452040801691437195871456 :=
  phaseBlock_append rec_0_16_2369_0_join9 rec_0_16_2369_0_join11 rfl rfl rfl
private theorem rec_0_16_2369_0_join13 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1920 256 = 39746041229129004363364237647552 :=
  phaseBlock_append rec_0_16_2369_0_part15 rec_0_16_2369_0_part16 rfl rfl rfl
private theorem rec_0_16_2369_0_join14 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2304 256 = 33957012429315904255587836444352 :=
  phaseBlock_append rec_0_16_2369_0_part18 rec_0_16_2369_0_part19 rfl rfl rfl
private theorem rec_0_16_2369_0_join15 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2176 384 = 52366669171644563155256323036704 :=
  phaseBlock_append rec_0_16_2369_0_part17 rec_0_16_2369_0_join14 rfl rfl rfl
private theorem rec_0_16_2369_0_join16 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1920 640 = 92112710400773567518620560684256 :=
  phaseBlock_append rec_0_16_2369_0_join13 rec_0_16_2369_0_join15 rfl rfl rfl
private theorem rec_0_16_2369_0_join17 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 1280 1280 = 209161693852814369210057756555712 :=
  phaseBlock_append rec_0_16_2369_0_join12 rec_0_16_2369_0_join16 rfl rfl rfl
private theorem rec_0_16_2369_0_join18 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 0 2560 = 524778946840898346991761683428224 :=
  phaseBlock_append rec_0_16_2369_0_join8 rec_0_16_2369_0_join17 rfl rfl rfl
private theorem rec_0_16_2369_0_join19 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2560 256 = 30225518278701601615690727012805 :=
  phaseBlock_append rec_0_16_2369_0_part20 rec_0_16_2369_0_part21 rfl rfl rfl
private theorem rec_0_16_2369_0_join20 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2944 256 = 24816662777722164889848992835077 :=
  phaseBlock_append rec_0_16_2369_0_part23 rec_0_16_2369_0_part24 rfl rfl rfl
private theorem rec_0_16_2369_0_join21 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2816 384 = 38561633820076293006336206190022 :=
  phaseBlock_append rec_0_16_2369_0_part22 rec_0_16_2369_0_join20 rfl rfl rfl
private theorem rec_0_16_2369_0_join22 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2560 640 = 68787152098777894622026933202827 :=
  phaseBlock_append rec_0_16_2369_0_join19 rec_0_16_2369_0_join21 rfl rfl rfl
private theorem rec_0_16_2369_0_join23 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3200 256 = 21334354354698776589297931388340 :=
  phaseBlock_append rec_0_16_2369_0_part25 rec_0_16_2369_0_part26 rfl rfl rfl
private theorem rec_0_16_2369_0_join24 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3584 256 = 16292863670678918335113123751750 :=
  phaseBlock_append rec_0_16_2369_0_part28 rec_0_16_2369_0_part29 rfl rfl rfl
private theorem rec_0_16_2369_0_join25 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3456 384 = 25684628472761844480159410094260 :=
  phaseBlock_append rec_0_16_2369_0_part27 rec_0_16_2369_0_join24 rfl rfl rfl
private theorem rec_0_16_2369_0_join26 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3200 640 = 47018982827460621069457341482600 :=
  phaseBlock_append rec_0_16_2369_0_join23 rec_0_16_2369_0_join25 rfl rfl rfl
private theorem rec_0_16_2369_0_join27 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2560 1280 = 115806134926238515691484274685427 :=
  phaseBlock_append rec_0_16_2369_0_join22 rec_0_16_2369_0_join26 rfl rfl rfl
private theorem rec_0_16_2369_0_join28 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3840 256 = 13051191372716353769497822769575 :=
  phaseBlock_append rec_0_16_2369_0_part30 rec_0_16_2369_0_part31 rfl rfl rfl
private theorem rec_0_16_2369_0_join29 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4224 256 = 8364252445611755694218820860130 :=
  phaseBlock_append rec_0_16_2369_0_part33 rec_0_16_2369_0_part34 rfl rfl rfl
private theorem rec_0_16_2369_0_join30 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4096 384 = 13703606933490347960921281109052 :=
  phaseBlock_append rec_0_16_2369_0_part32 rec_0_16_2369_0_join29 rfl rfl rfl
private theorem rec_0_16_2369_0_join31 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3840 640 = 26754798306206701730419103878627 :=
  phaseBlock_append rec_0_16_2369_0_join28 rec_0_16_2369_0_join30 rfl rfl rfl
private theorem rec_0_16_2369_0_join32 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4480 256 = 5354684477667082769705810707929 :=
  phaseBlock_append rec_0_16_2369_0_part35 rec_0_16_2369_0_part36 rfl rfl rfl
private theorem rec_0_16_2369_0_join33 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4864 219 = 1037910705196471774703681947767 :=
  phaseBlock_append rec_0_16_2369_0_part38 rec_0_16_2369_0_part39 rfl rfl rfl
private theorem rec_0_16_2369_0_join34 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4736 347 = 2614986058393794137530230434409 :=
  phaseBlock_append rec_0_16_2369_0_part37 rec_0_16_2369_0_join33 rfl rfl rfl
private theorem rec_0_16_2369_0_join35 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 4480 603 = 7969670536060876907236041142338 :=
  phaseBlock_append rec_0_16_2369_0_join32 rec_0_16_2369_0_join34 rfl rfl rfl
private theorem rec_0_16_2369_0_join36 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 3840 1243 = 34724468842267578637655145020965 :=
  phaseBlock_append rec_0_16_2369_0_join31 rec_0_16_2369_0_join35 rfl rfl rfl
private theorem rec_0_16_2369_0_join37 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 2560 2523 = 150530603768506094329139419706392 :=
  phaseBlock_append rec_0_16_2369_0_join27 rec_0_16_2369_0_join36 rfl rfl rfl
private theorem rec_0_16_2369_0_join38 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 0) 0 5083 = 675309550609404441320901103134616 :=
  phaseBlock_append rec_0_16_2369_0_join18 rec_0_16_2369_0_join37 rfl rfl rfl

private theorem rec_0_16_2369_0 : fastPhase (bank 0 16).shape 179798 2369 138 1 0 1 0 = 675309550609404441320901103134616 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_0_16_2369_0_join38

private theorem rec_0_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 0 128 = 36734073656355274910676787194080 := by decide +kernel
private theorem rec_0_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 128 128 = 35545100862886663747784292899040 := by decide +kernel
private theorem rec_0_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 256 128 = 34370386528047216480686604896480 := by decide +kernel
private theorem rec_0_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 384 128 = 33209844483646884682227221231840 := by decide +kernel
private theorem rec_0_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 512 128 = 32063388602488232875410909669600 := by decide +kernel
private theorem rec_0_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 640 128 = 30930932798360153109212828522720 := by decide +kernel
private theorem rec_0_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 768 128 = 29812391026031579534387647482080 := by decide +kernel
private theorem rec_0_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 896 128 = 28707677281245202979278668445920 := by decide +kernel
private theorem rec_0_16_2369_1_part8 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1024 128 = 27616705600711185525626946349280 := by decide +kernel
private theorem rec_0_16_2369_1_part9 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1152 128 = 26539390062100875084380409993440 := by decide +kernel
private theorem rec_0_16_2369_1_part10 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1280 128 = 25475644784040519971502982875360 := by decide +kernel
private theorem rec_0_16_2369_1_part11 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1408 128 = 24425383926104983483783704017120 := by decide +kernel
private theorem rec_0_16_2369_1_part12 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1536 128 = 23388521688811458474645848795360 := by decide +kernel
private theorem rec_0_16_2369_1_part13 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1664 128 = 22364972313613181929956049770720 := by decide +kernel
private theorem rec_0_16_2369_1_part14 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1792 128 = 21354650082893149543833417517280 := by decide +kernel
private theorem rec_0_16_2369_1_part15 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1920 128 = 20357469319957830294458661452000 := by decide +kernel
private theorem rec_0_16_2369_1_part16 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2048 128 = 19373344389030881019883210664160 := by decide +kernel
private theorem rec_0_16_2369_1_part17 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2176 128 = 18402189695246860993838334744800 := by decide +kernel
private theorem rec_0_16_2369_1_part18 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2304 128 = 17443919684644946501544264616160 := by decide +kernel
private theorem rec_0_16_2369_1_part19 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2432 128 = 16498448844162645415519313361120 := by decide +kernel
private theorem rec_0_16_2369_1_part20 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2560 128 = 15565692031157527656064933662611 := by decide +kernel
private theorem rec_0_16_2369_1_part21 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2688 128 = 14645564964718112800104428526498 := by decide +kernel
private theorem rec_0_16_2369_1_part22 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2816 128 = 13737982267385151433657936496158 := by decide +kernel
private theorem rec_0_16_2369_1_part23 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2944 128 = 12842858293377236669938439158578 := by decide +kernel
private theorem rec_0_16_2369_1_part24 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3072 128 = 11960107438910761326496123934068 := by decide +kernel
private theorem rec_0_16_2369_1_part25 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3200 128 = 11089644140253958697445770298881 := by decide +kernel
private theorem rec_0_16_2369_1_part26 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3328 128 = 10231382874141041950419654067409 := by decide +kernel
private theorem rec_0_16_2369_1_part27 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3456 128 = 9385238159696687986837146928283 := by decide +kernel
private theorem rec_0_16_2369_1_part28 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3584 128 = 8551124556453967343696216330400 := by decide +kernel
private theorem rec_0_16_2369_1_part29 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3712 128 = 7728956664394166751040146883257 := by decide +kernel
private theorem rec_0_16_2369_1_part30 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3840 128 = 6918649124903237343601150647105 := by decide +kernel
private theorem rec_0_16_2369_1_part31 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3968 128 = 6120116620755733935541089510287 := by decide +kernel
private theorem rec_0_16_2369_1_part32 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4096 128 = 5333273875127083901451801636220 := by decide +kernel
private theorem rec_0_16_2369_1_part33 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4224 128 = 4558035651969805996660350310279 := by decide +kernel
private theorem rec_0_16_2369_1_part34 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4352 128 = 3794316756894428712599975407994 := by decide +kernel
private theorem rec_0_16_2369_1_part35 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4480 128 = 3042032036071195104127869055122 := by decide +kernel
private theorem rec_0_16_2369_1_part36 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4608 128 = 2301096376422257185761111121110 := by decide +kernel
private theorem rec_0_16_2369_1_part37 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4736 128 = 1571424706081158702158447805498 := by decide +kernel
private theorem rec_0_16_2369_1_part38 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4864 128 = 852931994114026138105078160813 := by decide +kernel
private theorem rec_0_16_2369_1_part39 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4992 91 = 175505420903599200307878855591 := by decide +kernel
private theorem rec_0_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 0 256 = 72279174519241938658461080093120 :=
  phaseBlock_append rec_0_16_2369_1_part0 rec_0_16_2369_1_part1 rfl rfl rfl
private theorem rec_0_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 384 256 = 65273233086135117557638130901440 :=
  phaseBlock_append rec_0_16_2369_1_part3 rec_0_16_2369_1_part4 rfl rfl rfl
private theorem rec_0_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 256 384 = 99643619614182334038324735797920 :=
  phaseBlock_append rec_0_16_2369_1_part2 rec_0_16_2369_1_join1 rfl rfl rfl
private theorem rec_0_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 0 640 = 171922794133424272696785815891040 :=
  phaseBlock_append rec_0_16_2369_1_join0 rec_0_16_2369_1_join2 rfl rfl rfl
private theorem rec_0_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 640 256 = 60743323824391732643600476004800 :=
  phaseBlock_append rec_0_16_2369_1_part5 rec_0_16_2369_1_part6 rfl rfl rfl
private theorem rec_0_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1024 256 = 54156095662812060610007356342720 :=
  phaseBlock_append rec_0_16_2369_1_part8 rec_0_16_2369_1_part9 rfl rfl rfl
private theorem rec_0_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 896 384 = 82863772944057263589286024788640 :=
  phaseBlock_append rec_0_16_2369_1_part7 rec_0_16_2369_1_join5 rfl rfl rfl
private theorem rec_0_16_2369_1_join7 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 640 640 = 143607096768448996232886500793440 :=
  phaseBlock_append rec_0_16_2369_1_join4 rec_0_16_2369_1_join6 rfl rfl rfl
private theorem rec_0_16_2369_1_join8 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 0 1280 = 315529890901873268929672316684480 :=
  phaseBlock_append rec_0_16_2369_1_join3 rec_0_16_2369_1_join7 rfl rfl rfl
private theorem rec_0_16_2369_1_join9 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1280 256 = 49901028710145503455286686892480 :=
  phaseBlock_append rec_0_16_2369_1_part10 rec_0_16_2369_1_part11 rfl rfl rfl
private theorem rec_0_16_2369_1_join10 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1664 256 = 43719622396506331473789467288000 :=
  phaseBlock_append rec_0_16_2369_1_part13 rec_0_16_2369_1_part14 rfl rfl rfl
private theorem rec_0_16_2369_1_join11 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1536 384 = 67108144085317789948435316083360 :=
  phaseBlock_append rec_0_16_2369_1_part12 rec_0_16_2369_1_join10 rfl rfl rfl
private theorem rec_0_16_2369_1_join12 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1280 640 = 117009172795463293403722002975840 :=
  phaseBlock_append rec_0_16_2369_1_join9 rec_0_16_2369_1_join11 rfl rfl rfl
private theorem rec_0_16_2369_1_join13 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1920 256 = 39730813708988711314341872116160 :=
  phaseBlock_append rec_0_16_2369_1_part15 rec_0_16_2369_1_part16 rfl rfl rfl
private theorem rec_0_16_2369_1_join14 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2304 256 = 33942368528807591917063577977280 :=
  phaseBlock_append rec_0_16_2369_1_part18 rec_0_16_2369_1_part19 rfl rfl rfl
private theorem rec_0_16_2369_1_join15 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2176 384 = 52344558224054452910901912722080 :=
  phaseBlock_append rec_0_16_2369_1_part17 rec_0_16_2369_1_join14 rfl rfl rfl
private theorem rec_0_16_2369_1_join16 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1920 640 = 92075371933043164225243784838240 :=
  phaseBlock_append rec_0_16_2369_1_join13 rec_0_16_2369_1_join15 rfl rfl rfl
private theorem rec_0_16_2369_1_join17 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 1280 1280 = 209084544728506457628965787814080 :=
  phaseBlock_append rec_0_16_2369_1_join12 rec_0_16_2369_1_join16 rfl rfl rfl
private theorem rec_0_16_2369_1_join18 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 0 2560 = 524614435630379726558638104498560 :=
  phaseBlock_append rec_0_16_2369_1_join8 rec_0_16_2369_1_join17 rfl rfl rfl
private theorem rec_0_16_2369_1_join19 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2560 256 = 30211256995875640456169362189109 :=
  phaseBlock_append rec_0_16_2369_1_part20 rec_0_16_2369_1_part21 rfl rfl rfl
private theorem rec_0_16_2369_1_join20 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2944 256 = 24802965732287997996434563092646 :=
  phaseBlock_append rec_0_16_2369_1_part23 rec_0_16_2369_1_part24 rfl rfl rfl
private theorem rec_0_16_2369_1_join21 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2816 384 = 38540947999673149430092499588804 :=
  phaseBlock_append rec_0_16_2369_1_part22 rec_0_16_2369_1_join20 rfl rfl rfl
private theorem rec_0_16_2369_1_join22 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2560 640 = 68752204995548789886261861777913 :=
  phaseBlock_append rec_0_16_2369_1_join19 rec_0_16_2369_1_join21 rfl rfl rfl
private theorem rec_0_16_2369_1_join23 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3200 256 = 21321027014395000647865424366290 :=
  phaseBlock_append rec_0_16_2369_1_part25 rec_0_16_2369_1_part26 rfl rfl rfl
private theorem rec_0_16_2369_1_join24 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3584 256 = 16280081220848134094736363213657 :=
  phaseBlock_append rec_0_16_2369_1_part28 rec_0_16_2369_1_part29 rfl rfl rfl
private theorem rec_0_16_2369_1_join25 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3456 384 = 25665319380544822081573510141940 :=
  phaseBlock_append rec_0_16_2369_1_part27 rec_0_16_2369_1_join24 rfl rfl rfl
private theorem rec_0_16_2369_1_join26 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3200 640 = 46986346394939822729438934508230 :=
  phaseBlock_append rec_0_16_2369_1_join23 rec_0_16_2369_1_join25 rfl rfl rfl
private theorem rec_0_16_2369_1_join27 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2560 1280 = 115738551390488612615700796286143 :=
  phaseBlock_append rec_0_16_2369_1_join22 rec_0_16_2369_1_join26 rfl rfl rfl
private theorem rec_0_16_2369_1_join28 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3840 256 = 13038765745658971279142240157392 :=
  phaseBlock_append rec_0_16_2369_1_part30 rec_0_16_2369_1_part31 rfl rfl rfl
private theorem rec_0_16_2369_1_join29 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4224 256 = 8352352408864234709260325718273 :=
  phaseBlock_append rec_0_16_2369_1_part33 rec_0_16_2369_1_part34 rfl rfl rfl
private theorem rec_0_16_2369_1_join30 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4096 384 = 13685626283991318610712127354493 :=
  phaseBlock_append rec_0_16_2369_1_part32 rec_0_16_2369_1_join29 rfl rfl rfl
private theorem rec_0_16_2369_1_join31 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3840 640 = 26724392029650289889854367511885 :=
  phaseBlock_append rec_0_16_2369_1_join28 rec_0_16_2369_1_join30 rfl rfl rfl
private theorem rec_0_16_2369_1_join32 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4480 256 = 5343128412493452289888980176232 :=
  phaseBlock_append rec_0_16_2369_1_part35 rec_0_16_2369_1_part36 rfl rfl rfl
private theorem rec_0_16_2369_1_join33 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4864 219 = 1028437415017625338412957016404 :=
  phaseBlock_append rec_0_16_2369_1_part38 rec_0_16_2369_1_part39 rfl rfl rfl
private theorem rec_0_16_2369_1_join34 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4736 347 = 2599862121098784040571404821902 :=
  phaseBlock_append rec_0_16_2369_1_part37 rec_0_16_2369_1_join33 rfl rfl rfl
private theorem rec_0_16_2369_1_join35 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 4480 603 = 7942990533592236330460384998134 :=
  phaseBlock_append rec_0_16_2369_1_join32 rec_0_16_2369_1_join34 rfl rfl rfl
private theorem rec_0_16_2369_1_join36 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 3840 1243 = 34667382563242526220314752510019 :=
  phaseBlock_append rec_0_16_2369_1_join31 rec_0_16_2369_1_join35 rfl rfl rfl
private theorem rec_0_16_2369_1_join37 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 2560 2523 = 150405933953731138836015548796162 :=
  phaseBlock_append rec_0_16_2369_1_join27 rec_0_16_2369_1_join36 rfl rfl rfl
private theorem rec_0_16_2369_1_join38 :
    phaseBlock (fastLayerG (bank 0 16).shape 179798 2369 138 1 0 1 1) 0 5083 = 675020369584110865394653653294722 :=
  phaseBlock_append rec_0_16_2369_1_join18 rec_0_16_2369_1_join37 rfl rfl rfl

private theorem rec_0_16_2369_1 : fastPhase (bank 0 16).shape 179798 2369 138 1 0 1 1 = 675020369584110865394653653294722 :=
  phase_of_blockG (n := 5083) (by decide +kernel) rec_0_16_2369_1_join38

theorem receipt_0_16 : Checked (bank 0 16) 138 0 1 := by
  refine checked_from_values (bank 0 16) 138 0 1
    (P3_7_1.checked (bank 0 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_22951_5082)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_0_16_2368_0 rec_0_16_2368_1 rec_0_16_2369_0 rec_0_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect0_checked (i : Fin 17) (hi : i ≠ 0) :
    Checked (bank 0 i) (reserve i) (excess 0) (seed 0) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact receipt_0_1
  · exact receipt_0_2
  · exact receipt_0_3
  · exact receipt_0_4
  · exact receipt_0_5
  · exact receipt_0_6
  · exact receipt_0_7
  · exact receipt_0_8
  · exact receipt_0_9
  · exact receipt_0_10
  · exact receipt_0_11
  · exact receipt_0_12
  · exact receipt_0_13
  · exact receipt_0_14
  · exact receipt_0_15
  · exact receipt_0_16

end Lower6961.Lo.RescueSource
