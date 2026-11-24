import ProximityPrize.SubmissionLower.R6961LoRescueSourceSchedule
import ProximityPrize.SubmissionLower.R6961LoRescuePoolMoments0
import ProximityPrize.SubmissionLower.R6961LoRescuePoolMoments1

set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueSource
open P1_7 (Bank debit)
open Lower6960.HelperSource (WidthGuard)
open Lower6960.RescueSource (fastLayer fastPhase)
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

private theorem mkP (r : Fin 10) (s : Fin 17) (h a b c d e n z : ℕ) (cs : List (ℕ × ℕ))
    (hsz : (bank r s).shape.J / b + 1 = n)
    (hn : (cs.map Prod.fst).sum = n) (hz : (cs.map Prod.snd).sum = z)
    (hc : blk (fastLayer (bank r s).shape 179818 h a b c d e) 0 cs) :
    fastPhase (bank r s).shape 179818 h a b c d e = z :=
  phase_of_block hsz (by rw [← hn, ← hz]; exact blk_sum hc)


private theorem rec_8_0_2327_0 : fastPhase (bank 8 0).shape 179818 2327 0 1 2 14 0 = 3355930015769666945844 := mkP 8 0 2327 0 1 2 14 0 130 3355930015769666945844 [(128,3355456042086752562048),(2,473973682914383796)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_0_2327_1 : fastPhase (bank 8 0).shape 179818 2327 0 1 2 14 1 = 3288421664638577586444 := mkP 8 0 2327 0 1 2 14 1 130 3288421664638577586444 [(128,3288265263419441775168),(2,156401219135811276)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_0_2328_0 : fastPhase (bank 8 0).shape 179818 2328 0 1 2 14 0 = 3355950801241038057590 := mkP 8 0 2328 0 1 2 14 0 130 3355950801241038057590 [(128,3355476827856164128832),(2,473973384873928758)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_0_2328_1 : fastPhase (bank 8 0).shape 179818 2328 0 1 2 14 1 = 3288441981398124364190 := mkP 8 0 2328 0 1 2 14 1 130 3288441981398124364190 [(128,3288285580276656389312),(2,156401121467974878)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_0 : Checked (bank 8 0) 0 2 14 := by
  refine checked_from_values (bank 8 0) 0 2 14
    (P3_7_1.checked (bank 8 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_0_2327_0 rec_8_0_2327_1 rec_8_0_2328_0 rec_8_0_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_1_2327_0 : fastPhase (bank 8 1).shape 179818 2327 1 1 2 14 0 = 4864257256094118467442 := mkP 8 1 2327 1 1 2 14 0 130 4864257256094118467442 [(128,4863519202374966948672),(2,738053719151518770)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_1_2327_1 : fastPhase (bank 8 1).shape 179818 2327 1 1 2 14 1 = 4768685346969243144432 := mkP 8 1 2327 1 1 2 14 1 130 4768685346969243144432 [(128,4768441650744922006272),(2,243696224321138160)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_1_2328_0 : fastPhase (bank 8 1).shape 179818 2328 1 1 2 14 0 = 4864286903029129703504 := mkP 8 1 2328 1 1 2 14 0 130 4864286903029129703504 [(128,4863548849806525508864),(2,738053222604194640)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_1_2328_1 : fastPhase (bank 8 1).shape 179818 2328 1 1 2 14 1 = 4768714341577100921864 := mkP 8 1 2328 1 1 2 14 1 130 4768714341577100921864 [(128,4768470645515656686464),(2,243696061444235400)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_1 : Checked (bank 8 1) 1 2 14 := by
  refine checked_from_values (bank 8 1) 1 2 14
    (P3_7_1.checked (bank 8 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_1_2327_0 rec_8_1_2327_1 rec_8_1_2328_0 rec_8_1_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_2_2327_0 : fastPhase (bank 8 2).shape 179818 2327 2 1 2 14 0 = 7660750100126883288386 := mkP 8 2 2327 2 1 2 14 0 130 7660750100126883288386 [(128,7659505045258034525760),(2,1245054868848762626)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_2_2327_1 : fastPhase (bank 8 2).shape 179818 2327 2 1 2 14 1 = 7513791691101912097726 := mkP 8 2 2327 2 1 2 14 1 130 7513791691101912097726 [(128,7513380347852555812480),(2,411343249356285246)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_2_2328_0 : fastPhase (bank 8 2).shape 179818 2328 2 1 2 14 0 = 7660796033969626493231 := mkP 8 2 2328 2 1 2 14 0 130 7660796033969626493231 [(128,7659550979993176511520),(2,1245053976449981711)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_2_2328_1 : fastPhase (bank 8 2).shape 179818 2328 2 1 2 14 1 = 7513836639496391872031 := mkP 8 2 2328 2 1 2 14 1 130 7513836639496391872031 [(128,7513425296540018903840),(2,411342956372968191)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_2 : Checked (bank 8 2) 2 2 14 := by
  refine checked_from_values (bank 8 2) 2 2 14
    (P3_7_1.checked (bank 8 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_2_2327_0 rec_8_2_2327_1 rec_8_2_2328_0 rec_8_2_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_3_2327_0 : fastPhase (bank 8 3).shape 179818 2327 3 1 2 14 0 = 22726186952206165186080 := mkP 8 3 2327 3 1 2 14 0 191 22726186952206165186080 [(128,21369282681530390755008),(63,1356904270675774431072)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_3_2327_1 : fastPhase (bank 8 3).shape 179818 2327 3 1 2 14 1 = 22404602974253124804480 := mkP 8 3 2327 3 1 2 14 1 191 22404602974253124804480 [(128,21097727176125233370240),(63,1306875798127891434240)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_3_2328_0 : fastPhase (bank 8 3).shape 179818 2328 3 1 2 14 0 = 22726326511961481880464 := mkP 8 3 2328 3 1 2 14 0 191 22726326511961481880464 [(128,21369420752415117080160),(63,1356905759546364800304)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_3_2328_1 : fastPhase (bank 8 3).shape 179818 2328 3 1 2 14 1 = 22404740317152412174704 := mkP 8 3 2328 3 1 2 14 1 191 22404740317152412174704 [(128,21097863086569717351008),(63,1306877230582694823696)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_3 : Checked (bank 8 3) 3 2 14 := by
  refine checked_from_values (bank 8 3) 3 2 14
    (P3_7_1.checked (bank 8 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_3_2327_0 rec_8_3_2327_1 rec_8_3_2328_0 rec_8_3_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_4_2327_0 : fastPhase (bank 8 4).shape 179818 2327 4 1 2 14 0 = 27653001460488401031552 := mkP 8 4 2327 4 1 2 14 0 191 27653001460488401031552 [(128,25947043308930550759680),(63,1705958151557850271872)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_4_2327_1 : fastPhase (bank 8 4).shape 179818 2327 4 1 2 14 1 = 27267720591923594516832 := mkP 8 4 2327 4 1 2 14 1 191 27267720591923594516832 [(128,25624178897411183151552),(63,1643541694512411365280)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_4_2328_0 : fastPhase (bank 8 4).shape 179818 2328 4 1 2 14 0 = 27653169443234635080144 := mkP 8 4 2328 4 1 2 14 0 191 27653169443234635080144 [(128,25947209480038018789344),(63,1705959963196616290800)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_4_2328_1 : fastPhase (bank 8 4).shape 179818 2328 4 1 2 14 1 = 27267885948352705835760 := mkP 8 4 2328 4 1 2 14 1 191 27267885948352705835760 [(128,25624342510160625059808),(63,1643543438192080775952)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_4 : Checked (bank 8 4) 4 2 14 := by
  refine checked_from_values (bank 8 4) 4 2 14
    (P3_7_1.checked (bank 8 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_4_2327_0 rec_8_4_2327_1 rec_8_4_2328_0 rec_8_4_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_5_2327_0 : fastPhase (bank 8 5).shape 179818 2327 5 1 2 14 0 = 34363758112330185858240 := mkP 8 5 2327 5 1 2 14 0 191 34363758112330185858240 [(128,32174752000426914642048),(63,2189006111903271216192)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_5_2327_1 : fastPhase (bank 8 5).shape 179818 2327 5 1 2 14 1 = 33892427820871140608192 := mkP 8 5 2327 5 1 2 14 1 191 33892427820871140608192 [(128,31782915439111683377216),(63,2109512381759457230976)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_5_2328_0 : fastPhase (bank 8 5).shape 179818 2328 5 1 2 14 0 = 34363964581374928961376 := mkP 8 5 2328 5 1 2 14 0 191 34363964581374928961376 [(128,32174956221880401408576),(63,2189008359494527552800)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_5_2328_1 : fastPhase (bank 8 5).shape 179818 2328 5 1 2 14 1 = 33892631113773521124240 := mkP 8 5 2328 5 1 2 14 1 191 33892631113773521124240 [(128,31783116567895457442624),(63,2109514545878063681616)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_5 : Checked (bank 8 5) 5 2 14 := by
  refine checked_from_values (bank 8 5) 5 2 14
    (P3_7_1.checked (bank 8 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_5_2327_0 rec_8_5_2327_1 rec_8_5_2328_0 rec_8_5_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_6_2327_0 : fastPhase (bank 8 6).shape 179818 2327 7 1 2 14 0 = 57722355960190112600928 := mkP 8 6 2327 7 1 2 14 0 191 57722355960190112600928 [(128,53809911525829561915968),(63,3912444434360550684960)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_6_2327_1 : fastPhase (bank 8 6).shape 179818 2327 7 1 2 14 1 = 56955441499255528111104 := mkP 8 6 2327 7 1 2 14 1 191 56955441499255528111104 [(128,53183059561380829229952),(63,3772381937874698881152)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_6_2328_0 : fastPhase (bank 8 6).shape 179818 2328 7 1 2 14 0 = 57722695116375030172016 := mkP 8 6 2328 7 1 2 14 0 191 57722695116375030172016 [(128,53810246938756696598432),(63,3912448177618333573584)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_6_2328_1 : fastPhase (bank 8 6).shape 179818 2328 7 1 2 14 1 = 56955775609337456878416 := mkP 8 6 2328 7 1 2 14 1 191 56955775609337456878416 [(128,53183390064478474506144),(63,3772385544858982372272)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_6 : Checked (bank 8 6) 7 2 14 := by
  refine checked_from_values (bank 8 6) 7 2 14
    (P3_7_1.checked (bank 8 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_6_2327_0 rec_8_6_2327_1 rec_8_6_2328_0 rec_8_6_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_7_2327_0 : fastPhase (bank 8 7).shape 179818 2327 10 1 2 14 0 = 240864221970793095211446 := mkP 8 7 2327 10 1 2 14 0 278 240864221970793095211446 [(128,192726276149130851558816),(128,47495887376304294196640),(22,642058445357949455990)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_7_2327_1 : fastPhase (bank 8 7).shape 179818 2327 10 1 2 14 1 = 238538070966796329790320 := mkP 8 7 2327 10 1 2 14 1 278 238538070966796329790320 [(128,191197218151307542806240),(128,46757397509652447719136),(22,583455305836339264944)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_7_2328_0 : fastPhase (bank 8 7).shape 179818 2328 10 1 2 14 0 = 240865660371381455267844 := mkP 8 7 2328 10 1 2 14 0 278 240865660371381455267844 [(128,192727602215792686969024),(128,47496000028965462806720),(22,642058126623305492100)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_7_2328_1 : fastPhase (bank 8 7).shape 179818 2328 10 1 2 14 1 = 238539493759498797712910 := mkP 8 7 2328 10 1 2 14 1 278 238539493759498797712910 [(128,191198530587710632136640),(128,46757508154689387737024),(22,583455017098777839246)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_7 : Checked (bank 8 7) 10 2 14 := by
  refine checked_from_values (bank 8 7) 10 2 14
    (P3_7_1.checked (bank 8 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_7_2327_0 rec_8_7_2327_1 rec_8_7_2328_0 rec_8_7_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_8_2327_0 : fastPhase (bank 8 8).shape 179818 2327 16 1 2 14 0 = 696637793381869065004782 := mkP 8 8 2327 16 1 2 14 0 278 696637793381869065004782 [(128,544811426323788615728672),(128,149588841051835314261536),(22,2237526006245135014574)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_8_2327_1 : fastPhase (bank 8 8).shape 179818 2327 16 1 2 14 1 = 690342009572526502275984 := mkP 8 8 2327 16 1 2 14 1 278 690342009572526502275984 [(128,540920683061143534480224),(128,147386352648974604245856),(22,2034973862408363549904)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_8_2328_0 : fastPhase (bank 8 8).shape 179818 2328 16 1 2 14 0 = 696641761885048879733412 := mkP 8 8 2328 16 1 2 14 0 278 696641761885048879733412 [(128,544815066852506986063552),(128,149589170417784876500672),(22,2237524614757017169188)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_8_2328_1 : fastPhase (bank 8 8).shape 179818 2328 16 1 2 14 1 = 690345937906620784697822 := mkP 8 8 2328 16 1 2 14 1 278 690345937906620784697822 [(128,540924288901947303410112),(128,147386676404292842445248),(22,2034972600380638842462)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_8 : Checked (bank 8 8) 16 2 14 := by
  refine checked_from_values (bank 8 8) 16 2 14
    (P3_7_1.checked (bank 8 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_8_2327_0 rec_8_8_2327_1 rec_8_8_2328_0 rec_8_8_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_9_2327_0 : fastPhase (bank 8 9).shape 179818 2327 10 1 2 14 0 = 240864221970793095211446 := mkP 8 9 2327 10 1 2 14 0 278 240864221970793095211446 [(128,192726276149130851558816),(128,47495887376304294196640),(22,642058445357949455990)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_9_2327_1 : fastPhase (bank 8 9).shape 179818 2327 10 1 2 14 1 = 238538070966796329790320 := mkP 8 9 2327 10 1 2 14 1 278 238538070966796329790320 [(128,191197218151307542806240),(128,46757397509652447719136),(22,583455305836339264944)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_9_2328_0 : fastPhase (bank 8 9).shape 179818 2328 10 1 2 14 0 = 240865660371381455267844 := mkP 8 9 2328 10 1 2 14 0 278 240865660371381455267844 [(128,192727602215792686969024),(128,47496000028965462806720),(22,642058126623305492100)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_9_2328_1 : fastPhase (bank 8 9).shape 179818 2328 10 1 2 14 1 = 238539493759498797712910 := mkP 8 9 2328 10 1 2 14 1 278 238539493759498797712910 [(128,191198530587710632136640),(128,46757508154689387737024),(22,583455017098777839246)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_9 : Checked (bank 8 9) 10 2 14 := by
  refine checked_from_values (bank 8 9) 10 2 14
    (P3_7_1.checked (bank 8 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_9_2327_0 rec_8_9_2327_1 rec_8_9_2328_0 rec_8_9_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_10_2327_0 : fastPhase (bank 8 10).shape 179818 2327 20 1 2 14 0 = 1938362440018310206350261 := mkP 8 10 2327 20 1 2 14 0 370 1938362440018310206350261 [(128,1290165298930811871528288),(128,542360415996693944628576),(114,105836725090804390193397)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_10_2327_1 : fastPhase (bank 8 10).shape 179818 2327 20 1 2 14 1 = 1924657317204385607601411 := mkP 8 10 2327 20 1 2 14 1 370 1924657317204385607601411 [(128,1283155444081568331068448),(128,537787455618685131408416),(114,103714417504132145124547)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_10_2328_0 : fastPhase (bank 8 10).shape 179818 2328 20 1 2 14 0 = 1938373689787394426388185 := mkP 8 10 2328 20 1 2 14 0 370 1938373689787394426388185 [(128,1290174585560640704688512),(128,542362303246314206368128),(114,105836800980439515331545)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_10_2328_1 : fastPhase (bank 8 10).shape 179818 2328 20 1 2 14 1 = 1924668477665099250316485 := mkP 8 10 2328 20 1 2 14 1 370 1924668477665099250316485 [(128,1283164663233580548064512),(128,537789322580725847401728),(114,103714491850792854850245)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_10 : Checked (bank 8 10) 20 2 14 := by
  refine checked_from_values (bank 8 10) 20 2 14
    (P3_7_1.checked (bank 8 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_10_2327_0 rec_8_10_2327_1 rec_8_10_2328_0 rec_8_10_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_11_2327_0 : fastPhase (bank 8 11).shape 179818 2327 32 1 2 14 0 = 12949264932666509141194487 := mkP 8 11 2327 32 1 2 14 0 493 12949264932666509141194487 [(128,6972478842509090699882208),(128,3920563801259639000301280),(128,1714693883459886222462688),(109,341528405437893218548311)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_11_2327_1 : fastPhase (bank 8 11).shape 179818 2327 32 1 2 14 1 = 12881269073757380748659847 := mkP 8 11 2327 32 1 2 14 1 493 12881269073757380748659847 [(128,6945665511620982909902688),(128,3900163321835264762810208),(128,1700825643171617469890400),(109,334614597129515606056551)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_11_2328_0 : fastPhase (bank 8 11).shape 179818 2328 32 1 2 14 0 = 12949338802690267373272006 := mkP 8 11 2328 32 1 2 14 0 493 12949338802690267373272006 [(128,6972531251908191091127904),(128,3920581672671264916268640),(128,1714697425706031955138144),(109,341528452404779410737318)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_11_2328_1 : fastPhase (bank 8 11).shape 179818 2328 32 1 2 14 1 = 12881342508406245364402141 := mkP 8 11 2328 32 1 2 14 1 493 12881342508406245364402141 [(128,6945717646442156662460064),(128,3900181070536210076286624),(128,1700829148183226193047200),(109,334614643244652432608253)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_11 : Checked (bank 8 11) 32 2 14 := by
  refine checked_from_values (bank 8 11) 32 2 14
    (P3_7_1.checked (bank 8 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_11_2327_0 rec_8_11_2327_1 rec_8_11_2328_0 rec_8_11_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_12_2327_0 : fastPhase (bank 8 12).shape 179818 2327 31 1 2 14 0 = 11737546024681644311374191 := mkP 8 12 2327 31 1 2 14 0 493 11737546024681644311374191 [(128,6343767321352969059610464),(128,3546970893997491301728096),(128,1541639649497687665266528),(109,305168159833496284769103)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_12_2327_1 : fastPhase (bank 8 12).shape 179818 2327 31 1 2 14 1 = 11675529368674444618457835 := mkP 8 12 2327 31 1 2 14 1 493 11675529368674444618457835 [(128,6319107760495868458446048),(128,3528350306854517721963744),(128,1529093342113342505553120),(109,298977959210715932494923)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_12_2328_0 : fastPhase (bank 8 12).shape 179818 2328 31 1 2 14 0 = 11737613283679414735588218 := mkP 8 12 2328 31 1 2 14 0 493 11737613283679414735588218 [(128,6343815106892202411502432),(128,3546987115402191469943648),(128,1541642855738992124037984),(109,305168205646028730104154)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_12_2328_1 : fastPhase (bank 8 12).shape 179818 2328 31 1 2 14 1 = 11675596228669919957200565 := mkP 8 12 2328 31 1 2 14 1 493 11675596228669919957200565 [(128,6319155293774548175439264),(128,3528366416186707515012512),(128,1529096514530942109328800),(109,298978004177722157419989)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_12 : Checked (bank 8 12) 31 2 14 := by
  refine checked_from_values (bank 8 12) 31 2 14
    (P3_7_1.checked (bank 8 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_12_2327_0 rec_8_12_2327_1 rec_8_12_2328_0 rec_8_12_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_13_2327_0 : fastPhase (bank 8 13).shape 179818 2327 44 1 2 14 0 = 67052048822080084037739576 := mkP 8 13 2327 44 1 2 14 0 678 67052048822080084037739576 [(128,28355305517726873688090816),(128,19041829780565409702021312),(128,11579619957901551487936704),(128,5944136125157423728871616),(128,2039910003393933700344000),(38,91247437334891730475128)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_13_2327_1 : fastPhase (bank 8 13).shape 179818 2327 44 1 2 14 1 = 66791342120924036099052814 := mkP 8 13 2327 44 1 2 14 1 678 66791342120924036099052814 [(128,28276179558065020296959104),(128,18976792002202179174929536),(128,11528854824039984146486400),(128,5907217131364949397214336),(128,2015891290087675443221632),(38,86407315164227640241806)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_13_2328_0 : fastPhase (bank 8 13).shape 179818 2328 44 1 2 14 0 = 67052433601279714482471178 := mkP 8 13 2328 44 1 2 14 0 678 67052433601279714482471178 [(128,28355529267627908534311648),(128,19041937065739874515651296),(128,11579662050438162148489952),(128,5944147187450311155280608),(128,2039910662881445146057440),(38,91247367142012982680234)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_13_2328_1 : fastPhase (bank 8 13).shape 179818 2328 44 1 2 14 1 = 66791725219009060623531682 := mkP 8 13 2328 44 1 2 14 1 678 66791725219009060623531682 [(128,28276402457036009185296352),(128,18976898799301757983436768),(128,11528896673611135293857760),(128,5907228102257696195317728),(128,2015891938040805340151776),(38,86407248761656625471298)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_13 : Checked (bank 8 13) 44 2 14 := by
  refine checked_from_values (bank 8 13) 44 2 14
    (P3_7_1.checked (bank 8 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_13_2327_0 rec_8_13_2327_1 rec_8_13_2328_0 rec_8_13_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_14_2327_0 : fastPhase (bank 8 14).shape 179818 2327 76 1 2 14 0 = 850158138809576312233534275 := mkP 8 14 2327 76 1 2 14 0 925 850158138809576312233534275 [(128,267469523243311822040371680),(128,206607750075950844323389920),(128,152764083115271204758893024),(128,106316409425633367222583776),(128,67482141225805798611210720),(128,36329821932254086764995040),(128,12790732202430058390057440),(29,397677588919130122032675)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_14_2327_1 : fastPhase (bank 8 14).shape 179818 2327 76 1 2 14 1 = 847830479274698971298067975 := mkP 8 14 2327 76 1 2 14 1 925 847830479274698971298067975 [(128,266973159636082824443581920),(128,206162999917946392575821280),(128,152374783171240329587635680),(128,105985075526386778974725600),(128,67210059880701190991877600),(128,36117141941681440575391200),(128,12636556270296945265505760),(29,370702930363068883528935)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_14_2328_0 : fastPhase (bank 8 14).shape 179818 2328 76 1 2 14 0 = 850162850567397483821523120 := mkP 8 14 2328 76 1 2 14 0 925 850162850567397483821523120 [(128,267471675090236699464571680),(128,206609059806201680309267232),(128,152764813246176076419447584),(128,106316765476123727475264288),(128,67482278525393469587741472),(128,36329852076581235588885280),(128,12790729155392155321793312),(29,397677191292439654552272)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_14_2328_1 : fastPhase (bank 8 14).shape 179818 2328 76 1 2 14 1 = 847835176565777495638999995 := mkP 8 14 2328 76 1 2 14 1 925 847835176565777495638999995 [(128,266975305883423323080134368),(128,206164305773302016982965984),(128,152375510779337074216611552),(128,105985430078560581775884000),(128,67210196421517848772464352),(128,36117171822129506725011168),(128,12636553247553609849269984),(29,370702559953534236658587)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_14 : Checked (bank 8 14) 76 2 14 := by
  refine checked_from_values (bank 8 14) 76 2 14
    (P3_7_1.checked (bank 8 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_14_2327_0 rec_8_14_2327_1 rec_8_14_2328_0 rec_8_14_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_15_2327_0 : fastPhase (bank 8 15).shape 179818 2327 105 1 2 14 0 = 4979086610238662225535199458 := mkP 8 15 2327 105 1 2 14 0 1294 4979086610238662225535199458 [(128,1171021289646412338243438016),(128,976647221488345888239265216),(128,798445347035916611558196672),(128,637007202564554581294605760),(128,492718425977240358785025472),(128,365770362847794111530575296),(128,256171672464164731119388096),(128,163759933871718951149036992),(128,88213251916530465148962240),(128,29061863288669044502898112),(14,270039137315143963807586)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_15_2327_1 : fastPhase (bank 8 15).shape 179818 2327 105 1 2 14 1 = 4969206949392680529211791708 := mkP 8 15 2327 105 1 2 14 1 1294 4969206949392680529211791708 [(128,1169457802465877756465812992),(128,975204183358916010092336640),(128,797128603319101256417121792),(128,635820916239281858419496448),(128,491665169252341971058988544),(128,364851208774490659197752832),(128,255386286548551015522997760),(128,163106665687249278469412352),(128,87689226716503950141593088),(128,28663073618714914236470784),(14,233813411651859189808476)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_15_2328_0 : fastPhase (bank 8 15).shape 179818 2328 105 1 2 14 0 = 4979114364653332056120569805 := mkP 8 15 2328 105 1 2 14 0 1294 4979114364653332056120569805 [(128,1171030992988537020907844832),(128,976654092436925625743934688),(128,798450028179286455387821280),(128,637010235939797084932187360),(128,492720262032013760010597600),(128,365771369048733497087608032),(128,256172141551856183748875488),(128,163760091762246678991267040),(128,88213265249596913512969440),(128,29061846622287990003598560),(14,270038842050845793865485)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_15_2328_1 : fastPhase (bank 8 15).shape 179818 2328 105 1 2 14 1 = 4969234641992472803496556605 := mkP 8 15 2328 105 1 2 14 1 1294 4969234641992472803496556605 [(128,1169467487703821742692018400),(128,975211040325730808456001760),(128,797133273952143968337709280),(128,635823941983656272986495200),(128,491667000020369669278591200),(128,364852211551755100607215840),(128,255386753646514607172684000),(128,163106822642443426272516320),(128,87689239836292092591548640),(128,28663057173628538492041440),(14,233813156116576609734525)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_15 : Checked (bank 8 15) 105 2 14 := by
  refine checked_from_values (bank 8 15) 105 2 14
    (P3_7_1.checked (bank 8 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_15_2327_0 rec_8_15_2327_1 rec_8_15_2328_0 rec_8_15_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_8_16_2327_0 : fastPhase (bank 8 16).shape 179818 2327 138 1 2 14 0 = 25384245984183224194424920671 := mkP 8 16 2327 138 1 2 14 0 1787 25384245984183224194424920671 [(128,4500591596697322371681318624),(128,3942657337949206915193677536),(128,3420104665703529866117633760),(128,2933668391518331863144924896),(128,2483832887670194027802408672),(128,2070843693197527082374489824),(128,1694719119943860467825546976),(128,1355261858601131461722359520),(128,1052070584752974296156534496),(128,784551564918009275666933472),(128,551930262593131895162099424),(128,353262944296801957842683616),(128,187448285612332693123872480),(123,53302790728870020610437375)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_16_2327_1 : fastPhase (bank 8 16).shape 179818 2327 138 1 2 14 1 = 25347064295992893710350701642 := mkP 8 16 2327 138 1 2 14 1 1787 25347064295992893710350701642 [(128,4496142181247957302478717280),(128,3938474426610165974304395616),(128,3416195628123784291399885152),(128,2930038559840934820015911264),(128,2480485648144765912976359776),(128,2067780577792740827600703840),(128,1691939897959926843626430816),(128,1352764628282284381131469152),(128,1049851864899956118456615264),(128,782606386500556110127960416),(128,550252260362458904779317600),(128,351844448398088663074648416),(128,186280413197208275630489952),(123,52407374632065284747797098)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_16_2328_0 : fastPhase (bank 8 16).shape 179818 2328 138 1 2 14 0 = 25384389029396241051475845353 := mkP 8 16 2328 138 1 2 14 0 1787 25384389029396241051475845353 [(128,4500629770940400299723109792),(128,3942687140511830175162688928),(128,3420127507790425499485410720),(128,2933685519594366135060678048),(128,2483845394807138361939031456),(128,2070852530067396978142258592),(128,1694725105458827399953503648),(128,1355265690200007762207376800),(128,1052072848334271018580063648),(128,784552744419567041879434656),(128,551930749218324724335154592),(128,353263045387314077888791968),(128,187448233167508334483928480),(123,53302749498863242634414025)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_8_16_2328_1 : fastPhase (bank 8 16).shape 179818 2328 138 1 2 14 1 = 25347207105754928774545264841 := mkP 8 16 2328 138 1 2 14 1 1787 25347207105754928774545264841 [(128,4496180303159111522784573920),(128,3938504185784083316657154528),(128,3416218434703333952372791776),(128,2930055659303685186935376352),(128,2480498132647393420715932128),(128,2067789397162011797742725600),(128,1691945870330252305991375328),(128,1352768450379847877674961376),(128,1049854121973414489534134752),(128,782607561898313263127226848),(128,550252744756512565120358880),(128,351844548654450107577551328),(128,186280360892895048250833376),(123,52407334109623920060268649)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_8_16 : Checked (bank 8 16) 138 2 14 := by
  refine checked_from_values (bank 8 16) 138 2 14
    (P3_7_1.checked (bank 8 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_8_16_2327_0 rec_8_16_2327_1 rec_8_16_2328_0 rec_8_16_2328_1 (by decide +kernel) (by decide +kernel)

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
