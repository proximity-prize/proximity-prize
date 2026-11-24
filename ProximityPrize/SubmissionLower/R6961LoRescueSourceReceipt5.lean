import ProximityPrize.SubmissionLower.R6961LoRescueSourceSchedule
import ProximityPrize.SubmissionLower.R6961LoRescuePoolMoments0

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


private theorem rec_5_1_2327_0 : fastPhase (bank 5 1).shape 179818 2327 1 1 4 1 0 = 2018480042195095482360 := mkP 5 1 2327 1 1 4 1 0 130 2018480042195095482360 [(128,2018480042195095482360),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_1_2327_1 : fastPhase (bank 5 1).shape 179818 2327 1 1 4 1 1 = 1977213927454575416028 := mkP 5 1 2327 1 1 4 1 1 130 1977213927454575416028 [(128,1977213927454575416028),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_1_2328_0 : fastPhase (bank 5 1).shape 179818 2328 1 1 4 1 0 = 2018490465011775365718 := mkP 5 1 2328 1 1 4 1 0 130 2018490465011775365718 [(128,2018490465011775365718),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_1_2328_1 : fastPhase (bank 5 1).shape 179818 2328 1 1 4 1 1 = 1977224055281991388270 := mkP 5 1 2328 1 1 4 1 1 130 1977224055281991388270 [(128,1977224055281991388270),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_1 : Checked (bank 5 1) 1 4 1 := by
  refine checked_from_values (bank 5 1) 1 4 1
    (P3_7_1.checked (bank 5 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_1_2327_0 rec_5_1_2327_1 rec_5_1_2328_0 rec_5_1_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_2_2327_0 : fastPhase (bank 5 2).shape 179818 2327 2 1 4 1 0 = 2303164366879528697268 := mkP 5 2 2327 2 1 4 1 0 130 2303164366879528697268 [(128,2303164366879528697268),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_2_2327_1 : fastPhase (bank 5 2).shape 179818 2327 2 1 4 1 1 = 2256112371518359440186 := mkP 5 2 2327 2 1 4 1 1 130 2256112371518359440186 [(128,2256112371518359440186),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_2_2328_0 : fastPhase (bank 5 2).shape 179818 2328 2 1 4 1 0 = 2303176144071924365538 := mkP 5 2 2328 2 1 4 1 0 130 2303176144071924365538 [(128,2303176144071924365538),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_2_2328_1 : fastPhase (bank 5 2).shape 179818 2328 2 1 4 1 1 = 2256123815173783794730 := mkP 5 2 2328 2 1 4 1 1 130 2256123815173783794730 [(128,2256123815173783794730),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_2 : Checked (bank 5 2) 2 4 1 := by
  refine checked_from_values (bank 5 2) 2 4 1
    (P3_7_1.checked (bank 5 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_2_2327_0 rec_5_2_2327_1 rec_5_2_2328_0 rec_5_2_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_3_2327_0 : fastPhase (bank 5 3).shape 179818 2327 3 1 4 1 0 = 2652832525510447578996 := mkP 5 3 2327 3 1 4 1 0 130 2652832525510447578996 [(128,2652832525510447578996),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_3_2327_1 : fastPhase (bank 5 3).shape 179818 2327 3 1 4 1 1 = 2598676520116912311384 := mkP 5 3 2327 3 1 4 1 1 130 2598676520116912311384 [(128,2598676520116912311384),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_3_2328_0 : fastPhase (bank 5 3).shape 179818 2328 3 1 4 1 0 = 2652845957503674710628 := mkP 5 3 2328 3 1 4 1 0 130 2652845957503674710628 [(128,2652845957503674710628),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_3_2328_1 : fastPhase (bank 5 3).shape 179818 2328 3 1 4 1 1 = 2598689571453171654700 := mkP 5 3 2328 3 1 4 1 1 130 2598689571453171654700 [(128,2598689571453171654700),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_3 : Checked (bank 5 3) 3 4 1 := by
  refine checked_from_values (bank 5 3) 3 4 1
    (P3_7_1.checked (bank 5 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_3_2327_0 rec_5_3_2327_1 rec_5_3_2328_0 rec_5_3_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_4_2327_0 : fastPhase (bank 5 4).shape 179818 2327 4 1 4 1 0 = 3086989130761159562748 := mkP 5 4 2327 4 1 4 1 0 130 3086989130761159562748 [(128,3086989130761159562748),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_4_2327_1 : fastPhase (bank 5 4).shape 179818 2327 4 1 4 1 1 = 3024015831172572441846 := mkP 5 4 2327 4 1 4 1 1 130 3024015831172572441846 [(128,3024015831172572441846),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_4_2328_0 : fastPhase (bank 5 4).shape 179818 2328 4 1 4 1 0 = 3087004605978255531546 := mkP 5 4 2328 4 1 4 1 0 130 3087004605978255531546 [(128,3087004605978255531546),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_4_2328_1 : fastPhase (bank 5 4).shape 179818 2328 4 1 4 1 1 = 3024030867523031867458 := mkP 5 4 2328 4 1 4 1 1 130 3024030867523031867458 [(128,3024030867523031867458),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_4 : Checked (bank 5 4) 4 4 1 := by
  refine checked_from_values (bank 5 4) 4 4 1
    (P3_7_1.checked (bank 5 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_4_2327_0 rec_5_4_2327_1 rec_5_4_2328_0 rec_5_4_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_5_2327_0 : fastPhase (bank 5 5).shape 179818 2327 5 1 4 1 0 = 3637787890976061104256 := mkP 5 5 2327 5 1 4 1 0 130 3637787890976061104256 [(128,3637787890976061104256),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_5_2327_1 : fastPhase (bank 5 5).shape 179818 2327 5 1 4 1 1 = 3563632483538425546404 := mkP 5 5 2327 5 1 4 1 1 130 3563632483538425546404 [(128,3563632483538425546404),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_5_2328_0 : fastPhase (bank 5 5).shape 179818 2328 5 1 4 1 0 = 3637805944661144219526 := mkP 5 5 2328 5 1 4 1 0 130 3637805944661144219526 [(128,3637805944661144219526),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_5_2328_1 : fastPhase (bank 5 5).shape 179818 2328 5 1 4 1 1 = 3563650024864181249398 := mkP 5 5 2328 5 1 4 1 1 130 3563650024864181249398 [(128,3563650024864181249398),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_5 : Checked (bank 5 5) 5 4 1 := by
  refine checked_from_values (bank 5 5) 5 4 1
    (P3_7_1.checked (bank 5 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_5_2327_0 rec_5_5_2327_1 rec_5_5_2328_0 rec_5_5_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_6_2327_0 : fastPhase (bank 5 6).shape 179818 2327 7 1 4 1 0 = 5292491389795300222512 := mkP 5 6 2327 7 1 4 1 0 130 5292491389795300222512 [(128,5292491389795300222512),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_6_2327_1 : fastPhase (bank 5 6).shape 179818 2327 7 1 4 1 1 = 5184762048307380180180 := mkP 5 6 2327 7 1 4 1 1 130 5184762048307380180180 [(128,5184762048307380180180),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_6_2328_0 : fastPhase (bank 5 6).shape 179818 2328 7 1 4 1 0 = 5292517123764971530026 := mkP 5 6 2328 7 1 4 1 0 130 5292517123764971530026 [(128,5292517123764971530026),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_6_2328_1 : fastPhase (bank 5 6).shape 179818 2328 7 1 4 1 1 = 5184787050842283045178 := mkP 5 6 2328 7 1 4 1 1 130 5184787050842283045178 [(128,5184787050842283045178),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_6 : Checked (bank 5 6) 7 4 1 := by
  refine checked_from_values (bank 5 6) 7 4 1
    (P3_7_1.checked (bank 5 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_6_2327_0 rec_5_6_2327_1 rec_5_6_2328_0 rec_5_6_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_7_2327_0 : fastPhase (bank 5 7).shape 179818 2327 10 1 4 1 0 = 11074373430681798432360 := mkP 5 7 2327 10 1 4 1 0 130 11074373430681798432360 [(128,11074373430681798432360),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_7_2327_1 : fastPhase (bank 5 7).shape 179818 2327 10 1 4 1 1 = 10849444026916578664668 := mkP 5 7 2327 10 1 4 1 1 130 10849444026916578664668 [(128,10849444026916578664668),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_7_2328_0 : fastPhase (bank 5 7).shape 179818 2328 10 1 4 1 0 = 11074425608973464651829 := mkP 5 7 2328 10 1 4 1 0 130 11074425608973464651829 [(128,11074425608973464651829),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_7_2328_1 : fastPhase (bank 5 7).shape 179818 2328 10 1 4 1 1 = 10849494718453998131581 := mkP 5 7 2328 10 1 4 1 1 130 10849494718453998131581 [(128,10849494718453998131581),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_7 : Checked (bank 5 7) 10 4 1 := by
  refine checked_from_values (bank 5 7) 10 4 1
    (P3_7_1.checked (bank 5 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_7_2327_0 rec_5_7_2327_1 rec_5_7_2328_0 rec_5_7_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_8_2327_0 : fastPhase (bank 5 8).shape 179818 2327 16 1 4 1 0 = 60263101846255740346602 := mkP 5 8 2327 16 1 4 1 0 191 60263101846255740346602 [(128,58395242460854097285696),(63,1867859385401643060906)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_8_2327_1 : fastPhase (bank 5 8).shape 179818 2327 16 1 4 1 1 = 59427552090509738598844 := mkP 5 8 2327 16 1 4 1 1 191 59427552090509738598844 [(128,57665933863256993198976),(63,1761618227252745399868)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_8_2328_0 : fastPhase (bank 5 8).shape 179818 2328 16 1 4 1 0 = 60263382899986044971093 := mkP 5 8 2328 16 1 4 1 0 191 60263382899986044971093 [(128,58395525330385202364768),(63,1867857569600842606325)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_8_2328_1 : fastPhase (bank 5 8).shape 179818 2328 16 1 4 1 1 = 59427827666750658244757 := mkP 5 8 2328 16 1 4 1 1 191 59427827666750658244757 [(128,57666211165011622035936),(63,1761616501739036208821)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_8 : Checked (bank 5 8) 16 4 1 := by
  refine checked_from_values (bank 5 8) 16 4 1
    (P3_7_1.checked (bank 5 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_8_2327_0 rec_5_8_2327_1 rec_5_8_2328_0 rec_5_8_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_9_2327_0 : fastPhase (bank 5 9).shape 179818 2327 10 1 4 1 0 = 11074373430681798432360 := mkP 5 9 2327 10 1 4 1 0 130 11074373430681798432360 [(128,11074373430681798432360),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_9_2327_1 : fastPhase (bank 5 9).shape 179818 2327 10 1 4 1 1 = 10849444026916578664668 := mkP 5 9 2327 10 1 4 1 1 130 10849444026916578664668 [(128,10849444026916578664668),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_9_2328_0 : fastPhase (bank 5 9).shape 179818 2328 10 1 4 1 0 = 11074425608973464651829 := mkP 5 9 2328 10 1 4 1 0 130 11074425608973464651829 [(128,11074425608973464651829),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_9_2328_1 : fastPhase (bank 5 9).shape 179818 2328 10 1 4 1 1 = 10849494718453998131581 := mkP 5 9 2328 10 1 4 1 1 130 10849494718453998131581 [(128,10849494718453998131581),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_9 : Checked (bank 5 9) 10 4 1 := by
  refine checked_from_values (bank 5 9) 10 4 1
    (P3_7_1.checked (bank 5 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_9_2327_0 rec_5_9_2327_1 rec_5_9_2328_0 rec_5_9_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_10_2327_0 : fastPhase (bank 5 10).shape 179818 2327 20 1 4 1 0 = 121095317791655670329580 := mkP 5 10 2327 20 1 4 1 0 191 121095317791655670329580 [(128,117328177092702406017408),(63,3767140698953264312172)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_10_2327_1 : fastPhase (bank 5 10).shape 179818 2327 20 1 4 1 1 = 119419639246338820535232 := mkP 5 10 2327 20 1 4 1 1 191 119419639246338820535232 [(128,115866664605771711282432),(63,3552974640567109252800)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_10_2328_0 : fastPhase (bank 5 10).shape 179818 2328 20 1 4 1 0 = 121095866069324660412192 := mkP 5 10 2328 20 1 4 1 0 191 121095866069324660412192 [(128,117328729407197934596544),(63,3767136662126725815648)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_10_2328_1 : fastPhase (bank 5 10).shape 179818 2328 20 1 4 1 1 = 119420176811146384212720 := mkP 5 10 2328 20 1 4 1 1 191 119420176811146384212720 [(128,115867206003367648389696),(63,3552970807778735823024)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_10 : Checked (bank 5 10) 20 4 1 := by
  refine checked_from_values (bank 5 10) 20 4 1
    (P3_7_1.checked (bank 5 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_10_2327_0 rec_5_10_2327_1 rec_5_10_2328_0 rec_5_10_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_11_2327_0 : fastPhase (bank 5 11).shape 179818 2327 32 1 4 1 0 = 887435611448506328265024 := mkP 5 11 2327 32 1 4 1 0 278 887435611448506328265024 [(128,742878776555486848303264),(128,144556834893019479961760),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_11_2327_1 : fastPhase (bank 5 11).shape 179818 2327 32 1 4 1 1 = 878957440934640423294511 := mkP 5 11 2327 32 1 4 1 1 278 878957440934640423294511 [(128,737445500868998963733600),(128,141511940065641459560911),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_11_2328_0 : fastPhase (bank 5 11).shape 179818 2328 32 1 4 1 0 = 887439563526457671325144 := mkP 5 11 2328 32 1 4 1 0 278 887439563526457671325144 [(128,742882690455695426968384),(128,144556873070762244356760),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_11_2328_1 : fastPhase (bank 5 11).shape 179818 2328 32 1 4 1 1 = 878961339518095776676149 := mkP 5 11 2328 32 1 4 1 1 278 878961339518095776676149 [(128,737449363167090561633600),(128,141511976351005215042549),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_11 : Checked (bank 5 11) 32 4 1 := by
  refine checked_from_values (bank 5 11) 32 4 1
    (P3_7_1.checked (bank 5 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_11_2327_0 rec_5_11_2327_1 rec_5_11_2328_0 rec_5_11_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_12_2327_0 : fastPhase (bank 5 12).shape 179818 2327 31 1 4 1 0 = 784254803350788109073280 := mkP 5 12 2327 31 1 4 1 0 278 784254803350788109073280 [(128,656560567750318953200960),(128,127694235600469155872320),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_12_2327_1 : fastPhase (bank 5 12).shape 179818 2327 31 1 4 1 1 = 776759818762463035514799 := mkP 5 12 2327 31 1 4 1 1 278 776759818762463035514799 [(128,651755720331131331577536),(128,125004098431331703937263),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_12_2328_0 : fastPhase (bank 5 12).shape 179818 2328 31 1 4 1 0 = 784258314314648342768638 := mkP 5 12 2328 31 1 4 1 0 278 784258314314648342768638 [(128,656564042608709425882432),(128,127694271705938916886206),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_12_2328_1 : fastPhase (bank 5 12).shape 179818 2328 31 1 4 1 1 = 776763282225566055187509 := mkP 5 12 2328 31 1 4 1 1 278 776763282225566055187509 [(128,651759149414471043226176),(128,125004132811095011961333),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_12 : Checked (bank 5 12) 31 4 1 := by
  refine checked_from_values (bank 5 12) 31 4 1
    (P3_7_1.checked (bank 5 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_12_2327_0 rec_5_12_2327_1 rec_5_12_2328_0 rec_5_12_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_13_2327_0 : fastPhase (bank 5 13).shape 179818 2327 44 1 4 1 0 = 4121676378466915370244030 := mkP 5 13 2327 44 1 4 1 0 370 4121676378466915370244030 [(128,2899001354875588581109344),(128,1125273667621042638872160),(114,97401355970284150262526)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_13_2327_1 : fastPhase (bank 5 13).shape 179818 2327 44 1 4 1 1 = 4092082113993759175372725 := mkP 5 13 2327 44 1 4 1 1 370 4092082113993759175372725 [(128,2884625400388232493463840),(128,1113257040780637951519008),(114,94199672824888730389877)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_13_2328_0 : fastPhase (bank 5 13).shape 179818 2328 44 1 4 1 0 = 4121694652148955836415300 := mkP 5 13 2328 44 1 4 1 0 370 4121694652148955836415300 [(128,2899018247556081914120928),(128,1125275173068706889079520),(114,97401231524167033214852)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_13_2328_1 : fastPhase (bank 5 13).shape 179818 2328 44 1 4 1 1 = 4092100201550562073763115 := mkP 5 13 2328 44 1 4 1 1 370 4092100201550562073763115 [(128,2884642132816203946529632),(128,1113258516587012401595232),(114,94199552147345725638251)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_13 : Checked (bank 5 13) 44 4 1 := by
  refine checked_from_values (bank 5 13) 44 4 1
    (P3_7_1.checked (bank 5 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_13_2327_0 rec_5_13_2327_1 rec_5_13_2328_0 rec_5_13_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_14_2327_0 : fastPhase (bank 5 14).shape 179818 2327 76 1 4 1 0 = 89872445220855495514240428 := mkP 5 14 2327 76 1 4 1 0 678 89872445220855495514240428 [(128,39637508411580528751585920),(128,27387969873377393759971968),(128,15713037851371266742299264),(128,6297919387525373290146432),(128,836009697000932970236844),(38,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_14_2327_1 : fastPhase (bank 5 14).shape 179818 2327 76 1 4 1 1 = 89519087925749579918675940 := mkP 5 14 2327 76 1 4 1 1 678 89519087925749579918675940 [(128,39544957834753594254403968),(128,27292895780482270576994688),(128,15628850073173206387599744),(128,6237732338412355853937024),(128,814651898928152845740516),(38,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_14_2328_0 : fastPhase (bank 5 14).shape 179818 2328 76 1 4 1 0 = 89872847546826145227224580 := mkP 5 14 2328 76 1 4 1 0 678 89872847546826145227224580 [(128,39637783511244565367864064),(128,27388076216895219300588288),(128,15713061959738321074322176),(128,6297917511296650455915264),(128,836008347651389028534788),(38,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_14_2328_1 : fastPhase (bank 5 14).shape 179818 2328 76 1 4 1 1 = 89519488010118399545075724 := mkP 5 14 2328 76 1 4 1 1 678 89519488010118399545075724 [(128,39545231616701474142419712),(128,27293001436098623680174848),(128,15628873926649144948603648),(128,6237730447896181558680320),(128,814650582772975215197196),(38,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_14 : Checked (bank 5 14) 76 4 1 := by
  refine checked_from_values (bank 5 14) 76 4 1
    (P3_7_1.checked (bank 5 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_14_2327_0 rec_5_14_2327_1 rec_5_14_2328_0 rec_5_14_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_15_2327_0 : fastPhase (bank 5 15).shape 179818 2327 105 1 4 1 0 = 541984546702011480304958709 := mkP 5 15 2327 105 1 4 1 0 925 541984546702011480304958709 [(128,182467435486137665013136128),(128,142934203608757190984989440),(128,103154540676393162096261888),(128,66102673632064248498912000),(128,34703100925461976767314688),(128,11830853111456183506238208),(128,791739261741053438106357),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_15_2327_1 : fastPhase (bank 5 15).shape 179818 2327 105 1 4 1 1 = 540420930223543706478009477 := mkP 5 15 2327 105 1 4 1 1 925 540420930223543706478009477 [(128,182170609762630398596750784),(128,142622819077659406447558080),(128,102852199555151230921235904),(128,65832586536292584988507584),(128,34488088913504013906517440),(128,11693349728945348826807744),(128,761276649360722790631941),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_15_2328_0 : fastPhase (bank 5 15).shape 179818 2328 105 1 4 1 0 = 541986967730340012320893631 := mkP 5 15 2328 105 1 4 1 0 925 541986967730340012320893631 [(128,182468775683251189594366432),(128,142934909065883303007007200),(128,103154846379662627858727392),(128,66102761079846937313464800),(128,34703098987553731124847072),(128,11830838883823662267953632),(128,791737650318561154527103),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_15_2328_1 : fastPhase (bank 5 15).shape 179818 2328 105 1 4 1 1 = 540423341348278331938609958 := mkP 5 15 2328 105 1 4 1 1 925 540423341348278331938609958 [(128,182171945378168595271262176),(128,142623521578379604092833760),(128,102852503580170087030816736),(128,65832673242798194801389536),(128,34488086835911788090417120),(128,11693335633611864185212896),(128,761275099238198466677734),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_15 : Checked (bank 5 15) 105 4 1 := by
  refine checked_from_values (bank 5 15) 105 4 1
    (P3_7_1.checked (bank 5 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_15_2327_0 rec_5_15_2327_1 rec_5_15_2328_0 rec_5_15_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_16_2327_0 : fastPhase (bank 5 16).shape 179818 2327 138 1 4 1 0 = 1628135441445074025920511690 := mkP 5 16 2327 138 1 4 1 0 925 1628135441445074025920511690 [(128,546770089980621546750676320),(128,429083888607565202157821280),(128,310225287644267214319889760),(128,199152739553999048216542560),(128,104738341716173833937374560),(128,35768097024851820289891680),(128,2396996917595360248315530),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_16_2327_1 : fastPhase (bank 5 16).shape 179818 2327 138 1 4 1 1 = 1623454199453922809569365308 := mkP 5 16 2327 138 1 4 1 1 925 1623454199453922809569365308 [(128,545888392853961995921343456),(128,428155169446868714972255200),(128,309320378973832065849811936),(128,198341794633998494131401696),(128,104090836587217086368351200),(128,35352832552545023693902816),(128,2304794405499428632299004),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_16_2328_0 : fastPhase (bank 5 16).shape 179818 2328 138 1 4 1 0 = 1628142336135890649474271515 := mkP 5 16 2328 138 1 4 1 0 925 1628142336135890649474271515 [(128,546773966548370080719025120),(128,429085907251588701316744160),(128,310226141489493735959647200),(128,199152964259221281010230240),(128,104738316957426520173376480),(128,35768047974347151128118240),(128,2396991655443179167130075),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_5_16_2328_1 : fastPhase (bank 5 16).shape 179818 2328 138 1 4 1 1 = 1623461065794317130557328992 := mkP 5 16 2328 138 1 4 1 1 925 1623461065794317130557328992 [(128,545892256091992959191849184),(128,428157179535784626845731040),(128,309321228021442142444124384),(128,198342017292033470598523104),(128,104090811534675646642804960),(128,35352783974598203264993504),(128,2304789343790081569302816),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_5_16 : Checked (bank 5 16) 138 4 1 := by
  refine checked_from_values (bank 5 16) 138 4 1
    (P3_7_1.checked (bank 5 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_16_2327_0 rec_5_16_2327_1 rec_5_16_2328_0 rec_5_16_2328_1 (by decide +kernel) (by decide +kernel)

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
