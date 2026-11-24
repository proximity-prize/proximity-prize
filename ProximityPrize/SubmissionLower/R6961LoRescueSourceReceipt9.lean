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


private theorem rec_9_0_2327_0 : fastPhase (bank 9 0).shape 179818 2327 0 1 4 12 0 = 800165917884667702992 := mkP 9 0 2327 0 1 4 12 0 130 800165917884667702992 [(128,800165917884667702992),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_0_2327_1 : fastPhase (bank 9 0).shape 179818 2327 0 1 4 12 1 = 780487588484981201604 := mkP 9 0 2327 0 1 4 12 1 130 780487588484981201604 [(128,780487588484981201604),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_0_2328_0 : fastPhase (bank 9 0).shape 179818 2328 0 1 4 12 0 = 800170403944542463560 := mkP 9 0 2328 0 1 4 12 0 130 800170403944542463560 [(128,800170403944542463560),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_0_2328_1 : fastPhase (bank 9 0).shape 179818 2328 0 1 4 12 1 = 780491925575461410168 := mkP 9 0 2328 0 1 4 12 1 130 780491925575461410168 [(128,780491925575461410168),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_0 : Checked (bank 9 0) 0 4 12 := by
  refine checked_from_values (bank 9 0) 0 4 12
    (P3_7_1.checked (bank 9 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_0_2327_0 rec_9_0_2327_1 rec_9_0_2328_0 rec_9_0_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_1_2327_0 : fastPhase (bank 9 1).shape 179818 2327 1 1 4 12 0 = 912287961623868368544 := mkP 9 1 2327 1 1 4 12 0 130 912287961623868368544 [(128,912287961623868368544),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_1_2327_1 : fastPhase (bank 9 1).shape 179818 2327 1 1 4 12 1 = 890110187401185313776 := mkP 9 1 2327 1 1 4 12 1 130 890110187401185313776 [(128,890110187401185313776),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_1_2328_0 : fastPhase (bank 9 1).shape 179818 2328 1 1 4 12 0 = 912293007617633637960 := mkP 9 1 2328 1 1 4 12 0 130 912293007617633637960 [(128,912293007617633637960),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_1_2328_1 : fastPhase (bank 9 1).shape 179818 2328 1 1 4 12 1 = 890115067257251419608 := mkP 9 1 2328 1 1 4 12 1 130 890115067257251419608 [(128,890115067257251419608),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_1 : Checked (bank 9 1) 1 4 12 := by
  refine checked_from_values (bank 9 1) 1 4 12
    (P3_7_1.checked (bank 9 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_1_2327_0 rec_9_1_2327_1 rec_9_1_2328_0 rec_9_1_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_2_2327_0 : fastPhase (bank 9 2).shape 179818 2327 2 1 4 12 0 = 1048715417420423809176 := mkP 9 2 2327 2 1 4 12 0 130 1048715417420423809176 [(128,1048715417420423809176),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_2_2327_1 : fastPhase (bank 9 2).shape 179818 2327 2 1 4 12 1 = 1023515054297687244348 := mkP 9 2 2327 2 1 4 12 1 130 1023515054297687244348 [(128,1023515054297687244348),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_2_2328_0 : fastPhase (bank 9 2).shape 179818 2328 2 1 4 12 0 = 1048721139249399866370 := mkP 9 2 2328 2 1 4 12 0 130 1048721139249399866370 [(128,1048721139249399866370),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_2_2328_1 : fastPhase (bank 9 2).shape 179818 2328 2 1 4 12 1 = 1023520589346211514178 := mkP 9 2 2328 2 1 4 12 1 130 1023520589346211514178 [(128,1023520589346211514178),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_2 : Checked (bank 9 2) 2 4 12 := by
  refine checked_from_values (bank 9 2) 2 4 12
    (P3_7_1.checked (bank 9 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_2_2327_0 rec_9_2_2327_1 rec_9_2_2328_0 rec_9_2_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_3_2327_0 : fastPhase (bank 9 3).shape 179818 2327 3 1 4 12 0 = 1216550826861848871216 := mkP 9 3 2327 3 1 4 12 0 130 1216550826861848871216 [(128,1216550826861848871216),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_3_2327_1 : fastPhase (bank 9 3).shape 179818 2327 3 1 4 12 1 = 1187654800442604016008 := mkP 9 3 2327 3 1 4 12 1 130 1187654800442604016008 [(128,1187654800442604016008),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_3_2328_0 : fastPhase (bank 9 3).shape 179818 2328 3 1 4 12 0 = 1216557373303419837456 := mkP 9 3 2328 3 1 4 12 0 130 1216557373303419837456 [(128,1216557373303419837456),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_3_2328_1 : fastPhase (bank 9 3).shape 179818 2328 3 1 4 12 1 = 1187661135013528730784 := mkP 9 3 2328 3 1 4 12 1 130 1187661135013528730784 [(128,1187661135013528730784),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_3 : Checked (bank 9 3) 3 4 12 := by
  refine checked_from_values (bank 9 3) 3 4 12
    (P3_7_1.checked (bank 9 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_3_2327_0 rec_9_3_2327_1 rec_9_3_2328_0 rec_9_3_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_4_2327_0 : fastPhase (bank 9 4).shape 179818 2327 4 1 4 12 0 = 1426182702039190767624 := mkP 9 4 2327 4 1 4 12 0 130 1426182702039190767624 [(128,1426182702039190767624),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_4_2327_1 : fastPhase (bank 9 4).shape 179818 2327 4 1 4 12 1 = 1392698857088842038376 := mkP 9 4 2327 4 1 4 12 1 130 1392698857088842038376 [(128,1392698857088842038376),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_4_2328_0 : fastPhase (bank 9 4).shape 179818 2328 4 1 4 12 0 = 1426190270037939734063 := mkP 9 4 2328 4 1 4 12 0 130 1426190270037939734063 [(128,1426190270037939734063),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_4_2328_1 : fastPhase (bank 9 4).shape 179818 2328 4 1 4 12 1 = 1392706182254810664231 := mkP 9 4 2328 4 1 4 12 1 130 1392706182254810664231 [(128,1392706182254810664231),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_4 : Checked (bank 9 4) 4 4 12 := by
  refine checked_from_values (bank 9 4) 4 4 12
    (P3_7_1.checked (bank 9 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_4_2327_0 rec_9_4_2327_1 rec_9_4_2328_0 rec_9_4_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_5_2327_0 : fastPhase (bank 9 5).shape 179818 2327 5 1 4 12 0 = 1693012868434002273756 := mkP 9 5 2327 5 1 4 12 0 130 1693012868434002273756 [(128,1693012868434002273756),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_5_2327_1 : fastPhase (bank 9 5).shape 179818 2327 5 1 4 12 1 = 1653724995093254030688 := mkP 9 5 2327 5 1 4 12 1 130 1653724995093254030688 [(128,1653724995093254030688),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_5_2328_0 : fastPhase (bank 9 5).shape 179818 2328 5 1 4 12 0 = 1693021726221470793798 := mkP 9 5 2328 5 1 4 12 0 130 1693021726221470793798 [(128,1693021726221470793798),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_5_2328_1 : fastPhase (bank 9 5).shape 179818 2328 5 1 4 12 1 = 1653733571109198599046 := mkP 9 5 2328 5 1 4 12 1 130 1653733571109198599046 [(128,1653733571109198599046),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_5 : Checked (bank 9 5) 5 4 12 := by
  refine checked_from_values (bank 9 5) 5 4 12
    (P3_7_1.checked (bank 9 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_5_2327_0 rec_9_5_2327_1 rec_9_5_2328_0 rec_9_5_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_6_2327_0 : fastPhase (bank 9 6).shape 179818 2327 7 1 4 12 0 = 2498926741365091329648 := mkP 9 6 2327 7 1 4 12 0 130 2498926741365091329648 [(128,2498926741365091329648),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_6_2327_1 : fastPhase (bank 9 6).shape 179818 2327 7 1 4 12 1 = 2442275727243928713480 := mkP 9 6 2327 7 1 4 12 1 130 2442275727243928713480 [(128,2442275727243928713480),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_6_2328_0 : fastPhase (bank 9 6).shape 179818 2328 7 1 4 12 0 = 2498939444878571354784 := mkP 9 6 2328 7 1 4 12 0 130 2498939444878571354784 [(128,2498939444878571354784),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_6_2328_1 : fastPhase (bank 9 6).shape 179818 2328 7 1 4 12 1 = 2442288033603708976272 := mkP 9 6 2328 7 1 4 12 1 130 2442288033603708976272 [(128,2442288033603708976272),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_6 : Checked (bank 9 6) 7 4 12 := by
  refine checked_from_values (bank 9 6) 7 4 12
    (P3_7_1.checked (bank 9 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_6_2327_0 rec_9_6_2327_1 rec_9_6_2328_0 rec_9_6_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_7_2327_0 : fastPhase (bank 9 7).shape 179818 2327 10 1 4 12 0 = 5346189378765046724220 := mkP 9 7 2327 10 1 4 12 0 130 5346189378765046724220 [(128,5346189378765046724220),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_7_2327_1 : fastPhase (bank 9 7).shape 179818 2327 10 1 4 12 1 = 5229182229651278289192 := mkP 9 7 2327 10 1 4 12 1 130 5229182229651278289192 [(128,5229182229651278289192),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_7_2328_0 : fastPhase (bank 9 7).shape 179818 2328 10 1 4 12 0 = 5346215374689210849171 := mkP 9 7 2328 10 1 4 12 0 130 5346215374689210849171 [(128,5346215374689210849171),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_7_2328_1 : fastPhase (bank 9 7).shape 179818 2328 10 1 4 12 1 = 5229207433911951784779 := mkP 9 7 2328 10 1 4 12 1 130 5229207433911951784779 [(128,5229207433911951784779),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_7 : Checked (bank 9 7) 10 4 12 := by
  refine checked_from_values (bank 9 7) 10 4 12
    (P3_7_1.checked (bank 9 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_7_2327_0 rec_9_7_2327_1 rec_9_7_2328_0 rec_9_7_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_8_2327_0 : fastPhase (bank 9 8).shape 179818 2327 16 1 4 12 0 = 28622654289606684528612 := mkP 9 8 2327 16 1 4 12 0 191 28622654289606684528612 [(128,27905087691940708123776),(63,717566597665976404836)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_8_2327_1 : fastPhase (bank 9 8).shape 179818 2327 16 1 4 12 1 = 28183107938825533918968 := mkP 9 8 2327 16 1 4 12 1 191 28183107938825533918968 [(128,27507562027560752663808),(63,675545911264781255160)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_8_2328_0 : fastPhase (bank 9 8).shape 179818 2328 16 1 4 12 0 = 28622793675625498823562 := mkP 9 8 2328 16 1 4 12 0 191 28622793675625498823562 [(128,27905227768846119835968),(63,717565906779378987594)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_8_2328_1 : fastPhase (bank 9 8).shape 179818 2328 16 1 4 12 1 = 28183244351405207582442 := mkP 9 8 2328 16 1 4 12 1 191 28183244351405207582442 [(128,27507699095832026526528),(63,675545255573181055914)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_8 : Checked (bank 9 8) 16 4 12 := by
  refine checked_from_values (bank 9 8) 16 4 12
    (P3_7_1.checked (bank 9 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_8_2327_0 rec_9_8_2327_1 rec_9_8_2328_0 rec_9_8_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_9_2327_0 : fastPhase (bank 9 9).shape 179818 2327 10 1 4 12 0 = 5346189378765046724220 := mkP 9 9 2327 10 1 4 12 0 130 5346189378765046724220 [(128,5346189378765046724220),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_9_2327_1 : fastPhase (bank 9 9).shape 179818 2327 10 1 4 12 1 = 5229182229651278289192 := mkP 9 9 2327 10 1 4 12 1 130 5229182229651278289192 [(128,5229182229651278289192),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_9_2328_0 : fastPhase (bank 9 9).shape 179818 2328 10 1 4 12 0 = 5346215374689210849171 := mkP 9 9 2328 10 1 4 12 0 130 5346215374689210849171 [(128,5346215374689210849171),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_9_2328_1 : fastPhase (bank 9 9).shape 179818 2328 10 1 4 12 1 = 5229207433911951784779 := mkP 9 9 2328 10 1 4 12 1 130 5229207433911951784779 [(128,5229207433911951784779),(2,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_9 : Checked (bank 9 9) 10 4 12 := by
  refine checked_from_values (bank 9 9) 10 4 12
    (P3_7_1.checked (bank 9 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_9_2327_0 rec_9_9_2327_1 rec_9_9_2328_0 rec_9_9_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_10_2327_0 : fastPhase (bank 9 10).shape 179818 2327 20 1 4 12 0 = 58670173889412605027172 := mkP 9 10 2327 20 1 4 12 0 191 58670173889412605027172 [(128,57091416691768493086080),(63,1578757197644111941092)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_10_2327_1 : fastPhase (bank 9 10).shape 179818 2327 20 1 4 12 1 = 57797455568562975912624 := mkP 9 10 2327 20 1 4 12 1 191 57797455568562975912624 [(128,56310235782839544821760),(63,1487219785723431090864)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_10_2328_0 : fastPhase (bank 9 10).shape 179818 2328 20 1 4 12 0 = 58670447950321679751300 := mkP 9 10 2328 20 1 4 12 0 191 58670447950321679751300 [(128,57091692434615448961920),(63,1578755515706230789380)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_10_2328_1 : fastPhase (bank 9 10).shape 179818 2328 20 1 4 12 1 = 57797723918703276450948 := mkP 9 10 2328 20 1 4 12 1 191 57797723918703276450948 [(128,56310505728471755528832),(63,1487218190231520922116)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_10 : Checked (bank 9 10) 20 4 12 := by
  refine checked_from_values (bank 9 10) 20 4 12
    (P3_7_1.checked (bank 9 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_10_2327_0 rec_9_10_2327_1 rec_9_10_2328_0 rec_9_10_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_11_2327_0 : fastPhase (bank 9 11).shape 179818 2327 32 1 4 12 0 = 426346515516761690896062 := mkP 9 11 2327 32 1 4 12 0 278 426346515516761690896062 [(128,364233163027571779420992),(128,62113352489189911475070),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_11_2327_1 : fastPhase (bank 9 11).shape 179818 2327 32 1 4 12 1 = 421925862359895756201804 := mkP 9 11 2327 32 1 4 12 1 278 421925862359895756201804 [(128,361176565336100591307840),(128,60749297023795164893964),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_11_2328_0 : fastPhase (bank 9 11).shape 179818 2328 32 1 4 12 0 = 426348483198956257475670 := mkP 9 11 2328 32 1 4 12 0 278 426348483198956257475670 [(128,364235112567702243067584),(128,62113370631254014408086),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_11_2328_1 : fastPhase (bank 9 11).shape 179818 2328 32 1 4 12 1 = 421927801400242037276220 := mkP 9 11 2328 32 1 4 12 1 278 421927801400242037276220 [(128,361178487129190080187968),(128,60749314271051957088252),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_11 : Checked (bank 9 11) 32 4 12 := by
  refine checked_from_values (bank 9 11) 32 4 12
    (P3_7_1.checked (bank 9 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_11_2327_0 rec_9_11_2327_1 rec_9_11_2328_0 rec_9_11_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_12_2327_0 : fastPhase (bank 9 12).shape 179818 2327 31 1 4 12 0 = 375441174078500851357269 := mkP 9 12 2327 31 1 4 12 0 278 375441174078500851357269 [(128,321184513259943839605440),(128,54256660818557011751829),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_12_2327_1 : fastPhase (bank 9 12).shape 179818 2327 31 1 4 12 1 = 371526781871945992997664 := mkP 9 12 2327 31 1 4 12 1 278 371526781871945992997664 [(128,318465260159658332424576),(128,53061521712287660573088),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_12_2328_0 : fastPhase (bank 9 12).shape 179818 2328 31 1 4 12 0 = 375442919639046519758793 := mkP 9 12 2328 31 1 4 12 0 278 375442919639046519758793 [(128,321186241853797739289184),(128,54256677785248780469609),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_12_2328_1 : fastPhase (bank 9 12).shape 179818 2328 31 1 4 12 1 = 371528501921216132013638 := mkP 9 12 2328 31 1 4 12 1 278 371528501921216132013638 [(128,318466964052911306621728),(128,53061537868304825391910),(22,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_12 : Checked (bank 9 12) 31 4 12 := by
  refine checked_from_values (bank 9 12) 31 4 12
    (P3_7_1.checked (bank 9 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_12_2327_0 rec_9_12_2327_1 rec_9_12_2328_0 rec_9_12_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_13_2327_0 : fastPhase (bank 9 13).shape 179818 2327 44 1 4 12 0 = 1971954975804289287276780 := mkP 9 13 2327 44 1 4 12 0 370 1971954975804289287276780 [(128,1437988715969940787310784),(128,495420098565229114527936),(114,38546161269119385438060)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_13_2327_1 : fastPhase (bank 9 13).shape 179818 2327 44 1 4 12 1 = 1956464841754229078761155 := mkP 9 13 2327 44 1 4 12 1 370 1956464841754229078761155 [(128,1429536644639779997303424),(128,489678588926525509345920),(114,37249608187923572111811)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_13_2328_0 : fastPhase (bank 9 13).shape 179818 2328 44 1 4 12 0 = 1971964068670851852921870 := mkP 9 13 2328 44 1 4 12 0 370 1971964068670851852921870 [(128,1437997177694082238867488),(128,495420778713027946362912),(114,38546112263741667691470)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_13_2328_1 : fastPhase (bank 9 13).shape 179818 2328 44 1 4 12 1 = 1956473834334473116989225 := mkP 9 13 2328 44 1 4 12 1 370 1956473834334473116989225 [(128,1429545018478279696809696),(128,489679255158741449821920),(114,37249560697451970357609)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_13 : Checked (bank 9 13) 44 4 12 := by
  refine checked_from_values (bank 9 13) 44 4 12
    (P3_7_1.checked (bank 9 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_13_2327_0 rec_9_13_2327_1 rec_9_13_2328_0 rec_9_13_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_14_2327_0 : fastPhase (bank 9 14).shape 179818 2327 76 1 4 12 0 = 42191448320051484857589168 := mkP 9 14 2327 76 1 4 12 0 678 42191448320051484857589168 [(128,20101422528649845074259072),(128,12715405199199990872157312),(128,6653065054350844322704512),(128,2425951344429602398514304),(128,295604193421202189953968),(38,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_14_2327_1 : fastPhase (bank 9 14).shape 179818 2327 76 1 4 12 1 = 42004744366627327743510336 := mkP 9 14 2327 76 1 4 12 1 678 42004744366627327743510336 [(128,20040963683784117562566144),(128,12662330720385990394603008),(128,6612570094209245106660864),(128,2401000897619372928689664),(128,287878970628601750990656),(38,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_14_2328_0 : fastPhase (bank 9 14).shape 179818 2328 76 1 4 12 0 = 42191647118975194657767465 := mkP 9 14 2328 76 1 4 12 0 678 42191647118975194657767465 [(128,20101562550516092121593568),(128,12715454827149338200393440),(128,6653075370779000729327328),(128,2425950653000362543834848),(128,295603717530401062618281),(38,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_14_2328_1 : fastPhase (bank 9 14).shape 179818 2328 76 1 4 12 1 = 42004941936487605926528637 := mkP 9 14 2328 76 1 4 12 1 678 42004941936487605926528637 [(128,20041102941445811549433696),(128,12662379992983023545565024),(128,6612580294522665827012448),(128,2401000200837201243529056),(128,287878506698903760988413),(38,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_14 : Checked (bank 9 14) 76 4 12 := by
  refine checked_from_values (bank 9 14) 76 4 12
    (P3_7_1.checked (bank 9 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_14_2327_0 rec_9_14_2327_1 rec_9_14_2328_0 rec_9_14_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_15_2327_0 : fastPhase (bank 9 15).shape 179818 2327 105 1 4 12 0 = 253672958527388230994562753 := mkP 9 15 2327 105 1 4 12 0 925 253672958527388230994562753 [(128,93489835454575061730972480),(128,68523758195403031064195904),(128,46160054063406221265048384),(128,27542845935038993301599040),(128,13434727671323758472549184),(128,4254290302636297955914560),(128,267446905004867204283201),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_15_2327_1 : fastPhase (bank 9 15).shape 179818 2327 105 1 4 12 1 = 252846059950550451341534541 := mkP 9 15 2327 105 1 4 12 1 925 252846059950550451341534541 [(128,93290140763714644210543488),(128,68338327696491434759441280),(128,45999544695993181096487808),(128,27414768634801469274917760),(128,13343741786846460095261568),(128,4202498012192208654027648),(128,257038360511053250854989),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_15_2328_0 : fastPhase (bank 9 15).shape 179818 2328 105 1 4 12 0 = 253674153296719734380450469 := mkP 9 15 2328 105 1 4 12 0 925 253674153296719734380450469 [(128,93490523488313047918644000),(128,68524097237660367818955552),(128,46160191346103693055240992),(128,27542882622972775312046880),(128,13434727027380931905145632),(128,4254285213358480755252000),(128,267446360930437615165413),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_15_2328_1 : fastPhase (bank 9 15).shape 179818 2328 105 1 4 12 1 = 252847249278608998074386076 := mkP 9 15 2328 105 1 4 12 1 925 252847249278608998074386076 [(128,93290826096469551337871328),(128,68338665140273528902756320),(128,45999681151066803470120928),(128,27414804992038620376451040),(128,13343741088479397308979168),(128,4202492972914159279400928),(128,257037837366937398806364),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_15 : Checked (bank 9 15) 105 4 12 := by
  refine checked_from_values (bank 9 15) 105 4 12
    (P3_7_1.checked (bank 9 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_15_2327_0 rec_9_15_2327_1 rec_9_15_2328_0 rec_9_15_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_16_2327_0 : fastPhase (bank 9 16).shape 179818 2327 138 1 4 12 0 = 788703233046163449162386202 := mkP 9 16 2327 138 1 4 12 0 925 788703233046163449162386202 [(128,279110596477226796453579840),(128,210832324394519507797486656),(128,146611908165448194944961600),(128,90463674482297760748792896),(128,45707143841604899220442176),(128,15004556728943415078726720),(128,973028956122874918396314),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_16_2327_1 : fastPhase (bank 9 16).shape 179818 2327 138 1 4 12 1 = 786269186648128016563981878 := mkP 9 16 2327 138 1 4 12 1 925 786269186648128016563981878 [(128,278578256588105253302298048),(128,210312642535619180179457472),(128,146139389622140408644969920),(128,90067218083928878554465728),(128,45410336378276845338912192),(128,14825967368294199553295808),(128,935376071763250990582710),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_16_2328_0 : fastPhase (bank 9 16).shape 179818 2328 138 1 4 12 0 = 788706681214124024313508344 := mkP 9 16 2328 138 1 4 12 0 925 788706681214124024313508344 [(128,279112577688965391389007360),(128,210833317723193186187812352),(128,146612312545890400171630080),(128,90463777002744966816210432),(128,45707133230539058643574272),(128,15004536202282522195729920),(128,973026820508498909543928),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_9_16_2328_1 : fastPhase (bank 9 16).shape 179818 2328 138 1 4 12 1 = 786272619717125515300214508 := mkP 9 16 2328 138 1 4 12 1 925 786272619717125515300214508 [(128,278580230405866697922711552),(128,210313631358091096245866496),(128,146139791608518227338334208),(128,90067319640543043893399552),(128,45410325640972344370139136),(128,14825947045158207967137792),(128,935374017975897562625772),(29,0)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_9_16 : Checked (bank 9 16) 138 4 12 := by
  refine checked_from_values (bank 9 16) 138 4 12
    (P3_7_1.checked (bank 9 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_16_2327_0 rec_9_16_2327_1 rec_9_16_2328_0 rec_9_16_2328_1 (by decide +kernel) (by decide +kernel)

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
