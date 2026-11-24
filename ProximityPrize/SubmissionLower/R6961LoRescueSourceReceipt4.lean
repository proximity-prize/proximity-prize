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


private theorem rec_4_1_2327_0 : fastPhase (bank 4 1).shape 179818 2327 1 1 2 1 0 = 23187701434234290747222 := mkP 4 1 2327 1 1 2 1 0 130 23187701434234290747222 [(128,23182923303370610484672),(2,4778130863680262550)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_1_2327_1 : fastPhase (bank 4 1).shape 179818 2327 1 1 2 1 1 = 22782890290599224485362 := mkP 4 1 2327 1 1 2 1 1 130 22782890290599224485362 [(128,22781308696199555539392),(2,1581594399668945970)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_1_2328_0 : fastPhase (bank 4 1).shape 179818 2328 1 1 2 1 0 = 23187837646740903908759 := mkP 4 1 2328 1 1 2 1 0 130 23187837646740903908759 [(128,23183059519092082271264),(2,4778127648821637495)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_1_2328_1 : fastPhase (bank 4 1).shape 179818 2328 1 1 2 1 1 = 22783023868974791392919 := mkP 4 1 2328 1 1 2 1 1 130 22783023868974791392919 [(128,22781442275632197491744),(2,1581593342593901175)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_1 : Checked (bank 4 1) 1 2 1 := by
  refine checked_from_values (bank 4 1) 1 2 1
    (P3_7_1.checked (bank 4 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_1_2327_0 rec_4_1_2327_1 rec_4_1_2328_0 rec_4_1_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_2_2327_0 : fastPhase (bank 4 2).shape 179818 2327 2 1 2 1 0 = 36451444478137735227948 := mkP 4 2 2327 2 1 2 1 0 130 36451444478137735227948 [(128,36443918512462025407488),(2,7525965675709820460)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_2_2327_1 : fastPhase (bank 4 2).shape 179818 2327 2 1 2 1 1 = 35815622976040771717308 := mkP 4 2 2327 2 1 2 1 1 130 35815622976040771717308 [(128,35813131792716219512256),(2,2491183324552205052)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_2_2328_0 : fastPhase (bank 4 2).shape 179818 2328 2 1 2 1 0 = 36451656622682082164942 := mkP 4 2 2328 2 1 2 1 0 130 36451656622682082164942 [(128,36444130662400921825088),(2,7525960281160339854)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_2_2328_1 : fastPhase (bank 4 2).shape 179818 2328 2 1 2 1 1 = 35815831021951018751102 := mkP 4 2 2328 2 1 2 1 1 130 35815831021951018751102 [(128,35813339840400836624960),(2,2491181550182126142)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_2 : Checked (bank 4 2) 2 2 1 := by
  refine checked_from_values (bank 4 2) 2 2 1
    (P3_7_1.checked (bank 4 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_2_2327_0 rec_4_2_2327_1 rec_4_2_2328_0 rec_4_2_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_3_2327_0 : fastPhase (bank 4 3).shape 179818 2327 3 1 2 1 0 = 107591661640962182281824 := mkP 4 3 2327 3 1 2 1 0 191 107591661640962182281824 [(128,98821137950578474615872),(63,8770523690383707665952)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_3_2327_1 : fastPhase (bank 4 3).shape 179818 2327 3 1 2 1 1 = 106307978345286291281952 := mkP 4 3 2327 3 1 2 1 1 191 106307978345286291281952 [(128,97838731458257927963328),(63,8469246887028363318624)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_3_2328_0 : fastPhase (bank 4 3).shape 179818 2328 3 1 2 1 0 = 107592287979398293099472 := mkP 4 3 2328 3 1 2 1 0 191 107592287979398293099472 [(128,98821754969183478744032),(63,8770533010214814355440)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_3_2328_1 : fastPhase (bank 4 3).shape 179818 2328 3 1 2 1 1 = 106308596405519573081040 := mkP 4 3 2328 3 1 2 1 1 191 106308596405519573081040 [(128,97839340519882778614752),(63,8469255885636794466288)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_3 : Checked (bank 4 3) 3 2 1 := by
  refine checked_from_values (bank 4 3) 3 2 1
    (P3_7_1.checked (bank 4 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_3_2327_0 rec_4_3_2327_1 rec_4_3_2328_0 rec_4_3_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_4_2327_0 : fastPhase (bank 4 4).shape 179818 2327 4 1 2 1 0 = 130689785267361315700032 := mkP 4 4 2327 4 1 2 1 0 191 130689785267361315700032 [(128,120026724270364674986880),(63,10663060996996640713152)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_4_2327_1 : fastPhase (bank 4 4).shape 179818 2327 4 1 2 1 1 = 129131427110464481337312 := mkP 4 4 2327 4 1 2 1 1 191 129131427110464481337312 [(128,118834581036088421417472),(63,10296846074376059919840)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_4_2328_0 : fastPhase (bank 4 4).shape 179818 2328 4 1 2 1 0 = 130690541253071103408384 := mkP 4 4 2328 4 1 2 1 0 191 130690541253071103408384 [(128,120027469261595702951424),(63,10663071991475400456960)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_4_2328_1 : fastPhase (bank 4 4).shape 179818 2328 4 1 2 1 1 = 129132173110869099447120 := mkP 4 4 2328 4 1 2 1 1 191 129132173110869099447120 [(128,118835316420539324498688),(63,10296856690329774948432)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_4 : Checked (bank 4 4) 4 2 1 := by
  refine checked_from_values (bank 4 4) 4 2 1
    (P3_7_1.checked (bank 4 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_4_2327_0 rec_4_4_2327_1 rec_4_4_2328_0 rec_4_4_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_5_2327_0 : fastPhase (bank 4 5).shape 179818 2327 5 1 2 1 0 = 162089489550985177204800 := mkP 4 5 2327 5 1 2 1 0 191 162089489550985177204800 [(128,148852538074818994308480),(63,13236951476166182896320)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_5_2327_1 : fastPhase (bank 4 5).shape 179818 2327 5 1 2 1 1 = 160157846404980325692000 := mkP 4 5 2327 5 1 2 1 1 191 160157846404980325692000 [(128,147375418294351674705600),(63,12782428110628650986400)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_5_2328_0 : fastPhase (bank 4 5).shape 179818 2328 5 1 2 1 0 = 162090421195820040533664 := mkP 4 5 2328 5 1 2 1 0 191 162090421195820040533664 [(128,148853456488970630605248),(63,13236964706849409928416)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_5_2328_1 : fastPhase (bank 4 5).shape 179818 2328 5 1 2 1 1 = 160158765752273516428224 := mkP 4 5 2328 5 1 2 1 1 191 160158765752273516428224 [(128,147376324865948495821248),(63,12782440886325020606976)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_5 : Checked (bank 4 5) 5 2 1 := by
  refine checked_from_values (bank 4 5) 5 2 1
    (P3_7_1.checked (bank 4 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_5_2327_0 rec_4_5_2327_1 rec_4_5_2328_0 rec_4_5_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_6_2327_0 : fastPhase (bank 4 6).shape 179818 2327 7 1 2 1 0 = 271429606405844247276000 := mkP 4 6 2327 7 1 2 1 0 191 271429606405844247276000 [(128,249223368295261941717312),(63,22206238110582305558688)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_6_2327_1 : fastPhase (bank 4 6).shape 179818 2327 7 1 2 1 1 = 268198717438453637262240 := mkP 4 6 2327 7 1 2 1 1 191 268198717438453637262240 [(128,246754684173885221364480),(63,21444033264568415897760)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_6_2328_0 : fastPhase (bank 4 6).shape 179818 2328 7 1 2 1 0 = 271431146492613300316464 := mkP 4 6 2328 7 1 2 1 0 191 271431146492613300316464 [(128,249224887588008503908896),(63,22206258904604796407568)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_6_2328_1 : fastPhase (bank 4 6).shape 179818 2328 7 1 2 1 1 = 268200237222634536163584 := mkP 4 6 2328 7 1 2 1 1 191 268200237222634536163584 [(128,246756183877327024865568),(63,21444053345307511298016)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_6 : Checked (bank 4 6) 7 2 1 := by
  refine checked_from_values (bank 4 6) 7 2 1
    (P3_7_1.checked (bank 4 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_6_2327_0 rec_4_6_2327_1 rec_4_6_2328_0 rec_4_6_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_7_2327_0 : fastPhase (bank 4 7).shape 179818 2327 10 1 2 1 0 = 1152730967867687019757374 := mkP 4 7 2327 10 1 2 1 0 278 1152730967867687019757374 [(128,872427990978029221257504),(128,275670708794224826069280),(22,4632268095432972430590)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_7_2327_1 : fastPhase (bank 4 7).shape 179818 2327 10 1 2 1 1 = 1143260484241737966496209 := mkP 4 7 2327 10 1 2 1 1 278 1143260484241737966496209 [(128,867154844453728604871264),(128,271888914702649120025184),(22,4216725085360241599761)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_7_2328_0 : fastPhase (bank 4 7).shape 179818 2328 10 1 2 1 0 = 1152737505386623603202118 := mkP 4 7 2328 10 1 2 1 0 278 1152737505386623603202118 [(128,872433898226294334407328),(128,275671341373513503306400),(22,4632265786815765488390)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_7_2328_1 : fastPhase (bank 4 7).shape 179818 2328 10 1 2 1 1 = 1143266962229402726544723 := mkP 4 7 2328 10 1 2 1 1 278 1143266962229402726544723 [(128,867160701997593803778208),(128,271889537240718928345248),(22,4216722991089994421267)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_7 : Checked (bank 4 7) 10 2 1 := by
  refine checked_from_values (bank 4 7) 10 2 1
    (P3_7_1.checked (bank 4 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_7_2327_0 rec_4_7_2327_1 rec_4_7_2328_0 rec_4_7_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_8_2327_0 : fastPhase (bank 4 8).shape 179818 2327 16 1 2 1 0 = 3312744062747318919578166 := mkP 4 8 2327 16 1 2 1 0 278 3312744062747318919578166 [(128,2505121700095754330803616),(128,794241513851039322725792),(22,13380848800525266048758)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_8_2327_1 : fastPhase (bank 4 8).shape 179818 2327 16 1 2 1 1 = 3285593581998561903751071 := mkP 4 8 2327 16 1 2 1 1 278 3285593581998561903751071 [(128,2490048726895724186304096),(128,783364112991174648712800),(22,12180742111663068734175)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_8_2328_0 : fastPhase (bank 4 8).shape 179818 2328 16 1 2 1 0 = 3312762345372070977309330 := mkP 4 8 2328 16 1 2 1 0 278 3312762345372070977309330 [(128,2505138276809213603615200),(128,794243228097610753728992),(22,13380840465246619965138)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_8_2328_1 : fastPhase (bank 4 8).shape 179818 2328 16 1 2 1 1 = 3285611698587811756899701 := mkP 4 8 2328 16 1 2 1 1 278 3285611698587811756899701 [(128,2490065164109404249766496),(128,783365799932423240706656),(22,12180734545984266426549)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_8 : Checked (bank 4 8) 16 2 1 := by
  refine checked_from_values (bank 4 8) 16 2 1
    (P3_7_1.checked (bank 4 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_8_2327_0 rec_4_8_2327_1 rec_4_8_2328_0 rec_4_8_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_9_2327_0 : fastPhase (bank 4 9).shape 179818 2327 10 1 2 1 0 = 1152730967867687019757374 := mkP 4 9 2327 10 1 2 1 0 278 1152730967867687019757374 [(128,872427990978029221257504),(128,275670708794224826069280),(22,4632268095432972430590)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_9_2327_1 : fastPhase (bank 4 9).shape 179818 2327 10 1 2 1 1 = 1143260484241737966496209 := mkP 4 9 2327 10 1 2 1 1 278 1143260484241737966496209 [(128,867154844453728604871264),(128,271888914702649120025184),(22,4216725085360241599761)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_9_2328_0 : fastPhase (bank 4 9).shape 179818 2328 10 1 2 1 0 = 1152737505386623603202118 := mkP 4 9 2328 10 1 2 1 0 278 1152737505386623603202118 [(128,872433898226294334407328),(128,275671341373513503306400),(22,4632265786815765488390)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_9_2328_1 : fastPhase (bank 4 9).shape 179818 2328 10 1 2 1 1 = 1143266962229402726544723 := mkP 4 9 2328 10 1 2 1 1 278 1143266962229402726544723 [(128,867160701997593803778208),(128,271889537240718928345248),(22,4216722991089994421267)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_9 : Checked (bank 4 9) 10 2 1 := by
  refine checked_from_values (bank 4 9) 10 2 1
    (P3_7_1.checked (bank 4 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_9_2327_0 rec_4_9_2327_1 rec_4_9_2328_0 rec_4_9_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_10_2327_0 : fastPhase (bank 4 10).shape 179818 2327 20 1 2 1 0 = 9184856516149269188626533 := mkP 4 10 2327 20 1 2 1 0 370 9184856516149269188626533 [(128,5721964261799133636913248),(128,2820784412476043635611744),(114,642107841874091916101541)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_10_2327_1 : fastPhase (bank 4 10).shape 179818 2327 20 1 2 1 1 = 9128188326525217944267393 := mkP 4 10 2327 20 1 2 1 1 370 9128188326525217944267393 [(128,5697749052982827867231072),(128,2800566585017533360816992),(114,629872688524856716219329)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_10_2328_0 : fastPhase (bank 4 10).shape 179818 2328 20 1 2 1 0 = 9184907526473460284352801 := mkP 4 10 2328 20 1 2 1 0 370 9184907526473460284352801 [(128,5722005139472209074183648),(128,2820794099204920936836576),(114,642108287796330273332577)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_10_2328_1 : fastPhase (bank 4 10).shape 179818 2328 20 1 2 1 1 = 9128238988058979154907091 := mkP 4 10 2328 20 1 2 1 1 370 9128238988058979154907091 [(128,5697789682325360880662304),(128,2800576179672052521985824),(114,629873126061565752258963)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_10 : Checked (bank 4 10) 20 2 1 := by
  refine checked_from_values (bank 4 10) 20 2 1
    (P3_7_1.checked (bank 4 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_10_2327_0 rec_4_10_2327_1 rec_4_10_2328_0 rec_4_10_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_11_2327_0 : fastPhase (bank 4 11).shape 179818 2327 32 1 2 1 0 = 61231454654892820125080136 := mkP 4 11 2327 32 1 2 1 0 493 61231454654892820125080136 [(128,30570587326656590383881984),(128,19176666039659598650416896),(128,9401408851812262982262528),(109,2082792436764368108518728)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_11_2327_1 : fastPhase (bank 4 11).shape 179818 2327 32 1 2 1 1 = 60947833262188814103091560 := mkP 4 11 2327 32 1 2 1 1 493 60947833262188814103091560 [(128,30478410674498961446398848),(128,19093595626425891211676544),(128,9333778287574230994070400),(109,2042048673689730450945768)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_11_2328_0 : fastPhase (bank 4 11).shape 179818 2328 32 1 2 1 0 = 61231789965036347988458868 := mkP 4 11 2328 32 1 2 1 0 493 61231789965036347988458868 [(128,30570816236463011472937792),(128,19176752964408631313699648),(128,9401428062854413113824064),(109,2082792701310292087997364)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_11_2328_1 : fastPhase (bank 4 11).shape 179818 2328 32 1 2 1 1 = 60948166851100906235643260 := mkP 4 11 2328 32 1 2 1 1 493 60948166851100906235643260 [(128,30478638574134531593535744),(128,19093682029411816870568192),(128,9333797313508037449662720),(109,2042048934046520321876604)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_11 : Checked (bank 4 11) 32 2 1 := by
  refine checked_from_values (bank 4 11) 32 2 1
    (P3_7_1.checked (bank 4 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_11_2327_0 rec_4_11_2327_1 rec_4_11_2328_0 rec_4_11_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_12_2327_0 : fastPhase (bank 4 12).shape 179818 2327 31 1 2 1 0 = 55535744036841389337903003 := mkP 4 12 2327 31 1 2 1 0 493 55535744036841389337903003 [(128,27730709515747393816321632),(128,17391919554183804013211232),(128,8524831699820505427705440),(109,1888283267089686080664699)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_12_2327_1 : fastPhase (bank 4 12).shape 179818 2327 31 1 2 1 1 = 55278446381011620140305521 := mkP 4 12 2327 31 1 2 1 1 493 55278446381011620140305521 [(128,27647054359521775425359520),(128,17316554697561156096876192),(128,8463494755252158438878880),(109,1851342568676530179190929)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_12_2328_0 : fastPhase (bank 4 12).shape 179818 2328 31 1 2 1 0 = 55536048950917256606948934 := mkP 4 12 2328 31 1 2 1 0 493 55536048950917256606948934 [(128,27730917567606028010181376),(128,17391998625740103808545536),(128,8524849227999695811121920),(109,1888283529571428977100102)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_12_2328_1 : fastPhase (bank 4 12).shape 179818 2328 31 1 2 1 1 = 55278749729489897718340718 := mkP 4 12 2328 31 1 2 1 1 493 55278749729489897718340718 [(128,27647261493240507157988160),(128,17316633294625077172732736),(128,8463512114716733332964160),(109,1851342826907580054655662)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_12 : Checked (bank 4 12) 31 2 1 := by
  refine checked_from_values (bank 4 12) 31 2 1
    (P3_7_1.checked (bank 4 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_12_2327_0 rec_4_12_2327_1 rec_4_12_2328_0 rec_4_12_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_13_2327_0 : fastPhase (bank 4 13).shape 179818 2327 44 1 2 1 0 = 317839975461404321523920140 := mkP 4 13 2327 44 1 2 1 0 678 317839975461404321523920140 [(128,121592215205724892915184640),(128,89336542170715495145436160),(128,59686848383510327730549760),(128,33797222160396789000238080),(128,12806899494276439635604480),(38,620248046780377096907020)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_13_2327_1 : fastPhase (bank 4 13).shape 179818 2327 44 1 2 1 1 = 316768110666279890507097320 := mkP 4 13 2327 44 1 2 1 1 678 316768110666279890507097320 [(128,121336202036961106401585920),(128,89095423508050431977368320),(128,59469863714273946784951040),(128,33613493180700839616654080),(128,12665430576425100920974080),(38,587697649868464805563880)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_13_2328_0 : fastPhase (bank 4 13).shape 179818 2328 44 1 2 1 0 = 317841716673639593428425460 := mkP 4 13 2328 44 1 2 1 0 678 317841716673639593428425460 [(128,121593172541546256563698560),(128,89337044053069057770052480),(128,59687064442713817857768320),(128,33797284583320209058208640),(128,12806903483843265285290880),(38,620247569146986893406580)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_13_2328_1 : fastPhase (bank 4 13).shape 179818 2328 44 1 2 1 1 = 316769845369679429421263920 := mkP 4 13 2328 44 1 2 1 1 678 316769845369679429421263920 [(128,121337156385749513939269120),(128,89095923465190065936668160),(128,59470078686872902966638080),(128,33613555135359714959808000),(128,12665434498726166925719040),(38,587697197781064693161520)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_13 : Checked (bank 4 13) 44 2 1 := by
  refine checked_from_values (bank 4 13) 44 2 1
    (P3_7_1.checked (bank 4 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_13_2327_0 rec_4_13_2327_1 rec_4_13_2328_0 rec_4_13_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_14_2327_0 : fastPhase (bank 4 14).shape 179818 2327 76 1 2 1 0 = 4021674317703134039271151905 := mkP 4 14 2327 76 1 2 1 0 925 4021674317703134039271151905 [(128,1167625666320303178513631904),(128,945407919490398009400769184),(128,733571405933071641015528096),(128,536393104667492506562796192),(128,358121455862113606089149088),(128,202976420049179083615107744),(128,75149537339230804267395744),(29,2428808041345209806773953)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_14_2327_1 : fastPhase (bank 4 14).shape 179818 2327 76 1 2 1 1 = 4011742701424830124553413305 := mkP 4 14 2327 76 1 2 1 1 925 4011742701424830124553413305 [(128,1165882336349141083309699488),(128,943724078654514365139902880),(128,731981180243769809926377888),(128,534930394026118550693527968),(128,356819934527466926612230560),(128,201869537104923060132094368),(128,74270517161303434113716640),(29,2264723357592894625863513)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_14_2328_0 : fastPhase (bank 4 14).shape 179818 2328 76 1 2 1 0 = 4021695858784797064551522810 := mkP 4 14 2328 76 1 2 1 0 925 4021695858784797064551522810 [(128,1167635052020672868665328928),(128,945413906505983959741609248),(128,733574907549940027605804320),(128,536394897958350843318310176),(128,358122182565182446498465056),(128,202976587445260523387254048),(128,75149519126973784910013728),(29,2428805612432610424737306)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_14_2328_1 : fastPhase (bank 4 14).shape 179818 2328 76 1 2 1 1 = 4011764183542836661089010785 := mkP 4 14 2328 76 1 2 1 1 925 4011764183542836661089010785 [(128,1165891701024459665241088288),(128,943730050176958904214057248),(128,731984671090252153825640736),(128,534932180465809929275314464),(128,356820657500657627717853472),(128,201869703100078906326036768),(128,74270499090319060353351968),(29,2264721094300414135667841)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_14 : Checked (bank 4 14) 76 2 1 := by
  refine checked_from_values (bank 4 14) 76 2 1
    (P3_7_1.checked (bank 4 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_14_2327_0 rec_4_14_2327_1 rec_4_14_2328_0 rec_4_14_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_15_2327_0 : fastPhase (bank 4 15).shape 179818 2327 105 1 2 1 0 = 23531831465305114989063647250 := mkP 4 15 2327 105 1 2 1 0 1294 23531831465305114989063647250 [(128,5020565823631455286213821888),(128,4348131401378460052156458432),(128,3694189680957559489095468480),(128,3065282369146937561701410240),(128,2467915882115152230467290560),(128,1908561404635642028840822208),(128,1393654949301232640356681152),(128,929597415738643475768763840),(128,522754649822994250182444480),(128,179457502892311560186832320),(14,1720385684726414093653650)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_15_2327_1 : fastPhase (bank 4 15).shape 179818 2327 105 1 2 1 1 = 23490260600699055095028036570 := mkP 4 15 2327 105 1 2 1 1 1294 23490260600699055095028036570 [(128,5015325425456465168370584640),(128,4342999049874020250052619328),(128,3689217543086251845381229632),(128,3060522332319433417454824512),(128,2463419554657623064499047488),(128,1904380116257170096999033920),(128,1389839751561221614831668288),(128,926199082514229084397841472),(128,519823677776454915754708032),(128,177044111938479039747943488),(14,1489955257706597538535770)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_15_2328_0 : fastPhase (bank 4 15).shape 179818 2328 105 1 2 1 0 = 23531957696071550817278855661 := mkP 4 15 2328 105 1 2 1 0 1294 23531957696071550817278855661 [(128,5020607404951128599890034208),(128,4348161974817993955770289696),(128,3694211325740877528674115104),(128,3065296954942189302298078752),(128,2467925070123116002565701152),(128,1908566648676324475690159648),(128,1393657496898665066236993056),(128,929598309203874995186806304),(128,522754727335281737997975072),(128,179457399578506402669350432),(14,1720383803592750299352237)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_15_2328_1 : fastPhase (bank 4 15).shape 179818 2328 105 1 2 1 1 = 23490386584288513657306589001 := mkP 4 15 2328 105 1 2 1 1 1294 23490386584288513657306589001 [(128,5015366941297834927627793824),(128,4343029570174485892260840864),(128,3689239145824985568220222880),(128,3060536885926790275332564384),(128,2463428719103531689047799200),(128,1904385344137720218501875104),(128,1389842289183448384579458464),(128,926199970979094197976638880),(128,519823754060024537263633824),(128,177044009971298526947493280),(14,1489953629299439548268297)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_15 : Checked (bank 4 15) 105 2 1 := by
  refine checked_from_values (bank 4 15) 105 2 1
    (P3_7_1.checked (bank 4 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5842_1293)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_15_2327_0 rec_4_15_2327_1 rec_4_15_2328_0 rec_4_15_2328_1 (by decide +kernel) (by decide +kernel)

private theorem rec_4_16_2327_0 : fastPhase (bank 4 16).shape 179818 2327 138 1 2 1 0 = 120272030724404840716619507385 := mkP 4 16 2327 138 1 2 1 0 1787 120272030724404840716619507385 [(128,18941871311035356505675522080),(128,17123998749215737209705607200),(128,15337377505042699574189129760),(128,13591218351031019936067801120),(128,11894690182528744573506101280),(128,10256920076931696283023536160),(128,8686993352897980956626894880),(128,7193953629562494158942507040),(128,5786802885751427704348500000),(128,4474501519196776234107056160),(128,3265968405750843793496670240),(128,2170080958600750408944406560),(128,1195675187482938665158156320),(123,351978609376374712827618585)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_16_2327_1 : fastPhase (bank 4 16).shape 179818 2327 138 1 2 1 1 = 120118025622203352195594493785 := mkP 4 16 2327 138 1 2 1 1 1787 120118025622203352195594493785 [(128,18927757840943386304874402720),(128,17110071768219443560897668000),(128,15323710441626145069984183200),(128,13577884301988407576074945440),(128,11881761913431828403638506400),(128,10244470022597192034803229600),(128,8675093617854976686489547680),(128,7182675988519860887542219680),(128,5776218784065230055862588320),(128,4464682073337683075540837280),(128,3256984403771538873988248480),(128,2162002860603342999069459360),(128,1188573126086374196234720160),(123,346138479157942470593937465)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_16_2328_0 : fastPhase (bank 4 16).shape 179818 2328 138 1 2 1 0 = 120272679105643586142590127395 := mkP 4 16 2328 138 1 2 1 0 1787 120272679105643586142590127395 [(128,18942031930368870543863357280),(128,17124128148788228145087467360),(128,15337479904364625167757475680),(128,13591297672132206162199490400),(128,11894750051252609933699932000),(128,10256963824227672920568237920),(128,8687024016112132572199567200),(128,7193973953726330727137505120),(128,5786815324868916991136767840),(128,4474508237529552115225907040),(128,3265971279101611373770014560),(128,2170081575594887942533427040),(128,1195674850848296276742430560),(123,351978336727645270668547395)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

private theorem rec_4_16_2328_1 : fastPhase (bank 4 16).shape 179818 2328 138 1 2 1 1 = 120118673083075311236293735475 := mkP 4 16 2328 138 1 2 1 1 1787 120118673083075311236293735475 [(128,18927918279179486591884813280),(128,17110201011423626264342131680),(128,15323812707541389904065692640),(128,13577963510885334862618924000),(128,11881821689402911359921923040),(128,10244513694849165862314161120),(128,8675124221999444460617188320),(128,7182696267862096248197338080),(128,5776231190891176699028431840),(128,4464688770199151045754483680),(128,3256987264769597657752404960),(128,2162003472669911419194708960),(128,1188572790264007107112215520),(123,346138211138011753489318355)] (by decide +kernel) rfl rfl (by dsimp only [blk]; repeat (refine ⟨by decide +kernel, ?_⟩); trivial)

theorem receipt_4_16 : Checked (bank 4 16) 138 2 1 := by
  refine checked_from_values (bank 4 16) 138 2 1
    (P3_7_1.checked (bank 4 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_4_16_2327_0 rec_4_16_2327_1 rec_4_16_2328_0 rec_4_16_2328_1 (by decide +kernel) (by decide +kernel)

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
