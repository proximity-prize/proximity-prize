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


private theorem rec_3_1_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2368 1 1 1 1 0) 0 128 = 493547420248690867784160 := by decide +kernel
private theorem rec_3_1_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2368 1 1 1 1 0) 128 63 = 50392382631287586694896 := by decide +kernel
private theorem rec_3_1_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2368 1 1 1 1 0) 0 191 = 543939802879978454479056 :=
  phaseBlock_append rec_3_1_2368_0_part0 rec_3_1_2368_0_part1 rfl rfl rfl

private theorem rec_3_1_2368_0 : fastPhase (bank 3 1).shape 179798 2368 1 1 1 1 0 = 543939802879978454479056 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_3_1_2368_0_join0

private theorem rec_3_1_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2368 1 1 1 1 1) 0 128 = 488946307843376435288544 := by decide +kernel
private theorem rec_3_1_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2368 1 1 1 1 1) 128 63 = 48747151008703968458736 := by decide +kernel
private theorem rec_3_1_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2368 1 1 1 1 1) 0 191 = 537693458852080403747280 :=
  phaseBlock_append rec_3_1_2368_1_part0 rec_3_1_2368_1_part1 rfl rfl rfl

private theorem rec_3_1_2368_1 : fastPhase (bank 3 1).shape 179798 2368 1 1 1 1 1 = 537693458852080403747280 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_3_1_2368_1_join0

private theorem rec_3_1_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2369 1 1 1 1 0) 0 128 = 493550902237881681824160 := by decide +kernel
private theorem rec_3_1_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2369 1 1 1 1 0) 128 63 = 50392516396566070398672 := by decide +kernel
private theorem rec_3_1_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2369 1 1 1 1 0) 0 191 = 543943418634447752222832 :=
  phaseBlock_append rec_3_1_2369_0_part0 rec_3_1_2369_0_part1 rfl rfl rfl

private theorem rec_3_1_2369_0 : fastPhase (bank 3 1).shape 179798 2369 1 1 1 1 0 = 543943418634447752222832 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_3_1_2369_0_join0

private theorem rec_3_1_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2369 1 1 1 1 1) 0 128 = 488949755070393250226208 := by decide +kernel
private theorem rec_3_1_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2369 1 1 1 1 1) 128 63 = 48747280769718384396816 := by decide +kernel
private theorem rec_3_1_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 1).shape 179798 2369 1 1 1 1 1) 0 191 = 537697035840111634623024 :=
  phaseBlock_append rec_3_1_2369_1_part0 rec_3_1_2369_1_part1 rfl rfl rfl

private theorem rec_3_1_2369_1 : fastPhase (bank 3 1).shape 179798 2369 1 1 1 1 1 = 537697035840111634623024 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_3_1_2369_1_join0

theorem receipt_3_1 : Checked (bank 3 1) 1 1 1 := by
  refine checked_from_values (bank 3 1) 1 1 1
    (P3_7_1.checked (bank 3 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_1_2368_0 rec_3_1_2368_1 rec_3_1_2369_0 rec_3_1_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_2_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2368 2 1 1 1 0) 0 128 = 782266529227802065248480 := by decide +kernel
private theorem rec_3_2_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2368 2 1 1 1 0) 128 63 = 79949394807017827664496 := by decide +kernel
private theorem rec_3_2_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2368 2 1 1 1 0) 0 191 = 862215924034819892912976 :=
  phaseBlock_append rec_3_2_2368_0_part0 rec_3_2_2368_0_part1 rfl rfl rfl

private theorem rec_3_2_2368_0 : fastPhase (bank 3 2).shape 179798 2368 2 1 1 1 0 = 862215924034819892912976 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_3_2_2368_0_join0

private theorem rec_3_2_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2368 2 1 1 1 1) 0 128 = 774980905463180224001760 := by decide +kernel
private theorem rec_3_2_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2368 2 1 1 1 1) 128 63 = 77339703485420786791920 := by decide +kernel
private theorem rec_3_2_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2368 2 1 1 1 1) 0 191 = 852320608948601010793680 :=
  phaseBlock_append rec_3_2_2368_1_part0 rec_3_2_2368_1_part1 rfl rfl rfl

private theorem rec_3_2_2368_1 : fastPhase (bank 3 2).shape 179798 2368 2 1 1 1 1 = 852320608948601010793680 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_3_2_2368_1_join0

private theorem rec_3_2_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2369 2 1 1 1 0) 0 128 = 782272017771510312160800 := by decide +kernel
private theorem rec_3_2_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2369 2 1 1 1 0) 128 63 = 79949604078650078421264 := by decide +kernel
private theorem rec_3_2_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2369 2 1 1 1 0) 0 191 = 862221621850160390582064 :=
  phaseBlock_append rec_3_2_2369_0_part0 rec_3_2_2369_0_part1 rfl rfl rfl

private theorem rec_3_2_2369_0 : fastPhase (bank 3 2).shape 179798 2369 2 1 1 1 0 = 862221621850160390582064 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_3_2_2369_0_join0

private theorem rec_3_2_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2369 2 1 1 1 1) 0 128 = 774986339258879799207072 := by decide +kernel
private theorem rec_3_2_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2369 2 1 1 1 1) 128 63 = 77339906503394234397264 := by decide +kernel
private theorem rec_3_2_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 2).shape 179798 2369 2 1 1 1 1) 0 191 = 852326245762274033604336 :=
  phaseBlock_append rec_3_2_2369_1_part0 rec_3_2_2369_1_part1 rfl rfl rfl

private theorem rec_3_2_2369_1 : fastPhase (bank 3 2).shape 179798 2369 2 1 1 1 1 = 852326245762274033604336 :=
  phase_of_blockG (n := 191) (by decide +kernel) rec_3_2_2369_1_join0

theorem receipt_3_2 : Checked (bank 3 2) 2 1 1 := by
  refine checked_from_values (bank 3 2) 2 1 1
    (P3_7_1.checked (bank 3 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_2_2368_0 rec_3_2_2368_1 rec_3_2_2369_0 rec_3_2_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_3_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2368 3 1 1 1 0) 0 128 = 1889288853922804902615936 := by decide +kernel
private theorem rec_3_3_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2368 3 1 1 1 0) 128 128 = 652408873809496444631936 := by decide +kernel
private theorem rec_3_3_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2368 3 1 1 1 0) 256 22 = 12944981984850265596994 := by decide +kernel
private theorem rec_3_3_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2368 3 1 1 1 0) 128 150 = 665353855794346710228930 :=
  phaseBlock_append rec_3_3_2368_0_part1 rec_3_3_2368_0_part2 rfl rfl rfl
private theorem rec_3_3_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2368 3 1 1 1 0) 0 278 = 2554642709717151612844866 :=
  phaseBlock_append rec_3_3_2368_0_part0 rec_3_3_2368_0_join0 rfl rfl rfl

private theorem rec_3_3_2368_0 : fastPhase (bank 3 3).shape 179798 2368 3 1 1 1 0 = 2554642709717151612844866 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_3_2368_0_join1

private theorem rec_3_3_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2368 3 1 1 1 1) 0 128 = 1878478023577429048901120 := by decide +kernel
private theorem rec_3_3_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2368 3 1 1 1 1) 128 128 = 644133195489567516655104 := by decide +kernel
private theorem rec_3_3_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2368 3 1 1 1 1) 256 22 = 11805929185954008134491 := by decide +kernel
private theorem rec_3_3_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2368 3 1 1 1 1) 128 150 = 655939124675521524789595 :=
  phaseBlock_append rec_3_3_2368_1_part1 rec_3_3_2368_1_part2 rfl rfl rfl
private theorem rec_3_3_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2368 3 1 1 1 1) 0 278 = 2534417148252950573690715 :=
  phaseBlock_append rec_3_3_2368_1_part0 rec_3_3_2368_1_join0 rfl rfl rfl

private theorem rec_3_3_2368_1 : fastPhase (bank 3 3).shape 179798 2368 3 1 1 1 1 = 2534417148252950573690715 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_3_2368_1_join1

private theorem rec_3_3_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2369 3 1 1 1 0) 0 128 = 1889303187511503158865120 := by decide +kernel
private theorem rec_3_3_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2369 3 1 1 1 0) 128 128 = 652411385937477719981280 := by decide +kernel
private theorem rec_3_3_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2369 3 1 1 1 0) 256 22 = 12944997778052771959770 := by decide +kernel
private theorem rec_3_3_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2369 3 1 1 1 0) 128 150 = 665356383715530491941050 :=
  phaseBlock_append rec_3_3_2369_0_part1 rec_3_3_2369_0_part2 rfl rfl rfl
private theorem rec_3_3_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2369 3 1 1 1 0) 0 278 = 2554659571227033650806170 :=
  phaseBlock_append rec_3_3_2369_0_part0 rec_3_3_2369_0_join0 rfl rfl rfl

private theorem rec_3_3_2369_0 : fastPhase (bank 3 3).shape 179798 2369 3 1 1 1 0 = 2554659571227033650806170 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_3_2369_0_join1

private theorem rec_3_3_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2369 3 1 1 1 1) 0 128 = 1878492265352029717967520 := by decide +kernel
private theorem rec_3_3_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2369 3 1 1 1 1) 128 128 = 644135676201944980488864 := by decide +kernel
private theorem rec_3_3_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2369 3 1 1 1 1) 256 22 = 11805943657925233925031 := by decide +kernel
private theorem rec_3_3_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2369 3 1 1 1 1) 128 150 = 655941619859870214413895 :=
  phaseBlock_append rec_3_3_2369_1_part1 rec_3_3_2369_1_part2 rfl rfl rfl
private theorem rec_3_3_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 3).shape 179798 2369 3 1 1 1 1) 0 278 = 2534433885211899932381415 :=
  phaseBlock_append rec_3_3_2369_1_part0 rec_3_3_2369_1_join0 rfl rfl rfl

private theorem rec_3_3_2369_1 : fastPhase (bank 3 3).shape 179798 2369 3 1 1 1 1 = 2534433885211899932381415 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_3_2369_1_join1

theorem receipt_3_3 : Checked (bank 3 3) 3 1 1 := by
  refine checked_from_values (bank 3 3) 3 1 1
    (P3_7_1.checked (bank 3 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_3_2368_0 rec_3_3_2368_1 rec_3_3_2369_0 rec_3_3_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_4_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2368 4 1 1 1 0) 0 128 = 2335646248930802519028288 := by decide +kernel
private theorem rec_3_4_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2368 4 1 1 1 0) 128 128 = 807000941484007966380608 := by decide +kernel
private theorem rec_3_4_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2368 4 1 1 1 0) 256 22 = 16019191010935186941757 := by decide +kernel
private theorem rec_3_4_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2368 4 1 1 1 0) 128 150 = 823020132494943153322365 :=
  phaseBlock_append rec_3_4_2368_0_part1 rec_3_4_2368_0_part2 rfl rfl rfl
private theorem rec_3_4_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2368 4 1 1 1 0) 0 278 = 3158666381425745672350653 :=
  phaseBlock_append rec_3_4_2368_0_part0 rec_3_4_2368_0_join0 rfl rfl rfl

private theorem rec_3_4_2368_0 : fastPhase (bank 3 4).shape 179798 2368 4 1 1 1 0 = 3158666381425745672350653 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_4_2368_0_join1

private theorem rec_3_4_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2368 4 1 1 1 1) 0 128 = 2322291991560347809102400 := by decide +kernel
private theorem rec_3_4_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2368 4 1 1 1 1) 128 128 = 796767425240746653973056 := by decide +kernel
private theorem rec_3_4_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2368 4 1 1 1 1) 256 22 = 14609680018257781685074 := by decide +kernel
private theorem rec_3_4_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2368 4 1 1 1 1) 128 150 = 811377105259004435658130 :=
  phaseBlock_append rec_3_4_2368_1_part1 rec_3_4_2368_1_part2 rfl rfl rfl
private theorem rec_3_4_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2368 4 1 1 1 1) 0 278 = 3133669096819352244760530 :=
  phaseBlock_append rec_3_4_2368_1_part0 rec_3_4_2368_1_join0 rfl rfl rfl

private theorem rec_3_4_2368_1 : fastPhase (bank 3 4).shape 179798 2368 4 1 1 1 1 = 3133669096819352244760530 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_4_2368_1_join1

private theorem rec_3_4_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2369 4 1 1 1 0) 0 128 = 2335663906594742436702816 := by decide +kernel
private theorem rec_3_4_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2369 4 1 1 1 0) 128 128 = 807004028039251869350496 := by decide +kernel
private theorem rec_3_4_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2369 4 1 1 1 0) 256 22 = 16019210153359335161184 := by decide +kernel
private theorem rec_3_4_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2369 4 1 1 1 0) 128 150 = 823023238192611204511680 :=
  phaseBlock_append rec_3_4_2369_0_part1 rec_3_4_2369_0_part2 rfl rfl rfl
private theorem rec_3_4_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2369 4 1 1 1 0) 0 278 = 3158687144787353641214496 :=
  phaseBlock_append rec_3_4_2369_0_part0 rec_3_4_2369_0_join0 rfl rfl rfl

private theorem rec_3_4_2369_0 : fastPhase (bank 3 4).shape 179798 2369 4 1 1 1 0 = 3158687144787353641214496 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_4_2369_0_join1

private theorem rec_3_4_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2369 4 1 1 1 1) 0 128 = 2322309536180016920028000 := by decide +kernel
private theorem rec_3_4_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2369 4 1 1 1 1) 128 128 = 796770473220279666856800 := by decide +kernel
private theorem rec_3_4_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2369 4 1 1 1 1) 256 22 = 14609697561172425390525 := by decide +kernel
private theorem rec_3_4_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2369 4 1 1 1 1) 128 150 = 811380170781452092247325 :=
  phaseBlock_append rec_3_4_2369_1_part1 rec_3_4_2369_1_part2 rfl rfl rfl
private theorem rec_3_4_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 4).shape 179798 2369 4 1 1 1 1) 0 278 = 3133689706961469012275325 :=
  phaseBlock_append rec_3_4_2369_1_part0 rec_3_4_2369_1_join0 rfl rfl rfl

private theorem rec_3_4_2369_1 : fastPhase (bank 3 4).shape 179798 2369 4 1 1 1 1 = 3133689706961469012275325 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_4_2369_1_join1

theorem receipt_3_4 : Checked (bank 3 4) 4 1 1 := by
  refine checked_from_values (bank 3 4) 4 1 1
    (P3_7_1.checked (bank 3 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_4_2368_0 rec_3_4_2368_1 rec_3_4_2369_0 rec_3_4_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_5_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2368 5 1 1 1 0) 0 128 = 2960900266534771038824032 := by decide +kernel
private theorem rec_3_5_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2368 5 1 1 1 0) 128 128 = 1023613671208640974247520 := by decide +kernel
private theorem rec_3_5_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2368 5 1 1 1 0) 256 22 = 20327658311173153905965 := by decide +kernel
private theorem rec_3_5_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2368 5 1 1 1 0) 128 150 = 1043941329519814128153485 :=
  phaseBlock_append rec_3_5_2368_0_part1 rec_3_5_2368_0_part2 rfl rfl rfl
private theorem rec_3_5_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2368 5 1 1 1 0) 0 278 = 4004841596054585166977517 :=
  phaseBlock_append rec_3_5_2368_0_part0 rec_3_5_2368_0_join0 rfl rfl rfl

private theorem rec_3_5_2368_0 : fastPhase (bank 3 5).shape 179798 2368 5 1 1 1 0 = 4004841596054585166977517 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_5_2368_0_join1

private theorem rec_3_5_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2368 5 1 1 1 1) 0 128 = 2943984632472844396247456 := by decide +kernel
private theorem rec_3_5_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2368 5 1 1 1 1) 128 128 = 1010637274882014981392800 := by decide +kernel
private theorem rec_3_5_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2368 5 1 1 1 1) 256 22 = 18539109732724564858875 := by decide +kernel
private theorem rec_3_5_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2368 5 1 1 1 1) 128 150 = 1029176384614739546251675 :=
  phaseBlock_append rec_3_5_2368_1_part1 rec_3_5_2368_1_part2 rfl rfl rfl
private theorem rec_3_5_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2368 5 1 1 1 1) 0 278 = 3973161017087583942499131 :=
  phaseBlock_append rec_3_5_2368_1_part0 rec_3_5_2368_1_join0 rfl rfl rfl

private theorem rec_3_5_2368_1 : fastPhase (bank 3 5).shape 179798 2368 5 1 1 1 1 = 3973161017087583942499131 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_5_2368_1_join1

private theorem rec_3_5_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2369 5 1 1 1 0) 0 128 = 2960922572137688642221184 := by decide +kernel
private theorem rec_3_5_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2369 5 1 1 1 0) 128 128 = 1023617559815829743654016 := by decide +kernel
private theorem rec_3_5_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2369 5 1 1 1 0) 256 22 = 20327682092671294722304 := by decide +kernel
private theorem rec_3_5_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2369 5 1 1 1 0) 128 150 = 1043945241908501038376320 :=
  phaseBlock_append rec_3_5_2369_0_part1 rec_3_5_2369_0_part2 rfl rfl rfl
private theorem rec_3_5_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2369 5 1 1 1 0) 0 278 = 4004867814046189680597504 :=
  phaseBlock_append rec_3_5_2369_0_part0 rec_3_5_2369_0_join0 rfl rfl rfl

private theorem rec_3_5_2369_0 : fastPhase (bank 3 5).shape 179798 2369 5 1 1 1 0 = 4004867814046189680597504 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_5_2369_0_join1

private theorem rec_3_5_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2369 5 1 1 1 1) 0 128 = 2944006795353859474416640 := by decide +kernel
private theorem rec_3_5_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2369 5 1 1 1 1) 128 128 = 1010641114919172644389888 := by decide +kernel
private theorem rec_3_5_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2369 5 1 1 1 1) 256 22 = 18539131529553749258452 := by decide +kernel
private theorem rec_3_5_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2369 5 1 1 1 1) 128 150 = 1029180246448726393648340 :=
  phaseBlock_append rec_3_5_2369_1_part1 rec_3_5_2369_1_part2 rfl rfl rfl
private theorem rec_3_5_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 5).shape 179798 2369 5 1 1 1 1) 0 278 = 3973187041802585868064980 :=
  phaseBlock_append rec_3_5_2369_1_part0 rec_3_5_2369_1_join0 rfl rfl rfl

private theorem rec_3_5_2369_1 : fastPhase (bank 3 5).shape 179798 2369 5 1 1 1 1 = 3973187041802585868064980 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_5_2369_1_join1

theorem receipt_3_5 : Checked (bank 3 5) 5 1 1 := by
  refine checked_from_values (bank 3 5) 5 1 1
    (P3_7_1.checked (bank 3 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_5_2368_0 rec_3_5_2368_1 rec_3_5_2369_0 rec_3_5_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_6_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2368 7 1 1 1 0) 0 128 = 5288961471018912259958208 := by decide +kernel
private theorem rec_3_6_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2368 7 1 1 1 0) 128 128 = 1830513674062897302824384 := by decide +kernel
private theorem rec_3_6_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2368 7 1 1 1 0) 256 22 = 36382552028358789224356 := by decide +kernel
private theorem rec_3_6_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2368 7 1 1 1 0) 128 150 = 1866896226091256092048740 :=
  phaseBlock_append rec_3_6_2368_0_part1 rec_3_6_2368_0_part2 rfl rfl rfl
private theorem rec_3_6_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2368 7 1 1 1 0) 0 278 = 7155857697110168352006948 :=
  phaseBlock_append rec_3_6_2368_0_part0 rec_3_6_2368_0_join0 rfl rfl rfl

private theorem rec_3_6_2368_0 : fastPhase (bank 3 6).shape 179798 2368 7 1 1 1 0 = 7155857697110168352006948 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_6_2368_0_join1

private theorem rec_3_6_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2368 7 1 1 1 1) 0 128 = 5258794066323795777787584 := by decide +kernel
private theorem rec_3_6_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2368 7 1 1 1 1) 128 128 = 1807322349194800056907456 := by decide +kernel
private theorem rec_3_6_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2368 7 1 1 1 1) 256 22 = 33181611534324782997699 := by decide +kernel
private theorem rec_3_6_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2368 7 1 1 1 1) 128 150 = 1840503960729124839905155 :=
  phaseBlock_append rec_3_6_2368_1_part1 rec_3_6_2368_1_part2 rfl rfl rfl
private theorem rec_3_6_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2368 7 1 1 1 1) 0 278 = 7099298027052920617692739 :=
  phaseBlock_append rec_3_6_2368_1_part0 rec_3_6_2368_1_join0 rfl rfl rfl

private theorem rec_3_6_2368_1 : fastPhase (bank 3 6).shape 179798 2368 7 1 1 1 1 = 7099298027052920617692739 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_6_2368_1_join1

private theorem rec_3_6_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2369 7 1 1 1 0) 0 128 = 5289001032418111302470048 := by decide +kernel
private theorem rec_3_6_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2369 7 1 1 1 0) 128 128 = 1830520533452000408598944 := by decide +kernel
private theorem rec_3_6_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2369 7 1 1 1 0) 256 22 = 36382592768806537730246 := by decide +kernel
private theorem rec_3_6_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2369 7 1 1 1 0) 128 150 = 1866903126220806946329190 :=
  phaseBlock_append rec_3_6_2369_0_part1 rec_3_6_2369_0_part2 rfl rfl rfl
private theorem rec_3_6_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2369 7 1 1 1 0) 0 278 = 7155904158638918248799238 :=
  phaseBlock_append rec_3_6_2369_0_part0 rec_3_6_2369_0_join0 rfl rfl rfl

private theorem rec_3_6_2369_0 : fastPhase (bank 3 6).shape 179798 2369 7 1 1 1 0 = 7155904158638918248799238 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_6_2369_0_join1

private theorem rec_3_6_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2369 7 1 1 1 1) 0 128 = 5258833374867539739385824 := by decide +kernel
private theorem rec_3_6_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2369 7 1 1 1 1) 128 128 = 1807329123013624393453536 := by decide +kernel
private theorem rec_3_6_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2369 7 1 1 1 1) 256 22 = 33181648883836378736349 := by decide +kernel
private theorem rec_3_6_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2369 7 1 1 1 1) 128 150 = 1840510771897460772189885 :=
  phaseBlock_append rec_3_6_2369_1_part1 rec_3_6_2369_1_part2 rfl rfl rfl
private theorem rec_3_6_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 6).shape 179798 2369 7 1 1 1 1) 0 278 = 7099344146765000511575709 :=
  phaseBlock_append rec_3_6_2369_1_part0 rec_3_6_2369_1_join0 rfl rfl rfl

private theorem rec_3_6_2369_1 : fastPhase (bank 3 6).shape 179798 2369 7 1 1 1 1 = 7099344146765000511575709 :=
  phase_of_blockG (n := 278) (by decide +kernel) rec_3_6_2369_1_join1

theorem receipt_3_6 : Checked (bank 3 6) 7 1 1 := by
  refine checked_from_values (bank 3 6) 7 1 1
    (P3_7_1.checked (bank 3 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_6_2368_0 rec_3_6_2368_1 rec_3_6_2369_0 rec_3_6_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_7_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2368 10 1 1 1 0) 0 128 = 13107391894154136733750752 := by decide +kernel
private theorem rec_3_7_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2368 10 1 1 1 0) 128 128 = 6801320710255539770140128 := by decide +kernel
private theorem rec_3_7_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2368 10 1 1 1 0) 256 114 = 1728257733472475564550165 := by decide +kernel
private theorem rec_3_7_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2368 10 1 1 1 0) 128 242 = 8529578443728015334690293 :=
  phaseBlock_append rec_3_7_2368_0_part1 rec_3_7_2368_0_part2 rfl rfl rfl
private theorem rec_3_7_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2368 10 1 1 1 0) 0 370 = 21636970337882152068441045 :=
  phaseBlock_append rec_3_7_2368_0_part0 rec_3_7_2368_0_join0 rfl rfl rfl

private theorem rec_3_7_2368_0 : fastPhase (bank 3 7).shape 179798 2368 10 1 1 1 0 = 21636970337882152068441045 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_3_7_2368_0_join1

private theorem rec_3_7_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2368 10 1 1 1 1) 0 128 = 13054385381628633040373088 := by decide +kernel
private theorem rec_3_7_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2368 10 1 1 1 1) 128 128 = 6756974154224506276935008 := by decide +kernel
private theorem rec_3_7_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2368 10 1 1 1 1) 256 114 = 1696915325958635122182166 := by decide +kernel
private theorem rec_3_7_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2368 10 1 1 1 1) 128 242 = 8453889480183141399117174 :=
  phaseBlock_append rec_3_7_2368_1_part1 rec_3_7_2368_1_part2 rfl rfl rfl
private theorem rec_3_7_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2368 10 1 1 1 1) 0 370 = 21508274861811774439490262 :=
  phaseBlock_append rec_3_7_2368_1_part0 rec_3_7_2368_1_join0 rfl rfl rfl

private theorem rec_3_7_2368_1 : fastPhase (bank 3 7).shape 179798 2368 10 1 1 1 1 = 21508274861811774439490262 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_3_7_2368_1_join1

private theorem rec_3_7_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2369 10 1 1 1 0) 0 128 = 13107495045731765705236704 := by decide +kernel
private theorem rec_3_7_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2369 10 1 1 1 0) 128 128 = 6801353887069803195461856 := by decide +kernel
private theorem rec_3_7_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2369 10 1 1 1 0) 256 114 = 1728261837335609704093965 := by decide +kernel
private theorem rec_3_7_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2369 10 1 1 1 0) 128 242 = 8529615724405412899555821 :=
  phaseBlock_append rec_3_7_2369_0_part1 rec_3_7_2369_0_part2 rfl rfl rfl
private theorem rec_3_7_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2369 10 1 1 1 0) 0 370 = 21637110770137178604792525 :=
  phaseBlock_append rec_3_7_2369_0_part0 rec_3_7_2369_0_join0 rfl rfl rfl

private theorem rec_3_7_2369_0 : fastPhase (bank 3 7).shape 179798 2369 10 1 1 1 0 = 21637110770137178604792525 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_3_7_2369_0_join1

private theorem rec_3_7_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2369 10 1 1 1 1) 0 128 = 13054488058587758337180192 := by decide +kernel
private theorem rec_3_7_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2369 10 1 1 1 1) 128 128 = 6757007095829071261553184 := by decide +kernel
private theorem rec_3_7_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2369 10 1 1 1 1) 256 114 = 1696919362058470153056180 := by decide +kernel
private theorem rec_3_7_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2369 10 1 1 1 1) 128 242 = 8453926457887541414609364 :=
  phaseBlock_append rec_3_7_2369_1_part1 rec_3_7_2369_1_part2 rfl rfl rfl
private theorem rec_3_7_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 7).shape 179798 2369 10 1 1 1 1) 0 370 = 21508414516475299751789556 :=
  phaseBlock_append rec_3_7_2369_1_part0 rec_3_7_2369_1_join0 rfl rfl rfl

private theorem rec_3_7_2369_1 : fastPhase (bank 3 7).shape 179798 2369 10 1 1 1 1 = 21508414516475299751789556 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_3_7_2369_1_join1

theorem receipt_3_7 : Checked (bank 3 7) 10 1 1 := by
  refine checked_from_values (bank 3 7) 10 1 1
    (P3_7_1.checked (bank 3 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_7_2368_0 rec_3_7_2368_1 rec_3_7_2369_0 rec_3_7_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_8_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 0) 0 128 = 52624263232566523621147136 := by decide +kernel
private theorem rec_3_8_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 0) 128 128 = 33951755214677094981444096 := by decide +kernel
private theorem rec_3_8_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 0) 256 128 = 17758090274249164194726400 := by decide +kernel
private theorem rec_3_8_2368_0_part3 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 0) 384 109 = 4357901837491321571143362 := by decide +kernel
private theorem rec_3_8_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 0) 0 256 = 86576018447243618602591232 :=
  phaseBlock_append rec_3_8_2368_0_part0 rec_3_8_2368_0_part1 rfl rfl rfl
private theorem rec_3_8_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 0) 256 237 = 22115992111740485765869762 :=
  phaseBlock_append rec_3_8_2368_0_part2 rec_3_8_2368_0_part3 rfl rfl rfl
private theorem rec_3_8_2368_0_join2 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 0) 0 493 = 108692010558984104368460994 :=
  phaseBlock_append rec_3_8_2368_0_join0 rec_3_8_2368_0_join1 rfl rfl rfl

private theorem rec_3_8_2368_0 : fastPhase (bank 3 8).shape 179798 2368 16 1 1 1 0 = 108692010558984104368460994 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_3_8_2368_0_join2

private theorem rec_3_8_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 1) 0 128 = 52471197924822521101819328 := by decide +kernel
private theorem rec_3_8_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 1) 128 128 = 33816567279685150792990144 := by decide +kernel
private theorem rec_3_8_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 1) 256 128 = 17642474475276703883943360 := by decide +kernel
private theorem rec_3_8_2368_1_part3 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 1) 384 109 = 4276132644851588842225398 := by decide +kernel
private theorem rec_3_8_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 1) 0 256 = 86287765204507671894809472 :=
  phaseBlock_append rec_3_8_2368_1_part0 rec_3_8_2368_1_part1 rfl rfl rfl
private theorem rec_3_8_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 1) 256 237 = 21918607120128292726168758 :=
  phaseBlock_append rec_3_8_2368_1_part2 rec_3_8_2368_1_part3 rfl rfl rfl
private theorem rec_3_8_2368_1_join2 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2368 16 1 1 1 1) 0 493 = 108206372324635964620978230 :=
  phaseBlock_append rec_3_8_2368_1_join0 rec_3_8_2368_1_join1 rfl rfl rfl

private theorem rec_3_8_2368_1 : fastPhase (bank 3 8).shape 179798 2368 16 1 1 1 1 = 108206372324635964620978230 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_3_8_2368_1_join2

private theorem rec_3_8_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 0) 0 128 = 52624692323659451957695776 := by decide +kernel
private theorem rec_3_8_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 0) 128 128 = 33951953682137793688446240 := by decide +kernel
private theorem rec_3_8_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 0) 256 128 = 17758155543029185893332256 := by decide +kernel
private theorem rec_3_8_2369_0_part3 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 0) 384 109 = 4357909924416906034751937 := by decide +kernel
private theorem rec_3_8_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 0) 0 256 = 86576646005797245646142016 :=
  phaseBlock_append rec_3_8_2369_0_part0 rec_3_8_2369_0_part1 rfl rfl rfl
private theorem rec_3_8_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 0) 256 237 = 22116065467446091928084193 :=
  phaseBlock_append rec_3_8_2369_0_part2 rec_3_8_2369_0_part3 rfl rfl rfl
private theorem rec_3_8_2369_0_join2 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 0) 0 493 = 108692711473243337574226209 :=
  phaseBlock_append rec_3_8_2369_0_join0 rec_3_8_2369_0_join1 rfl rfl rfl

private theorem rec_3_8_2369_0 : fastPhase (bank 3 8).shape 179798 2369 16 1 1 1 0 = 108692711473243337574226209 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_3_8_2369_0_join2

private theorem rec_3_8_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 1) 0 128 = 52471625583312099495171360 := by decide +kernel
private theorem rec_3_8_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 1) 128 128 = 33816764861704601690342688 := by decide +kernel
private theorem rec_3_8_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 1) 256 128 = 17642539287352732367729952 := by decide +kernel
private theorem rec_3_8_2369_1_part3 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 1) 384 109 = 4276140593187634151202945 := by decide +kernel
private theorem rec_3_8_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 1) 0 256 = 86288390445016701185514048 :=
  phaseBlock_append rec_3_8_2369_1_part0 rec_3_8_2369_1_part1 rfl rfl rfl
private theorem rec_3_8_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 1) 256 237 = 21918679880540366518932897 :=
  phaseBlock_append rec_3_8_2369_1_part2 rec_3_8_2369_1_part3 rfl rfl rfl
private theorem rec_3_8_2369_1_join2 :
    phaseBlock (fastLayerG (bank 3 8).shape 179798 2369 16 1 1 1 1) 0 493 = 108207070325557067704446945 :=
  phaseBlock_append rec_3_8_2369_1_join0 rec_3_8_2369_1_join1 rfl rfl rfl

private theorem rec_3_8_2369_1 : fastPhase (bank 3 8).shape 179798 2369 16 1 1 1 1 = 108207070325557067704446945 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_3_8_2369_1_join2

theorem receipt_3_8 : Checked (bank 3 8) 16 1 1 := by
  refine checked_from_values (bank 3 8) 16 1 1
    (P3_7_1.checked (bank 3 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_8_2368_0 rec_3_8_2368_1 rec_3_8_2369_0 rec_3_8_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_9_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2368 10 1 1 1 0) 0 128 = 13107391894154136733750752 := by decide +kernel
private theorem rec_3_9_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2368 10 1 1 1 0) 128 128 = 6801320710255539770140128 := by decide +kernel
private theorem rec_3_9_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2368 10 1 1 1 0) 256 114 = 1728257733472475564550165 := by decide +kernel
private theorem rec_3_9_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2368 10 1 1 1 0) 128 242 = 8529578443728015334690293 :=
  phaseBlock_append rec_3_9_2368_0_part1 rec_3_9_2368_0_part2 rfl rfl rfl
private theorem rec_3_9_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2368 10 1 1 1 0) 0 370 = 21636970337882152068441045 :=
  phaseBlock_append rec_3_9_2368_0_part0 rec_3_9_2368_0_join0 rfl rfl rfl

private theorem rec_3_9_2368_0 : fastPhase (bank 3 9).shape 179798 2368 10 1 1 1 0 = 21636970337882152068441045 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_3_9_2368_0_join1

private theorem rec_3_9_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2368 10 1 1 1 1) 0 128 = 13054385381628633040373088 := by decide +kernel
private theorem rec_3_9_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2368 10 1 1 1 1) 128 128 = 6756974154224506276935008 := by decide +kernel
private theorem rec_3_9_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2368 10 1 1 1 1) 256 114 = 1696915325958635122182166 := by decide +kernel
private theorem rec_3_9_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2368 10 1 1 1 1) 128 242 = 8453889480183141399117174 :=
  phaseBlock_append rec_3_9_2368_1_part1 rec_3_9_2368_1_part2 rfl rfl rfl
private theorem rec_3_9_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2368 10 1 1 1 1) 0 370 = 21508274861811774439490262 :=
  phaseBlock_append rec_3_9_2368_1_part0 rec_3_9_2368_1_join0 rfl rfl rfl

private theorem rec_3_9_2368_1 : fastPhase (bank 3 9).shape 179798 2368 10 1 1 1 1 = 21508274861811774439490262 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_3_9_2368_1_join1

private theorem rec_3_9_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2369 10 1 1 1 0) 0 128 = 13107495045731765705236704 := by decide +kernel
private theorem rec_3_9_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2369 10 1 1 1 0) 128 128 = 6801353887069803195461856 := by decide +kernel
private theorem rec_3_9_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2369 10 1 1 1 0) 256 114 = 1728261837335609704093965 := by decide +kernel
private theorem rec_3_9_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2369 10 1 1 1 0) 128 242 = 8529615724405412899555821 :=
  phaseBlock_append rec_3_9_2369_0_part1 rec_3_9_2369_0_part2 rfl rfl rfl
private theorem rec_3_9_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2369 10 1 1 1 0) 0 370 = 21637110770137178604792525 :=
  phaseBlock_append rec_3_9_2369_0_part0 rec_3_9_2369_0_join0 rfl rfl rfl

private theorem rec_3_9_2369_0 : fastPhase (bank 3 9).shape 179798 2369 10 1 1 1 0 = 21637110770137178604792525 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_3_9_2369_0_join1

private theorem rec_3_9_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2369 10 1 1 1 1) 0 128 = 13054488058587758337180192 := by decide +kernel
private theorem rec_3_9_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2369 10 1 1 1 1) 128 128 = 6757007095829071261553184 := by decide +kernel
private theorem rec_3_9_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2369 10 1 1 1 1) 256 114 = 1696919362058470153056180 := by decide +kernel
private theorem rec_3_9_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2369 10 1 1 1 1) 128 242 = 8453926457887541414609364 :=
  phaseBlock_append rec_3_9_2369_1_part1 rec_3_9_2369_1_part2 rfl rfl rfl
private theorem rec_3_9_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 9).shape 179798 2369 10 1 1 1 1) 0 370 = 21508414516475299751789556 :=
  phaseBlock_append rec_3_9_2369_1_part0 rec_3_9_2369_1_join0 rfl rfl rfl

private theorem rec_3_9_2369_1 : fastPhase (bank 3 9).shape 179798 2369 10 1 1 1 1 = 21508414516475299751789556 :=
  phase_of_blockG (n := 370) (by decide +kernel) rec_3_9_2369_1_join1

theorem receipt_3_9 : Checked (bank 3 9) 10 1 1 := by
  refine checked_from_values (bank 3 9) 10 1 1
    (P3_7_1.checked (bank 3 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_9_2368_0 rec_3_9_2368_1 rec_3_9_2369_0 rec_3_9_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_10_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 0) 0 128 = 96990883567251621938786816 := by decide +kernel
private theorem rec_3_10_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 0) 128 128 = 62623593728594512538964480 := by decide +kernel
private theorem rec_3_10_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 0) 256 128 = 32779206528122697139171840 := by decide +kernel
private theorem rec_3_10_2368_0_part3 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 0) 384 109 = 8049435445782936289037250 := by decide +kernel
private theorem rec_3_10_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 0) 0 256 = 159614477295846134477751296 :=
  phaseBlock_append rec_3_10_2368_0_part0 rec_3_10_2368_0_part1 rfl rfl rfl
private theorem rec_3_10_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 0) 256 237 = 40828641973905633428209090 :=
  phaseBlock_append rec_3_10_2368_0_part2 rec_3_10_2368_0_part3 rfl rfl rfl
private theorem rec_3_10_2368_0_join2 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 0) 0 493 = 200443119269751767905960386 :=
  phaseBlock_append rec_3_10_2368_0_join0 rec_3_10_2368_0_join1 rfl rfl rfl

private theorem rec_3_10_2368_0 : fastPhase (bank 3 10).shape 179798 2368 20 1 1 1 0 = 200443119269751767905960386 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_3_10_2368_0_join2

private theorem rec_3_10_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 1) 0 128 = 96709348805380922617941440 := by decide +kernel
private theorem rec_3_10_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 1) 128 128 = 62374611524864301999222208 := by decide +kernel
private theorem rec_3_10_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 1) 256 128 = 32565982082215228029799872 := by decide +kernel
private theorem rec_3_10_2368_1_part3 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 1) 384 109 = 7898432846655707619232374 := by decide +kernel
private theorem rec_3_10_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 1) 0 256 = 159083960330245224617163648 :=
  phaseBlock_append rec_3_10_2368_1_part0 rec_3_10_2368_1_part1 rfl rfl rfl
private theorem rec_3_10_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 1) 256 237 = 40464414928870935649032246 :=
  phaseBlock_append rec_3_10_2368_1_part2 rec_3_10_2368_1_part3 rfl rfl rfl
private theorem rec_3_10_2368_1_join2 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2368 20 1 1 1 1) 0 493 = 199548375259116160266195894 :=
  phaseBlock_append rec_3_10_2368_1_join0 rec_3_10_2368_1_join1 rfl rfl rfl

private theorem rec_3_10_2368_1 : fastPhase (bank 3 10).shape 179798 2368 20 1 1 1 1 = 199548375259116160266195894 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_3_10_2368_1_join2

private theorem rec_3_10_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 0) 0 128 = 96991668582367794556557600 := by decide +kernel
private theorem rec_3_10_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 0) 128 128 = 62623956102543753354160416 := by decide +kernel
private theorem rec_3_10_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 0) 256 128 = 32779325107165211638659360 := by decide +kernel
private theorem rec_3_10_2369_0_part3 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 0) 384 109 = 8049449924912490557875137 := by decide +kernel
private theorem rec_3_10_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 0) 0 256 = 159615624684911547910718016 :=
  phaseBlock_append rec_3_10_2369_0_part0 rec_3_10_2369_0_part1 rfl rfl rfl
private theorem rec_3_10_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 0) 256 237 = 40828775032077702196534497 :=
  phaseBlock_append rec_3_10_2369_0_part2 rec_3_10_2369_0_part3 rfl rfl rfl
private theorem rec_3_10_2369_0_join2 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 0) 0 493 = 200444399716989250107252513 :=
  phaseBlock_append rec_3_10_2369_0_join0 rec_3_10_2369_0_join1 rfl rfl rfl

private theorem rec_3_10_2369_0 : fastPhase (bank 3 10).shape 179798 2369 20 1 1 1 0 = 200444399716989250107252513 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_3_10_2369_0_join2

private theorem rec_3_10_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 1) 0 128 = 96710131203017192897329440 := by decide +kernel
private theorem rec_3_10_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 1) 128 128 = 62374972283292834089920800 := by decide +kernel
private theorem rec_3_10_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 1) 256 128 = 32566099831685839643646240 := by decide +kernel
private theorem rec_3_10_2369_1_part3 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 1) 384 109 = 7898447078538972027847425 := by decide +kernel
private theorem rec_3_10_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 1) 0 256 = 159085103486310026987250240 :=
  phaseBlock_append rec_3_10_2369_1_part0 rec_3_10_2369_1_part1 rfl rfl rfl
private theorem rec_3_10_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 1) 256 237 = 40464546910224811671493665 :=
  phaseBlock_append rec_3_10_2369_1_part2 rec_3_10_2369_1_part3 rfl rfl rfl
private theorem rec_3_10_2369_1_join2 :
    phaseBlock (fastLayerG (bank 3 10).shape 179798 2369 20 1 1 1 1) 0 493 = 199549650396534838658743905 :=
  phaseBlock_append rec_3_10_2369_1_join0 rec_3_10_2369_1_join1 rfl rfl rfl

private theorem rec_3_10_2369_1 : fastPhase (bank 3 10).shape 179798 2369 20 1 1 1 1 = 199549650396534838658743905 :=
  phase_of_blockG (n := 493) (by decide +kernel) rec_3_10_2369_1_join2

theorem receipt_3_10 : Checked (bank 3 10) 20 1 1 := by
  refine checked_from_values (bank 3 10) 20 1 1
    (P3_7_1.checked (bank 3 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2225_492)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_10_2368_0 rec_3_10_2368_1 rec_3_10_2369_0 rec_3_10_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_11_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 0 128 = 550475132044352661531694240 := by decide +kernel
private theorem rec_3_11_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 128 128 = 410862632294968596046890144 := by decide +kernel
private theorem rec_3_11_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 256 128 = 283705905938722494335808672 := by decide +kernel
private theorem rec_3_11_2368_0_part3 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 384 128 = 169803174668952187160667296 := by decide +kernel
private theorem rec_3_11_2368_0_part4 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 512 128 = 69947665895544222671656096 := by decide +kernel
private theorem rec_3_11_2368_0_part5 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 640 38 = 3709251741147533965952802 := by decide +kernel
private theorem rec_3_11_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 128 256 = 694568538233691090382698816 :=
  phaseBlock_append rec_3_11_2368_0_part1 rec_3_11_2368_0_part2 rfl rfl rfl
private theorem rec_3_11_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 0 384 = 1245043670278043751914393056 :=
  phaseBlock_append rec_3_11_2368_0_part0 rec_3_11_2368_0_join0 rfl rfl rfl
private theorem rec_3_11_2368_0_join2 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 512 166 = 73656917636691756637608898 :=
  phaseBlock_append rec_3_11_2368_0_part4 rec_3_11_2368_0_part5 rfl rfl rfl
private theorem rec_3_11_2368_0_join3 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 384 294 = 243460092305643943798276194 :=
  phaseBlock_append rec_3_11_2368_0_part3 rec_3_11_2368_0_join2 rfl rfl rfl
private theorem rec_3_11_2368_0_join4 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 0) 0 678 = 1488503762583687695712669250 :=
  phaseBlock_append rec_3_11_2368_0_join1 rec_3_11_2368_0_join3 rfl rfl rfl

private theorem rec_3_11_2368_0 : fastPhase (bank 3 11).shape 179798 2368 32 1 1 1 0 = 1488503762583687695712669250 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_3_11_2368_0_join4

private theorem rec_3_11_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 0 128 = 549352718916299723367765024 := by decide +kernel
private theorem rec_3_11_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 128 128 = 409830542655250637949371424 := by decide +kernel
private theorem rec_3_11_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 256 128 = 282770847928162841022182432 := by decide +kernel
private theorem rec_3_11_2368_1_part3 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 384 128 = 168971815392936605336888352 := by decide +kernel
private theorem rec_3_11_2368_1_part4 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 512 128 = 69226631500750271257023520 := by decide +kernel
private theorem rec_3_11_2368_1_part5 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 640 38 = 3517404370825726843734462 := by decide +kernel
private theorem rec_3_11_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 128 256 = 692601390583413478971553856 :=
  phaseBlock_append rec_3_11_2368_1_part1 rec_3_11_2368_1_part2 rfl rfl rfl
private theorem rec_3_11_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 0 384 = 1241954109499713202339318880 :=
  phaseBlock_append rec_3_11_2368_1_part0 rec_3_11_2368_1_join0 rfl rfl rfl
private theorem rec_3_11_2368_1_join2 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 512 166 = 72744035871575998100757982 :=
  phaseBlock_append rec_3_11_2368_1_part4 rec_3_11_2368_1_part5 rfl rfl rfl
private theorem rec_3_11_2368_1_join3 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 384 294 = 241715851264512603437646334 :=
  phaseBlock_append rec_3_11_2368_1_part3 rec_3_11_2368_1_join2 rfl rfl rfl
private theorem rec_3_11_2368_1_join4 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2368 32 1 1 1 1) 0 678 = 1483669960764225805776965214 :=
  phaseBlock_append rec_3_11_2368_1_join1 rec_3_11_2368_1_join3 rfl rfl rfl

private theorem rec_3_11_2368_1 : fastPhase (bank 3 11).shape 179798 2368 32 1 1 1 1 = 1483669960764225805776965214 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_3_11_2368_1_join4

private theorem rec_3_11_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 0 128 = 550479720086529163747503264 := by decide +kernel
private theorem rec_3_11_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 128 128 = 410865354617079253080267936 := by decide +kernel
private theorem rec_3_11_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 256 128 = 283707318739020444867759264 := by decide +kernel
private theorem rec_3_11_2369_0_part3 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 384 128 = 169803752310450952205450400 := by decide +kernel
private theorem rec_3_11_2369_0_part4 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 512 128 = 69947801382164102203206816 := by decide +kernel
private theorem rec_3_11_2369_0_part5 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 640 38 = 3709254936481934119347834 := by decide +kernel
private theorem rec_3_11_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 128 256 = 694572673356099697948027200 :=
  phaseBlock_append rec_3_11_2369_0_part1 rec_3_11_2369_0_part2 rfl rfl rfl
private theorem rec_3_11_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 0 384 = 1245052393442628861695530464 :=
  phaseBlock_append rec_3_11_2369_0_part0 rec_3_11_2369_0_join0 rfl rfl rfl
private theorem rec_3_11_2369_0_join2 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 512 166 = 73657056318646036322554650 :=
  phaseBlock_append rec_3_11_2369_0_part4 rec_3_11_2369_0_part5 rfl rfl rfl
private theorem rec_3_11_2369_0_join3 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 384 294 = 243460808629096988528005050 :=
  phaseBlock_append rec_3_11_2369_0_part3 rec_3_11_2369_0_join2 rfl rfl rfl
private theorem rec_3_11_2369_0_join4 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 0) 0 678 = 1488513202071725850223535514 :=
  phaseBlock_append rec_3_11_2369_0_join1 rec_3_11_2369_0_join3 rfl rfl rfl

private theorem rec_3_11_2369_0 : fastPhase (bank 3 11).shape 179798 2369 32 1 1 1 0 = 1488513202071725850223535514 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_3_11_2369_0_join4

private theorem rec_3_11_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 0 128 = 549357296147390075894877600 := by decide +kernel
private theorem rec_3_11_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 128 128 = 409833257191173885311024544 := by decide +kernel
private theorem rec_3_11_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 256 128 = 282772255517140781670673824 := by decide +kernel
private theorem rec_3_11_2369_1_part3 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 384 128 = 168972389950838157771726240 := by decide +kernel
private theorem rec_3_11_2369_1_part4 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 512 128 = 69226765587232235654253984 := by decide +kernel
private theorem rec_3_11_2369_1_part5 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 640 38 = 3517407409439257806144348 := by decide +kernel
private theorem rec_3_11_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 128 256 = 692605512708314666981698368 :=
  phaseBlock_append rec_3_11_2369_1_part1 rec_3_11_2369_1_part2 rfl rfl rfl
private theorem rec_3_11_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 0 384 = 1241962808855704742876575968 :=
  phaseBlock_append rec_3_11_2369_1_part0 rec_3_11_2369_1_join0 rfl rfl rfl
private theorem rec_3_11_2369_1_join2 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 512 166 = 72744172996671493460398332 :=
  phaseBlock_append rec_3_11_2369_1_part4 rec_3_11_2369_1_part5 rfl rfl rfl
private theorem rec_3_11_2369_1_join3 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 384 294 = 241716562947509651232124572 :=
  phaseBlock_append rec_3_11_2369_1_part3 rec_3_11_2369_1_join2 rfl rfl rfl
private theorem rec_3_11_2369_1_join4 :
    phaseBlock (fastLayerG (bank 3 11).shape 179798 2369 32 1 1 1 1) 0 678 = 1483679371803214394108700540 :=
  phaseBlock_append rec_3_11_2369_1_join1 rec_3_11_2369_1_join3 rfl rfl rfl

private theorem rec_3_11_2369_1 : fastPhase (bank 3 11).shape 179798 2369 32 1 1 1 1 = 1483679371803214394108700540 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_3_11_2369_1_join4

theorem receipt_3_11 : Checked (bank 3 11) 32 1 1 := by
  refine checked_from_values (bank 3 11) 32 1 1
    (P3_7_1.checked (bank 3 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_11_2368_0 rec_3_11_2368_1 rec_3_11_2369_0 rec_3_11_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_12_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 0 128 = 482460471146085357568520992 := by decide +kernel
private theorem rec_3_12_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 128 128 = 360061493157706177195664160 := by decide +kernel
private theorem rec_3_12_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 256 128 = 248601930756954865943302944 := by decide +kernel
private theorem rec_3_12_2368_0_part3 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 384 128 = 148777870156132325680595744 := by decide +kernel
private theorem rec_3_12_2368_0_part4 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 512 128 = 61280728008122767936172832 := by decide +kernel
private theorem rec_3_12_2368_0_part5 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 640 38 = 3249416850751531461882010 := by decide +kernel
private theorem rec_3_12_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 128 256 = 608663423914661043138967104 :=
  phaseBlock_append rec_3_12_2368_0_part1 rec_3_12_2368_0_part2 rfl rfl rfl
private theorem rec_3_12_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 0 384 = 1091123895060746400707488096 :=
  phaseBlock_append rec_3_12_2368_0_part0 rec_3_12_2368_0_join0 rfl rfl rfl
private theorem rec_3_12_2368_0_join2 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 512 166 = 64530144858874299398054842 :=
  phaseBlock_append rec_3_12_2368_0_part4 rec_3_12_2368_0_part5 rfl rfl rfl
private theorem rec_3_12_2368_0_join3 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 384 294 = 213308015015006625078650586 :=
  phaseBlock_append rec_3_12_2368_0_part3 rec_3_12_2368_0_join2 rfl rfl rfl
private theorem rec_3_12_2368_0_join4 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 0) 0 678 = 1304431910075753025786138682 :=
  phaseBlock_append rec_3_12_2368_0_join1 rec_3_12_2368_0_join3 rfl rfl rfl

private theorem rec_3_12_2368_0 : fastPhase (bank 3 12).shape 179798 2368 31 1 1 1 0 = 1304431910075753025786138682 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_3_12_2368_0_join4

private theorem rec_3_12_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 0 128 = 481476357687121262831179936 := by decide +kernel
private theorem rec_3_12_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 128 128 = 359156731960875706760824992 := by decide +kernel
private theorem rec_3_12_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 256 128 = 247782375439356628249376928 := by decide +kernel
private theorem rec_3_12_2368_1_part3 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 384 128 = 148049335962193613048572064 := by decide +kernel
private theorem rec_3_12_2368_1_part4 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 512 128 = 60648991886328906794490016 := by decide +kernel
private theorem rec_3_12_2368_1_part5 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 640 38 = 3081351091507425183708870 := by decide +kernel
private theorem rec_3_12_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 128 256 = 606939107400232335010201920 :=
  phaseBlock_append rec_3_12_2368_1_part1 rec_3_12_2368_1_part2 rfl rfl rfl
private theorem rec_3_12_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 0 384 = 1088415465087353597841381856 :=
  phaseBlock_append rec_3_12_2368_1_part0 rec_3_12_2368_1_join0 rfl rfl rfl
private theorem rec_3_12_2368_1_join2 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 512 166 = 63730342977836331978198886 :=
  phaseBlock_append rec_3_12_2368_1_part4 rec_3_12_2368_1_part5 rfl rfl rfl
private theorem rec_3_12_2368_1_join3 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 384 294 = 211779678940029945026770950 :=
  phaseBlock_append rec_3_12_2368_1_part3 rec_3_12_2368_1_join2 rfl rfl rfl
private theorem rec_3_12_2368_1_join4 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2368 31 1 1 1 1) 0 678 = 1300195144027383542868152806 :=
  phaseBlock_append rec_3_12_2368_1_join1 rec_3_12_2368_1_join3 rfl rfl rfl

private theorem rec_3_12_2368_1 : fastPhase (bank 3 12).shape 179798 2368 31 1 1 1 1 = 1300195144027383542868152806 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_3_12_2368_1_join4

private theorem rec_3_12_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 0 128 = 482464497593749464718968480 := by decide +kernel
private theorem rec_3_12_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 128 128 = 360063882769420948353365664 := by decide +kernel
private theorem rec_3_12_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 256 128 = 248603171396054987246036640 := by decide +kernel
private theorem rec_3_12_2369_0_part3 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 384 128 = 148778377837157017712858784 := by decide +kernel
private theorem rec_3_12_2369_0_part4 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 512 128 = 61280847342726849542342304 := by decide +kernel
private theorem rec_3_12_2369_0_part5 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 640 38 = 3249419683289543751038298 := by decide +kernel
private theorem rec_3_12_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 128 256 = 608667054165475935599402304 :=
  phaseBlock_append rec_3_12_2369_0_part1 rec_3_12_2369_0_part2 rfl rfl rfl
private theorem rec_3_12_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 0 384 = 1091131551759225400318370784 :=
  phaseBlock_append rec_3_12_2369_0_part0 rec_3_12_2369_0_join0 rfl rfl rfl
private theorem rec_3_12_2369_0_join2 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 512 166 = 64530267026016393293380602 :=
  phaseBlock_append rec_3_12_2369_0_part4 rec_3_12_2369_0_part5 rfl rfl rfl
private theorem rec_3_12_2369_0_join3 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 384 294 = 213308644863173411006239386 :=
  phaseBlock_append rec_3_12_2369_0_part3 rec_3_12_2369_0_join2 rfl rfl rfl
private theorem rec_3_12_2369_0_join4 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 0) 0 678 = 1304440196622398811324610170 :=
  phaseBlock_append rec_3_12_2369_0_join1 rec_3_12_2369_0_join3 rfl rfl rfl

private theorem rec_3_12_2369_0 : fastPhase (bank 3 12).shape 179798 2369 31 1 1 1 0 = 1304440196622398811324610170 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_3_12_2369_0_join4

private theorem rec_3_12_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 0 128 = 481480374644663921126664096 := by decide +kernel
private theorem rec_3_12_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 128 128 = 359159114736844294547625888 := by decide +kernel
private theorem rec_3_12_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 256 128 = 247783611501824328016447392 := by decide +kernel
private theorem rec_3_12_2369_1_part3 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 384 128 = 148049840933141816128223136 := by decide +kernel
private theorem rec_3_12_2369_1_part4 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 512 128 = 60649109987552642178459552 := by decide +kernel
private theorem rec_3_12_2369_1_part5 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 640 38 = 3081353785023941539110162 := by decide +kernel
private theorem rec_3_12_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 128 256 = 606942726238668622564073280 :=
  phaseBlock_append rec_3_12_2369_1_part1 rec_3_12_2369_1_part2 rfl rfl rfl
private theorem rec_3_12_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 0 384 = 1088423100883332543690737376 :=
  phaseBlock_append rec_3_12_2369_1_part0 rec_3_12_2369_1_join0 rfl rfl rfl
private theorem rec_3_12_2369_1_join2 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 512 166 = 63730463772576583717569714 :=
  phaseBlock_append rec_3_12_2369_1_part4 rec_3_12_2369_1_part5 rfl rfl rfl
private theorem rec_3_12_2369_1_join3 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 384 294 = 211780304705718399845792850 :=
  phaseBlock_append rec_3_12_2369_1_part3 rec_3_12_2369_1_join2 rfl rfl rfl
private theorem rec_3_12_2369_1_join4 :
    phaseBlock (fastLayerG (bank 3 12).shape 179798 2369 31 1 1 1 1) 0 678 = 1300203405589050943536530226 :=
  phaseBlock_append rec_3_12_2369_1_join1 rec_3_12_2369_1_join3 rfl rfl rfl

private theorem rec_3_12_2369_1 : fastPhase (bank 3 12).shape 179798 2369 31 1 1 1 1 = 1300203405589050943536530226 :=
  phase_of_blockG (n := 678) (by decide +kernel) rec_3_12_2369_1_join4

theorem receipt_3_12 : Checked (bank 3 12) 31 1 1 := by
  refine checked_from_values (bank 3 12) 31 1 1
    (P3_7_1.checked (bank 3 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_12_2368_0 rec_3_12_2368_1 rec_3_12_2369_0 rec_3_12_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_13_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 0 128 = 1988334102640537729351132320 := by decide +kernel
private theorem rec_3_13_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 128 128 = 1622599378236678689797231776 := by decide +kernel
private theorem rec_3_13_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 256 128 = 1279757283160799185124721824 := by decide +kernel
private theorem rec_3_13_2368_0_part3 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 384 128 = 960897613643711879317763232 := by decide +kernel
private theorem rec_3_13_2368_0_part4 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 512 128 = 667104316008706366370374816 := by decide +kernel
private theorem rec_3_13_2368_0_part5 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 640 128 = 399455496117981330091381920 := by decide +kernel
private theorem rec_3_13_2368_0_part6 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 768 128 = 159023428819076703909364896 := by decide +kernel
private theorem rec_3_13_2368_0_part7 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 896 29 = 5517041118203592666425576 := by decide +kernel
private theorem rec_3_13_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 0 256 = 3610933480877216419148364096 :=
  phaseBlock_append rec_3_13_2368_0_part0 rec_3_13_2368_0_part1 rfl rfl rfl
private theorem rec_3_13_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 256 256 = 2240654896804511064442485056 :=
  phaseBlock_append rec_3_13_2368_0_part2 rec_3_13_2368_0_part3 rfl rfl rfl
private theorem rec_3_13_2368_0_join2 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 0 512 = 5851588377681727483590849152 :=
  phaseBlock_append rec_3_13_2368_0_join0 rec_3_13_2368_0_join1 rfl rfl rfl
private theorem rec_3_13_2368_0_join3 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 512 256 = 1066559812126687696461756736 :=
  phaseBlock_append rec_3_13_2368_0_part4 rec_3_13_2368_0_part5 rfl rfl rfl
private theorem rec_3_13_2368_0_join4 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 768 157 = 164540469937280296575790472 :=
  phaseBlock_append rec_3_13_2368_0_part6 rec_3_13_2368_0_part7 rfl rfl rfl
private theorem rec_3_13_2368_0_join5 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 512 413 = 1231100282063967993037547208 :=
  phaseBlock_append rec_3_13_2368_0_join3 rec_3_13_2368_0_join4 rfl rfl rfl
private theorem rec_3_13_2368_0_join6 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 0) 0 925 = 7082688659745695476628396360 :=
  phaseBlock_append rec_3_13_2368_0_join2 rec_3_13_2368_0_join5 rfl rfl rfl

private theorem rec_3_13_2368_0 : fastPhase (bank 3 13).shape 179798 2368 44 1 1 1 0 = 7082688659745695476628396360 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_3_13_2368_0_join6

private theorem rec_3_13_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 0 128 = 1985429469149296388989205344 := by decide +kernel
private theorem rec_3_13_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 128 128 = 1619861837554004930888903520 := by decide +kernel
private theorem rec_3_13_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 256 128 = 1277195998543825800745851744 := by decide +kernel
private theorem rec_3_13_2368_1_part3 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 384 128 = 958521700282686395124648800 := by decide +kernel
private theorem rec_3_13_2368_1_part4 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 512 128 = 664922841103720390824622944 := by decide +kernel
private theorem rec_3_13_2368_1_part5 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 640 128 = 397477478955699904684780384 := by decide +kernel
private theorem rec_3_13_2368_1_part6 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 768 128 = 157257840849467653388753760 := by decide +kernel
private theorem rec_3_13_2368_1_part7 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 896 29 = 5147462595061137789892419 := by decide +kernel
private theorem rec_3_13_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 0 256 = 3605291306703301319878108864 :=
  phaseBlock_append rec_3_13_2368_1_part0 rec_3_13_2368_1_part1 rfl rfl rfl
private theorem rec_3_13_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 256 256 = 2235717698826512195870500544 :=
  phaseBlock_append rec_3_13_2368_1_part2 rec_3_13_2368_1_part3 rfl rfl rfl
private theorem rec_3_13_2368_1_join2 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 0 512 = 5841009005529813515748609408 :=
  phaseBlock_append rec_3_13_2368_1_join0 rec_3_13_2368_1_join1 rfl rfl rfl
private theorem rec_3_13_2368_1_join3 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 512 256 = 1062400320059420295509403328 :=
  phaseBlock_append rec_3_13_2368_1_part4 rec_3_13_2368_1_part5 rfl rfl rfl
private theorem rec_3_13_2368_1_join4 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 768 157 = 162405303444528791178646179 :=
  phaseBlock_append rec_3_13_2368_1_part6 rec_3_13_2368_1_part7 rfl rfl rfl
private theorem rec_3_13_2368_1_join5 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 512 413 = 1224805623503949086688049507 :=
  phaseBlock_append rec_3_13_2368_1_join3 rec_3_13_2368_1_join4 rfl rfl rfl
private theorem rec_3_13_2368_1_join6 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2368 44 1 1 1 1) 0 925 = 7065814629033762602436658915 :=
  phaseBlock_append rec_3_13_2368_1_join2 rec_3_13_2368_1_join5 rfl rfl rfl

private theorem rec_3_13_2368_1 : fastPhase (bank 3 13).shape 179798 2368 44 1 1 1 1 = 7065814629033762602436658915 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_3_13_2368_1_join6

private theorem rec_3_13_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 0 128 = 1988351096494943562799226880 := by decide +kernel
private theorem rec_3_13_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 128 128 = 1622611189331329064659091456 := by decide +kernel
private theorem rec_3_13_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 256 128 = 1279765018273992423075307520 := by decide +kernel
private theorem rec_3_13_2369_0_part3 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 384 128 = 960902266047171347703545856 := by decide +kernel
private theorem rec_3_13_2369_0_part4 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 512 128 = 667106766027432901216772096 := by decide +kernel
private theorem rec_3_13_2369_0_part5 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 640 128 = 399456511689226049807974400 := by decide +kernel
private theorem rec_3_13_2369_0_part6 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 768 128 = 159023666050434213692891136 := by decide +kernel
private theorem rec_3_13_2369_0_part7 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 896 29 = 5517045115709134574717066 := by decide +kernel
private theorem rec_3_13_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 0 256 = 3610962285826272627458318336 :=
  phaseBlock_append rec_3_13_2369_0_part0 rec_3_13_2369_0_part1 rfl rfl rfl
private theorem rec_3_13_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 256 256 = 2240667284321163770778853376 :=
  phaseBlock_append rec_3_13_2369_0_part2 rec_3_13_2369_0_part3 rfl rfl rfl
private theorem rec_3_13_2369_0_join2 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 0 512 = 5851629570147436398237171712 :=
  phaseBlock_append rec_3_13_2369_0_join0 rec_3_13_2369_0_join1 rfl rfl rfl
private theorem rec_3_13_2369_0_join3 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 512 256 = 1066563277716658951024746496 :=
  phaseBlock_append rec_3_13_2369_0_part4 rec_3_13_2369_0_part5 rfl rfl rfl
private theorem rec_3_13_2369_0_join4 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 768 157 = 164540711166143348267608202 :=
  phaseBlock_append rec_3_13_2369_0_part6 rec_3_13_2369_0_part7 rfl rfl rfl
private theorem rec_3_13_2369_0_join5 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 512 413 = 1231103988882802299292354698 :=
  phaseBlock_append rec_3_13_2369_0_join3 rec_3_13_2369_0_join4 rfl rfl rfl
private theorem rec_3_13_2369_0_join6 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 0) 0 925 = 7082733559030238697529526410 :=
  phaseBlock_append rec_3_13_2369_0_join2 rec_3_13_2369_0_join5 rfl rfl rfl

private theorem rec_3_13_2369_0 : fastPhase (bank 3 13).shape 179798 2369 44 1 1 1 0 = 7082733559030238697529526410 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_3_13_2369_0_join6

private theorem rec_3_13_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 0 128 = 1985446434222252799453015360 := by decide +kernel
private theorem rec_3_13_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 128 128 = 1619873625780855622277279040 := by decide +kernel
private theorem rec_3_13_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 256 128 = 1277203716078507572953656640 := by decide +kernel
private theorem rec_3_13_2369_1_part3 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 384 128 = 958526339775955296313748800 := by decide +kernel
private theorem rec_3_13_2369_1_part4 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 512 128 = 664925282262998505434230080 := by decide +kernel
private theorem rec_3_13_2369_1_part5 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 640 128 = 397478489104042532139576640 := by decide +kernel
private theorem rec_3_13_2369_1_part6 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 768 128 = 157258075483650877504793920 := by decide +kernel
private theorem rec_3_13_2369_1_part7 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 896 29 = 5147466334059723676658670 := by decide +kernel
private theorem rec_3_13_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 0 256 = 3605320060003108421730294400 :=
  phaseBlock_append rec_3_13_2369_1_part0 rec_3_13_2369_1_part1 rfl rfl rfl
private theorem rec_3_13_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 256 256 = 2235730055854462869267405440 :=
  phaseBlock_append rec_3_13_2369_1_part2 rec_3_13_2369_1_part3 rfl rfl rfl
private theorem rec_3_13_2369_1_join2 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 0 512 = 5841050115857571290997699840 :=
  phaseBlock_append rec_3_13_2369_1_join0 rec_3_13_2369_1_join1 rfl rfl rfl
private theorem rec_3_13_2369_1_join3 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 512 256 = 1062403771367041037573806720 :=
  phaseBlock_append rec_3_13_2369_1_part4 rec_3_13_2369_1_part5 rfl rfl rfl
private theorem rec_3_13_2369_1_join4 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 768 157 = 162405541817710601181452590 :=
  phaseBlock_append rec_3_13_2369_1_part6 rec_3_13_2369_1_part7 rfl rfl rfl
private theorem rec_3_13_2369_1_join5 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 512 413 = 1224809313184751638755259310 :=
  phaseBlock_append rec_3_13_2369_1_join3 rec_3_13_2369_1_join4 rfl rfl rfl
private theorem rec_3_13_2369_1_join6 :
    phaseBlock (fastLayerG (bank 3 13).shape 179798 2369 44 1 1 1 1) 0 925 = 7065859429042322929752959150 :=
  phaseBlock_append rec_3_13_2369_1_join2 rec_3_13_2369_1_join5 rfl rfl rfl

private theorem rec_3_13_2369_1 : fastPhase (bank 3 13).shape 179798 2369 44 1 1 1 1 = 7065859429042322929752959150 :=
  phase_of_blockG (n := 925) (by decide +kernel) rec_3_13_2369_1_join6

theorem receipt_3_13 : Checked (bank 3 13) 44 1 1 := by
  refine checked_from_values (bank 3 13) 44 1 1
    (P3_7_1.checked (bank 3 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_13_2368_0 rec_3_13_2368_1 rec_3_13_2369_0 rec_3_13_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_14_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 0 128 = 27802398062931421832243640896 := by decide +kernel
private theorem rec_3_14_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 128 128 = 25189426993312833410439985728 := by decide +kernel
private theorem rec_3_14_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 256 128 = 22657037182344398366935841344 := by decide +kernel
private theorem rec_3_14_2368_0_part3 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 384 128 = 20207191693216263001708739136 := by decide +kernel
private theorem rec_3_14_2368_0_part4 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 512 128 = 17841845674016496125068573248 := by decide +kernel
private theorem rec_3_14_2368_0_part5 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 640 128 = 15562946367177521217462549056 := by decide +kernel
private theorem rec_3_14_2368_0_part6 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 768 128 = 13372433118922548589280131648 := by decide +kernel
private theorem rec_3_14_2368_0_part7 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 896 128 = 11272237388712007540657994304 := by decide +kernel
private theorem rec_3_14_2368_0_part8 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 1024 128 = 9264282758689978521284966976 := by decide +kernel
private theorem rec_3_14_2368_0_part9 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 1152 128 = 7350484943130625290206984768 := by decide +kernel
private theorem rec_3_14_2368_0_part10 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 1280 128 = 5532751797884627075632036416 := by decide +kernel
private theorem rec_3_14_2368_0_part11 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 1408 128 = 3812983329825610734735112768 := by decide +kernel
private theorem rec_3_14_2368_0_part12 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 1536 128 = 2193071706296582913463155264 := by decide +kernel
private theorem rec_3_14_2368_0_part13 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 1664 123 = 675766229383819699981067022 := by decide +kernel
private theorem rec_3_14_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 128 256 = 47846464175657231777375827072 :=
  phaseBlock_append rec_3_14_2368_0_part1 rec_3_14_2368_0_part2 rfl rfl rfl
private theorem rec_3_14_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 0 384 = 75648862238588653609619467968 :=
  phaseBlock_append rec_3_14_2368_0_part0 rec_3_14_2368_0_join0 rfl rfl rfl
private theorem rec_3_14_2368_0_join2 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 384 256 = 38049037367232759126777312384 :=
  phaseBlock_append rec_3_14_2368_0_part3 rec_3_14_2368_0_part4 rfl rfl rfl
private theorem rec_3_14_2368_0_join3 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 640 256 = 28935379486100069806742680704 :=
  phaseBlock_append rec_3_14_2368_0_part5 rec_3_14_2368_0_part6 rfl rfl rfl
private theorem rec_3_14_2368_0_join4 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 384 512 = 66984416853332828933519993088 :=
  phaseBlock_append rec_3_14_2368_0_join2 rec_3_14_2368_0_join3 rfl rfl rfl
private theorem rec_3_14_2368_0_join5 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 0 896 = 142633279091921482543139461056 :=
  phaseBlock_append rec_3_14_2368_0_join1 rec_3_14_2368_0_join4 rfl rfl rfl
private theorem rec_3_14_2368_0_join6 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 1024 256 = 16614767701820603811491951744 :=
  phaseBlock_append rec_3_14_2368_0_part8 rec_3_14_2368_0_part9 rfl rfl rfl
private theorem rec_3_14_2368_0_join7 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 896 384 = 27887005090532611352149946048 :=
  phaseBlock_append rec_3_14_2368_0_part7 rec_3_14_2368_0_join6 rfl rfl rfl
private theorem rec_3_14_2368_0_join8 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 1280 256 = 9345735127710237810367149184 :=
  phaseBlock_append rec_3_14_2368_0_part10 rec_3_14_2368_0_part11 rfl rfl rfl
private theorem rec_3_14_2368_0_join9 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 1536 251 = 2868837935680402613444222286 :=
  phaseBlock_append rec_3_14_2368_0_part12 rec_3_14_2368_0_part13 rfl rfl rfl
private theorem rec_3_14_2368_0_join10 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 1280 507 = 12214573063390640423811371470 :=
  phaseBlock_append rec_3_14_2368_0_join8 rec_3_14_2368_0_join9 rfl rfl rfl
private theorem rec_3_14_2368_0_join11 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 896 891 = 40101578153923251775961317518 :=
  phaseBlock_append rec_3_14_2368_0_join7 rec_3_14_2368_0_join10 rfl rfl rfl
private theorem rec_3_14_2368_0_join12 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 0) 0 1787 = 182734857245844734319100778574 :=
  phaseBlock_append rec_3_14_2368_0_join5 rec_3_14_2368_0_join11 rfl rfl rfl

private theorem rec_3_14_2368_0 : fastPhase (bank 3 14).shape 179798 2368 76 1 1 1 0 = 182734857245844734319100778574 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_3_14_2368_0_join12

private theorem rec_3_14_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 0 128 = 27781957004621725921683172032 := by decide +kernel
private theorem rec_3_14_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 128 128 = 25169579777849568786055047872 := by decide +kernel
private theorem rec_3_14_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 256 128 = 22637800355306268627836103360 := by decide +kernel
private theorem rec_3_14_2368_1_part3 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 384 128 = 20188581735126872090458892992 := by decide +kernel
private theorem rec_3_14_2368_1_part4 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 512 128 = 17823879000421077677913205440 := by decide +kernel
private theorem rec_3_14_2368_1_part5 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 640 128 = 15545639328719667914551012032 := by decide +kernel
private theorem rec_3_14_2368_1_part6 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 768 128 = 13355802001420941504891415232 := by decide +kernel
private theorem rec_3_14_2368_1_part7 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 896 128 = 11256298413237145493425597120 := by decide +kernel
private theorem rec_3_14_2368_1_part8 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 1024 128 = 9249052081640907424421767872 := by decide +kernel
private theorem rec_3_14_2368_1_part9 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 1152 128 = 7335978656311667501730114240 := by decide +kernel
private theorem rec_3_14_2368_1_part10 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 1280 128 = 5518985928582110748587748032 := by decide +kernel
private theorem rec_3_14_2368_1_part11 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 1408 128 = 3799973840884599167423654592 := by decide +kernel
private theorem rec_3_14_2368_1_part12 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 1536 128 = 2180834496197603899663641280 := by decide +kernel
private theorem rec_3_14_2368_1_part13 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 1664 123 = 664749377455581175992490070 := by decide +kernel
private theorem rec_3_14_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 128 256 = 47807380133155837413891151232 :=
  phaseBlock_append rec_3_14_2368_1_part1 rec_3_14_2368_1_part2 rfl rfl rfl
private theorem rec_3_14_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 0 384 = 75589337137777563335574323264 :=
  phaseBlock_append rec_3_14_2368_1_part0 rec_3_14_2368_1_join0 rfl rfl rfl
private theorem rec_3_14_2368_1_join2 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 384 256 = 38012460735547949768372098432 :=
  phaseBlock_append rec_3_14_2368_1_part3 rec_3_14_2368_1_part4 rfl rfl rfl
private theorem rec_3_14_2368_1_join3 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 640 256 = 28901441330140609419442427264 :=
  phaseBlock_append rec_3_14_2368_1_part5 rec_3_14_2368_1_part6 rfl rfl rfl
private theorem rec_3_14_2368_1_join4 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 384 512 = 66913902065688559187814525696 :=
  phaseBlock_append rec_3_14_2368_1_join2 rec_3_14_2368_1_join3 rfl rfl rfl
private theorem rec_3_14_2368_1_join5 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 0 896 = 142503239203466122523388848960 :=
  phaseBlock_append rec_3_14_2368_1_join1 rec_3_14_2368_1_join4 rfl rfl rfl
private theorem rec_3_14_2368_1_join6 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 1024 256 = 16585030737952574926151882112 :=
  phaseBlock_append rec_3_14_2368_1_part8 rec_3_14_2368_1_part9 rfl rfl rfl
private theorem rec_3_14_2368_1_join7 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 896 384 = 27841329151189720419577479232 :=
  phaseBlock_append rec_3_14_2368_1_part7 rec_3_14_2368_1_join6 rfl rfl rfl
private theorem rec_3_14_2368_1_join8 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 1280 256 = 9318959769466709916011402624 :=
  phaseBlock_append rec_3_14_2368_1_part10 rec_3_14_2368_1_part11 rfl rfl rfl
private theorem rec_3_14_2368_1_join9 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 1536 251 = 2845583873653185075656131350 :=
  phaseBlock_append rec_3_14_2368_1_part12 rec_3_14_2368_1_part13 rfl rfl rfl
private theorem rec_3_14_2368_1_join10 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 1280 507 = 12164543643119894991667533974 :=
  phaseBlock_append rec_3_14_2368_1_join8 rec_3_14_2368_1_join9 rfl rfl rfl
private theorem rec_3_14_2368_1_join11 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 896 891 = 40005872794309615411245013206 :=
  phaseBlock_append rec_3_14_2368_1_join7 rec_3_14_2368_1_join10 rfl rfl rfl
private theorem rec_3_14_2368_1_join12 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2368 76 1 1 1 1) 0 1787 = 182509111997775737934633862166 :=
  phaseBlock_append rec_3_14_2368_1_join5 rec_3_14_2368_1_join11 rfl rfl rfl

private theorem rec_3_14_2368_1 : fastPhase (bank 3 14).shape 179798 2368 76 1 1 1 1 = 182509111997775737934633862166 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_3_14_2368_1_join12

private theorem rec_3_14_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 0 128 = 27802644821108485823770450208 := by decide +kernel
private theorem rec_3_14_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 128 128 = 25189633812914027272453294368 := by decide +kernel
private theorem rec_3_14_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 256 128 = 22657208344411947386480703776 := by decide +kernel
private theorem rec_3_14_2369_0_part3 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 384 128 = 20207331264193370222900111648 := by decide +kernel
private theorem rec_3_14_2369_0_part4 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 512 128 = 17841957506513639487646832928 := by decide +kernel
private theorem rec_3_14_2369_0_part5 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 640 128 = 15563034100737871086046791968 := by decide +kernel
private theorem rec_3_14_2369_0_part6 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 768 128 = 13372500180786505673319250208 := by decide +kernel
private theorem rec_3_14_2369_0_part7 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 896 128 = 11272286994580861205079533856 := by decide +kernel
private theorem rec_3_14_2369_0_part8 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 1024 128 = 9264317913488685487841761568 := by decide +kernel
private theorem rec_3_14_2369_0_part9 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 1152 128 = 7350508441769708729521572128 := by decide +kernel
private theorem rec_3_14_2369_0_part10 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 1280 128 = 5532766226021196089938852128 := by decide +kernel
private theorem rec_3_14_2369_0_part11 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 1408 128 = 3812991064623500231320463648 := by decide +kernel
private theorem rec_3_14_2369_0_part12 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 1536 128 = 2193074917185613868802971936 := by decide +kernel
private theorem rec_3_14_2369_0_part13 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 1664 123 = 675766879322885735827095637 := by decide +kernel
private theorem rec_3_14_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 128 256 = 47846842157325974658933998144 :=
  phaseBlock_append rec_3_14_2369_0_part1 rec_3_14_2369_0_part2 rfl rfl rfl
private theorem rec_3_14_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 0 384 = 75649486978434460482704448352 :=
  phaseBlock_append rec_3_14_2369_0_part0 rec_3_14_2369_0_join0 rfl rfl rfl
private theorem rec_3_14_2369_0_join2 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 384 256 = 38049288770707009710546944576 :=
  phaseBlock_append rec_3_14_2369_0_part3 rec_3_14_2369_0_part4 rfl rfl rfl
private theorem rec_3_14_2369_0_join3 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 640 256 = 28935534281524376759366042176 :=
  phaseBlock_append rec_3_14_2369_0_part5 rec_3_14_2369_0_part6 rfl rfl rfl
private theorem rec_3_14_2369_0_join4 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 384 512 = 66984823052231386469912986752 :=
  phaseBlock_append rec_3_14_2369_0_join2 rec_3_14_2369_0_join3 rfl rfl rfl
private theorem rec_3_14_2369_0_join5 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 0 896 = 142634310030665846952617435104 :=
  phaseBlock_append rec_3_14_2369_0_join1 rec_3_14_2369_0_join4 rfl rfl rfl
private theorem rec_3_14_2369_0_join6 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 1024 256 = 16614826355258394217363333696 :=
  phaseBlock_append rec_3_14_2369_0_part8 rec_3_14_2369_0_part9 rfl rfl rfl
private theorem rec_3_14_2369_0_join7 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 896 384 = 27887113349839255422442867552 :=
  phaseBlock_append rec_3_14_2369_0_part7 rec_3_14_2369_0_join6 rfl rfl rfl
private theorem rec_3_14_2369_0_join8 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 1280 256 = 9345757290644696321259315776 :=
  phaseBlock_append rec_3_14_2369_0_part10 rec_3_14_2369_0_part11 rfl rfl rfl
private theorem rec_3_14_2369_0_join9 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 1536 251 = 2868841796508499604630067573 :=
  phaseBlock_append rec_3_14_2369_0_part12 rec_3_14_2369_0_part13 rfl rfl rfl
private theorem rec_3_14_2369_0_join10 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 1280 507 = 12214599087153195925889383349 :=
  phaseBlock_append rec_3_14_2369_0_join8 rec_3_14_2369_0_join9 rfl rfl rfl
private theorem rec_3_14_2369_0_join11 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 896 891 = 40101712436992451348332250901 :=
  phaseBlock_append rec_3_14_2369_0_join7 rec_3_14_2369_0_join10 rfl rfl rfl
private theorem rec_3_14_2369_0_join12 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 0) 0 1787 = 182736022467658298300949686005 :=
  phaseBlock_append rec_3_14_2369_0_join5 rec_3_14_2369_0_join11 rfl rfl rfl

private theorem rec_3_14_2369_0 : fastPhase (bank 3 14).shape 179798 2369 76 1 1 1 0 = 182736022467658298300949686005 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_3_14_2369_0_join12

private theorem rec_3_14_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 0 128 = 27782203551885196905870621280 := by decide +kernel
private theorem rec_3_14_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 128 128 = 25169786408962823634803223136 := by decide +kernel
private theorem rec_3_14_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 256 128 = 22637971350129660270226856544 := by decide +kernel
private theorem rec_3_14_2369_1_part3 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 384 128 = 20188721158926377672547289696 := by decide +kernel
private theorem rec_3_14_2369_1_part4 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 512 128 = 17823990704634590066285951584 := by decide +kernel
private theorem rec_3_14_2369_1_part5 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 640 128 = 15545726951722407590582659680 := by decide +kernel
private theorem rec_3_14_2369_1_part6 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 768 128 = 13355868969289988849698347616 := by decide +kernel
private theorem rec_3_14_2369_1_part7 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 896 128 = 11256347940515093463517792864 := by decide +kernel
private theorem rec_3_14_2369_1_part8 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 1024 128 = 9249087172098634618052344416 := by decide +kernel
private theorem rec_3_14_2369_1_part9 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 1152 128 = 7336002103710231615942650464 := by decide +kernel
private theorem rec_3_14_2369_1_part10 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 1280 128 = 5519000317433762426961386080 := by decide +kernel
private theorem rec_3_14_2369_1_part11 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 1408 128 = 3799981547212916238515980896 := by decide +kernel
private theorem rec_3_14_2369_1_part12 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 1536 128 = 2180837688296746006151346784 := by decide +kernel
private theorem rec_3_14_2369_1_part13 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 1664 123 = 664750017406811712160313966 := by decide +kernel
private theorem rec_3_14_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 128 256 = 47807757759092483905030079680 :=
  phaseBlock_append rec_3_14_2369_1_part1 rec_3_14_2369_1_part2 rfl rfl rfl
private theorem rec_3_14_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 0 384 = 75589961310977680810900700960 :=
  phaseBlock_append rec_3_14_2369_1_part0 rec_3_14_2369_1_join0 rfl rfl rfl
private theorem rec_3_14_2369_1_join2 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 384 256 = 38012711863560967738833241280 :=
  phaseBlock_append rec_3_14_2369_1_part3 rec_3_14_2369_1_part4 rfl rfl rfl
private theorem rec_3_14_2369_1_join3 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 640 256 = 28901595921012396440281007296 :=
  phaseBlock_append rec_3_14_2369_1_part5 rec_3_14_2369_1_part6 rfl rfl rfl
private theorem rec_3_14_2369_1_join4 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 384 512 = 66914307784573364179114248576 :=
  phaseBlock_append rec_3_14_2369_1_join2 rec_3_14_2369_1_join3 rfl rfl rfl
private theorem rec_3_14_2369_1_join5 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 0 896 = 142504269095551044990014949536 :=
  phaseBlock_append rec_3_14_2369_1_join1 rec_3_14_2369_1_join4 rfl rfl rfl
private theorem rec_3_14_2369_1_join6 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 1024 256 = 16585089275808866233994994880 :=
  phaseBlock_append rec_3_14_2369_1_part8 rec_3_14_2369_1_part9 rfl rfl rfl
private theorem rec_3_14_2369_1_join7 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 896 384 = 27841437216323959697512787744 :=
  phaseBlock_append rec_3_14_2369_1_part7 rec_3_14_2369_1_join6 rfl rfl rfl
private theorem rec_3_14_2369_1_join8 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 1280 256 = 9318981864646678665477366976 :=
  phaseBlock_append rec_3_14_2369_1_part10 rec_3_14_2369_1_part11 rfl rfl rfl
private theorem rec_3_14_2369_1_join9 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 1536 251 = 2845587705703557718311660750 :=
  phaseBlock_append rec_3_14_2369_1_part12 rec_3_14_2369_1_part13 rfl rfl rfl
private theorem rec_3_14_2369_1_join10 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 1280 507 = 12164569570350236383789027726 :=
  phaseBlock_append rec_3_14_2369_1_join8 rec_3_14_2369_1_join9 rfl rfl rfl
private theorem rec_3_14_2369_1_join11 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 896 891 = 40006006786674196081301815470 :=
  phaseBlock_append rec_3_14_2369_1_join7 rec_3_14_2369_1_join10 rfl rfl rfl
private theorem rec_3_14_2369_1_join12 :
    phaseBlock (fastLayerG (bank 3 14).shape 179798 2369 76 1 1 1 1) 0 1787 = 182510275882225241071316765006 :=
  phaseBlock_append rec_3_14_2369_1_join5 rec_3_14_2369_1_join11 rfl rfl rfl

private theorem rec_3_14_2369_1 : fastPhase (bank 3 14).shape 179798 2369 76 1 1 1 1 = 182510275882225241071316765006 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_3_14_2369_1_join12

theorem receipt_3_14 : Checked (bank 3 14) 76 1 1 := by
  refine checked_from_values (bank 3 14) 76 1 1
    (P3_7_1.checked (bank 3 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_14_2368_0 rec_3_14_2368_1 rec_3_14_2369_0 rec_3_14_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_15_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 0 128 = 93377239599237390171937677024 := by decide +kernel
private theorem rec_3_15_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 128 128 = 84637231363274352703553695456 := by decide +kernel
private theorem rec_3_15_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 256 128 = 76160672394451065856031538912 := by decide +kernel
private theorem rec_3_15_2368_0_part3 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 384 128 = 67954497907232538074979372768 := by decide +kernel
private theorem rec_3_15_2368_0_part4 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 512 128 = 60025628433177556156763266784 := by decide +kernel
private theorem rec_3_15_2368_0_part5 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 640 128 = 52380969830385117408312143584 := by decide +kernel
private theorem rec_3_15_2368_0_part6 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 768 128 = 45027413292940861806922727136 := by decide +kernel
private theorem rec_3_15_2368_0_part7 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 896 128 = 37971835360363504160064491232 := by decide +kernel
private theorem rec_3_15_2368_0_part8 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 1024 128 = 31221097927051266265184607968 := by decide +kernel
private theorem rec_3_15_2368_0_part9 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 1152 128 = 24782048251728309069512896224 := by decide +kernel
private theorem rec_3_15_2368_0_part10 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 1280 128 = 18661518966891164829866770144 := by decide +kernel
private theorem rec_3_15_2368_0_part11 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 1408 128 = 12866328088255169272456187616 := by decide +kernel
private theorem rec_3_15_2368_0_part12 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 1536 128 = 7403279024200893752688598752 := by decide +kernel
private theorem rec_3_15_2368_0_part13 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 1664 123 = 2282082433704069657950935275 := by decide +kernel
private theorem rec_3_15_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 128 256 = 160797903757725418559585234368 :=
  phaseBlock_append rec_3_15_2368_0_part1 rec_3_15_2368_0_part2 rfl rfl rfl
private theorem rec_3_15_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 0 384 = 254175143356962808731522911392 :=
  phaseBlock_append rec_3_15_2368_0_part0 rec_3_15_2368_0_join0 rfl rfl rfl
private theorem rec_3_15_2368_0_join2 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 384 256 = 127980126340410094231742639552 :=
  phaseBlock_append rec_3_15_2368_0_part3 rec_3_15_2368_0_part4 rfl rfl rfl
private theorem rec_3_15_2368_0_join3 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 640 256 = 97408383123325979215234870720 :=
  phaseBlock_append rec_3_15_2368_0_part5 rec_3_15_2368_0_part6 rfl rfl rfl
private theorem rec_3_15_2368_0_join4 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 384 512 = 225388509463736073446977510272 :=
  phaseBlock_append rec_3_15_2368_0_join2 rec_3_15_2368_0_join3 rfl rfl rfl
private theorem rec_3_15_2368_0_join5 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 0 896 = 479563652820698882178500421664 :=
  phaseBlock_append rec_3_15_2368_0_join1 rec_3_15_2368_0_join4 rfl rfl rfl
private theorem rec_3_15_2368_0_join6 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 1024 256 = 56003146178779575334697504192 :=
  phaseBlock_append rec_3_15_2368_0_part8 rec_3_15_2368_0_part9 rfl rfl rfl
private theorem rec_3_15_2368_0_join7 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 896 384 = 93974981539143079494761995424 :=
  phaseBlock_append rec_3_15_2368_0_part7 rec_3_15_2368_0_join6 rfl rfl rfl
private theorem rec_3_15_2368_0_join8 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 1280 256 = 31527847055146334102322957760 :=
  phaseBlock_append rec_3_15_2368_0_part10 rec_3_15_2368_0_part11 rfl rfl rfl
private theorem rec_3_15_2368_0_join9 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 1536 251 = 9685361457904963410639534027 :=
  phaseBlock_append rec_3_15_2368_0_part12 rec_3_15_2368_0_part13 rfl rfl rfl
private theorem rec_3_15_2368_0_join10 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 1280 507 = 41213208513051297512962491787 :=
  phaseBlock_append rec_3_15_2368_0_join8 rec_3_15_2368_0_join9 rfl rfl rfl
private theorem rec_3_15_2368_0_join11 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 896 891 = 135188190052194377007724487211 :=
  phaseBlock_append rec_3_15_2368_0_join7 rec_3_15_2368_0_join10 rfl rfl rfl
private theorem rec_3_15_2368_0_join12 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 0) 0 1787 = 614751842872893259186224908875 :=
  phaseBlock_append rec_3_15_2368_0_join5 rec_3_15_2368_0_join11 rfl rfl rfl

private theorem rec_3_15_2368_0 : fastPhase (bank 3 15).shape 179798 2368 105 1 1 1 0 = 614751842872893259186224908875 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_3_15_2368_0_join12

private theorem rec_3_15_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 0 128 = 93308895864241008858805466848 := by decide +kernel
private theorem rec_3_15_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 128 128 = 84570824964274755553291536096 := by decide +kernel
private theorem rec_3_15_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 256 128 = 76096261452815054975909074656 := by decide +kernel
private theorem rec_3_15_2368_1_part3 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 384 128 = 67892140423775223488183871200 := by decide +kernel
private theorem rec_3_15_2368_1_part4 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 512 128 = 59965382288239085152624490208 := by decide +kernel
private theorem rec_3_15_2368_1_part5 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 640 128 = 52322892783907403892527220448 := by decide +kernel
private theorem rec_3_15_2368_1_part6 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 768 128 = 44971562984544315651781023456 := by decide +kernel
private theorem rec_3_15_2368_1_part7 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 896 128 = 37918269309423760554672482016 := by decide +kernel
private theorem rec_3_15_2368_1_part8 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 1024 128 = 31169873532775915065690748640 := by decide +kernel
private theorem rec_3_15_2368_1_part9 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 1152 128 = 24733222793233624149332494048 := by decide +kernel
private theorem rec_3_15_2368_1_part10 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 1280 128 = 18615149603278833429906855648 := by decide +kernel
private theorem rec_3_15_2368_1_part11 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 1408 128 = 12822471858689021351340386016 := by decide +kernel
private theorem rec_3_15_2368_1_part12 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 1536 128 = 7361992847983631336982001376 := by decide +kernel
private theorem rec_3_15_2368_1_part13 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 1664 123 = 2244883242862484039605988299 := by decide +kernel
private theorem rec_3_15_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 128 256 = 160667086417089810529200610752 :=
  phaseBlock_append rec_3_15_2368_1_part1 rec_3_15_2368_1_part2 rfl rfl rfl
private theorem rec_3_15_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 0 384 = 253975982281330819388006077600 :=
  phaseBlock_append rec_3_15_2368_1_part0 rec_3_15_2368_1_join0 rfl rfl rfl
private theorem rec_3_15_2368_1_join2 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 384 256 = 127857522712014308640808361408 :=
  phaseBlock_append rec_3_15_2368_1_part3 rec_3_15_2368_1_part4 rfl rfl rfl
private theorem rec_3_15_2368_1_join3 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 640 256 = 97294455768451719544308243904 :=
  phaseBlock_append rec_3_15_2368_1_part5 rec_3_15_2368_1_part6 rfl rfl rfl
private theorem rec_3_15_2368_1_join4 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 384 512 = 225151978480466028185116605312 :=
  phaseBlock_append rec_3_15_2368_1_join2 rec_3_15_2368_1_join3 rfl rfl rfl
private theorem rec_3_15_2368_1_join5 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 0 896 = 479127960761796847573122682912 :=
  phaseBlock_append rec_3_15_2368_1_join1 rec_3_15_2368_1_join4 rfl rfl rfl
private theorem rec_3_15_2368_1_join6 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 1024 256 = 55903096326009539215023242688 :=
  phaseBlock_append rec_3_15_2368_1_part8 rec_3_15_2368_1_part9 rfl rfl rfl
private theorem rec_3_15_2368_1_join7 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 896 384 = 93821365635433299769695724704 :=
  phaseBlock_append rec_3_15_2368_1_part7 rec_3_15_2368_1_join6 rfl rfl rfl
private theorem rec_3_15_2368_1_join8 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 1280 256 = 31437621461967854781247241664 :=
  phaseBlock_append rec_3_15_2368_1_part10 rec_3_15_2368_1_part11 rfl rfl rfl
private theorem rec_3_15_2368_1_join9 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 1536 251 = 9606876090846115376587989675 :=
  phaseBlock_append rec_3_15_2368_1_part12 rec_3_15_2368_1_part13 rfl rfl rfl
private theorem rec_3_15_2368_1_join10 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 1280 507 = 41044497552813970157835231339 :=
  phaseBlock_append rec_3_15_2368_1_join8 rec_3_15_2368_1_join9 rfl rfl rfl
private theorem rec_3_15_2368_1_join11 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 896 891 = 134865863188247269927530956043 :=
  phaseBlock_append rec_3_15_2368_1_join7 rec_3_15_2368_1_join10 rfl rfl rfl
private theorem rec_3_15_2368_1_join12 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2368 105 1 1 1 1) 0 1787 = 613993823950044117500653638955 :=
  phaseBlock_append rec_3_15_2368_1_join5 rec_3_15_2368_1_join11 rfl rfl rfl

private theorem rec_3_15_2368_1 : fastPhase (bank 3 15).shape 179798 2368 105 1 1 1 1 = 613993823950044117500653638955 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_3_15_2368_1_join12

private theorem rec_3_15_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 0 128 = 93378057072004033876214531136 := by decide +kernel
private theorem rec_3_15_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 128 128 = 84637916103741281475143976000 := by decide +kernel
private theorem rec_3_15_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 256 128 = 76161238636573980187925660736 := by decide +kernel
private theorem rec_3_15_2369_0_part3 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 384 128 = 67954959181250544069825446976 := by decide +kernel
private theorem rec_3_15_2369_0_part4 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 512 128 = 60025997567009606385757439040 := by decide +kernel
private theorem rec_3_15_2369_0_part5 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 640 128 = 52381258951025572160786711616 := by decide +kernel
private theorem rec_3_15_2369_0_part6 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 768 128 = 45027633827854170730632037440 := by decide +kernel
private theorem rec_3_15_2369_0_part7 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 896 128 = 37971998038878008292168614976 := by decide +kernel
private theorem rec_3_15_2369_0_part8 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 1024 128 = 31221212781752120453930796096 := by decide +kernel
private theorem rec_3_15_2369_0_part9 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 1152 128 = 24782124619849524786614813760 := by decide +kernel
private theorem rec_3_15_2369_0_part10 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 1280 128 = 18661565491706773373581509696 := by decide +kernel
private theorem rec_3_15_2369_0_part11 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 1408 128 = 12866352720469505361359062080 := by decide +kernel
private theorem rec_3_15_2369_0_part12 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 1536 128 = 7403289023337999510145713216 := by decide +kernel
private theorem rec_3_15_2369_0_part13 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 1664 123 = 2282084370872417137628971110 := by decide +kernel
private theorem rec_3_15_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 128 256 = 160799154740315261663069636736 :=
  phaseBlock_append rec_3_15_2369_0_part1 rec_3_15_2369_0_part2 rfl rfl rfl
private theorem rec_3_15_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 0 384 = 254177211812319295539284167872 :=
  phaseBlock_append rec_3_15_2369_0_part0 rec_3_15_2369_0_join0 rfl rfl rfl
private theorem rec_3_15_2369_0_join2 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 384 256 = 127980956748260150455582886016 :=
  phaseBlock_append rec_3_15_2369_0_part3 rec_3_15_2369_0_part4 rfl rfl rfl
private theorem rec_3_15_2369_0_join3 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 640 256 = 97408892778879742891418749056 :=
  phaseBlock_append rec_3_15_2369_0_part5 rec_3_15_2369_0_part6 rfl rfl rfl
private theorem rec_3_15_2369_0_join4 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 384 512 = 225389849527139893347001635072 :=
  phaseBlock_append rec_3_15_2369_0_join2 rec_3_15_2369_0_join3 rfl rfl rfl
private theorem rec_3_15_2369_0_join5 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 0 896 = 479567061339459188886285802944 :=
  phaseBlock_append rec_3_15_2369_0_join1 rec_3_15_2369_0_join4 rfl rfl rfl
private theorem rec_3_15_2369_0_join6 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 1024 256 = 56003337401601645240545609856 :=
  phaseBlock_append rec_3_15_2369_0_part8 rec_3_15_2369_0_part9 rfl rfl rfl
private theorem rec_3_15_2369_0_join7 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 896 384 = 93975335440479653532714224832 :=
  phaseBlock_append rec_3_15_2369_0_part7 rec_3_15_2369_0_join6 rfl rfl rfl
private theorem rec_3_15_2369_0_join8 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 1280 256 = 31527918212176278734940571776 :=
  phaseBlock_append rec_3_15_2369_0_part10 rec_3_15_2369_0_part11 rfl rfl rfl
private theorem rec_3_15_2369_0_join9 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 1536 251 = 9685373394210416647774684326 :=
  phaseBlock_append rec_3_15_2369_0_part12 rec_3_15_2369_0_part13 rfl rfl rfl
private theorem rec_3_15_2369_0_join10 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 1280 507 = 41213291606386695382715256102 :=
  phaseBlock_append rec_3_15_2369_0_join8 rec_3_15_2369_0_join9 rfl rfl rfl
private theorem rec_3_15_2369_0_join11 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 896 891 = 135188627046866348915429480934 :=
  phaseBlock_append rec_3_15_2369_0_join7 rec_3_15_2369_0_join10 rfl rfl rfl
private theorem rec_3_15_2369_0_join12 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 0) 0 1787 = 614755688386325537801715283878 :=
  phaseBlock_append rec_3_15_2369_0_join5 rec_3_15_2369_0_join11 rfl rfl rfl

private theorem rec_3_15_2369_0 : fastPhase (bank 3 15).shape 179798 2369 105 1 1 1 0 = 614755688386325537801715283878 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_3_15_2369_0_join12

private theorem rec_3_15_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 0 128 = 93309712640336338445916598464 := by decide +kernel
private theorem rec_3_15_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 128 128 = 84571509082331628650662637760 := by decide +kernel
private theorem rec_3_15_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 256 128 = 76096827142925782695463809216 := by decide +kernel
private theorem rec_3_15_2369_1_part3 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 384 128 = 67892601212323984271658135744 := by decide +kernel
private theorem rec_3_15_2369_1_part4 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 512 128 = 59965750999298359995459662016 := by decide +kernel
private theorem rec_3_15_2369_1_part5 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 640 128 = 52323181540633531958461182144 := by decide +kernel
private theorem rec_3_15_2369_1_part6 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 768 128 = 44971783210572170278136967360 := by decide +kernel
private theorem rec_3_15_2369_1_part7 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 896 128 = 37918431730260545648345493696 := by decide +kernel
private theorem rec_3_15_2369_1_part8 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 1024 128 = 31169988177194081889832169664 := by decide +kernel
private theorem rec_3_15_2369_1_part9 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 1152 128 = 24733298994662908500732063936 := by decide +kernel
private theorem rec_3_15_2369_1_part10 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 1280 128 = 18615196001197413207072633024 := by decide +kernel
private theorem rec_3_15_2369_1_part11 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 1408 128 = 12822496400013794513276448960 := by decide +kernel
private theorem rec_3_15_2369_1_part12 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 1536 128 = 7362002788459614252663926976 := by decide +kernel
private theorem rec_3_15_2369_1_part13 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 1664 123 = 2244885150519420742875463524 := by decide +kernel
private theorem rec_3_15_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 128 256 = 160668336225257411346126446976 :=
  phaseBlock_append rec_3_15_2369_1_part1 rec_3_15_2369_1_part2 rfl rfl rfl
private theorem rec_3_15_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 0 384 = 253978048865593749792043045440 :=
  phaseBlock_append rec_3_15_2369_1_part0 rec_3_15_2369_1_join0 rfl rfl rfl
private theorem rec_3_15_2369_1_join2 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 384 256 = 127858352211622344267117797760 :=
  phaseBlock_append rec_3_15_2369_1_part3 rec_3_15_2369_1_part4 rfl rfl rfl
private theorem rec_3_15_2369_1_join3 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 640 256 = 97294964751205702236598149504 :=
  phaseBlock_append rec_3_15_2369_1_part5 rec_3_15_2369_1_part6 rfl rfl rfl
private theorem rec_3_15_2369_1_join4 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 384 512 = 225153316962828046503715947264 :=
  phaseBlock_append rec_3_15_2369_1_join2 rec_3_15_2369_1_join3 rfl rfl rfl
private theorem rec_3_15_2369_1_join5 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 0 896 = 479131365828421796295758992704 :=
  phaseBlock_append rec_3_15_2369_1_join1 rec_3_15_2369_1_join4 rfl rfl rfl
private theorem rec_3_15_2369_1_join6 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 1024 256 = 55903287171856990390564233600 :=
  phaseBlock_append rec_3_15_2369_1_part8 rec_3_15_2369_1_part9 rfl rfl rfl
private theorem rec_3_15_2369_1_join7 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 896 384 = 93821718902117536038909727296 :=
  phaseBlock_append rec_3_15_2369_1_part7 rec_3_15_2369_1_join6 rfl rfl rfl
private theorem rec_3_15_2369_1_join8 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 1280 256 = 31437692401211207720349081984 :=
  phaseBlock_append rec_3_15_2369_1_part10 rec_3_15_2369_1_part11 rfl rfl rfl
private theorem rec_3_15_2369_1_join9 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 1536 251 = 9606887938979034995539390500 :=
  phaseBlock_append rec_3_15_2369_1_part12 rec_3_15_2369_1_part13 rfl rfl rfl
private theorem rec_3_15_2369_1_join10 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 1280 507 = 41044580340190242715888472484 :=
  phaseBlock_append rec_3_15_2369_1_join8 rec_3_15_2369_1_join9 rfl rfl rfl
private theorem rec_3_15_2369_1_join11 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 896 891 = 134866299242307778754798199780 :=
  phaseBlock_append rec_3_15_2369_1_join7 rec_3_15_2369_1_join10 rfl rfl rfl
private theorem rec_3_15_2369_1_join12 :
    phaseBlock (fastLayerG (bank 3 15).shape 179798 2369 105 1 1 1 1) 0 1787 = 613997665070729575050557192484 :=
  phaseBlock_append rec_3_15_2369_1_join5 rec_3_15_2369_1_join11 rfl rfl rfl

private theorem rec_3_15_2369_1 : fastPhase (bank 3 15).shape 179798 2369 105 1 1 1 1 = 613997665070729575050557192484 :=
  phase_of_blockG (n := 1787) (by decide +kernel) rec_3_15_2369_1_join12

theorem receipt_3_15 : Checked (bank 3 15) 105 1 1 := by
  refine checked_from_values (bank 3 15) 105 1 1
    (P3_7_1.checked (bank 3 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8067_1786)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_15_2368_0 rec_3_15_2368_1 rec_3_15_2369_0 rec_3_15_2369_1 (by decide +kernel) (by decide +kernel)

private theorem rec_3_16_2368_0_part0 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 0 128 = 317345927215376886578601439200 := by decide +kernel
private theorem rec_3_16_2368_0_part1 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 128 128 = 295338411898685041013731475424 := by decide +kernel
private theorem rec_3_16_2368_0_part2 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 256 128 = 273817505548448298658504953824 := by decide +kernel
private theorem rec_3_16_2368_0_part3 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 384 128 = 252792715293294035894528368608 := by decide +kernel
private theorem rec_3_16_2368_0_part4 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 512 128 = 232273531035806692511021199328 := by decide +kernel
private theorem rec_3_16_2368_0_part5 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 640 128 = 212269425461974203864620859360 := by decide +kernel
private theorem rec_3_16_2368_0_part6 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 768 128 = 192789854050634433039187644384 := by decide +kernel
private theorem rec_3_16_2368_0_part7 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 896 128 = 173844255082921603005609680864 := by decide +kernel
private theorem rec_3_16_2368_0_part8 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1024 128 = 155442049651712728781607874528 := by decide +kernel
private theorem rec_3_16_2368_0_part9 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1152 128 = 137592641671074049591540858848 := by decide +kernel
private theorem rec_3_16_2368_0_part10 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1280 128 = 120305417885707461026209943520 := by decide +kernel
private theorem rec_3_16_2368_0_part11 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1408 128 = 103589747880396947202664062944 := by decide +kernel
private theorem rec_3_16_2368_0_part12 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1536 128 = 87454984089455012924004724704 := by decide +kernel
private theorem rec_3_16_2368_0_part13 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1664 128 = 71910461806169115839190958048 := by decide +kernel
private theorem rec_3_16_2368_0_part14 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1792 128 = 56965499192248098602844262368 := by decide +kernel
private theorem rec_3_16_2368_0_part15 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1920 128 = 42629397287268621035053555680 := by decide +kernel
private theorem rec_3_16_2368_0_part16 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 2048 128 = 28911440018121592281180123104 := by decide +kernel
private theorem rec_3_16_2368_0_part17 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 2176 128 = 15820894208458602971662565344 := by decide +kernel
private theorem rec_3_16_2368_0_part18 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 2304 99 = 3662023797985047005735787585 := by decide +kernel
private theorem rec_3_16_2368_0_join0 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 0 256 = 612684339114061927592332914624 :=
  phaseBlock_append rec_3_16_2368_0_part0 rec_3_16_2368_0_part1 rfl rfl rfl
private theorem rec_3_16_2368_0_join1 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 256 256 = 526610220841742334553033322432 :=
  phaseBlock_append rec_3_16_2368_0_part2 rec_3_16_2368_0_part3 rfl rfl rfl
private theorem rec_3_16_2368_0_join2 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 0 512 = 1139294559955804262145366237056 :=
  phaseBlock_append rec_3_16_2368_0_join0 rec_3_16_2368_0_join1 rfl rfl rfl
private theorem rec_3_16_2368_0_join3 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 512 256 = 444542956497780896375642058688 :=
  phaseBlock_append rec_3_16_2368_0_part4 rec_3_16_2368_0_part5 rfl rfl rfl
private theorem rec_3_16_2368_0_join4 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 896 256 = 329286304734634331787217555392 :=
  phaseBlock_append rec_3_16_2368_0_part7 rec_3_16_2368_0_part8 rfl rfl rfl
private theorem rec_3_16_2368_0_join5 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 768 384 = 522076158785268764826405199776 :=
  phaseBlock_append rec_3_16_2368_0_part6 rec_3_16_2368_0_join4 rfl rfl rfl
private theorem rec_3_16_2368_0_join6 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 512 640 = 966619115283049661202047258464 :=
  phaseBlock_append rec_3_16_2368_0_join3 rec_3_16_2368_0_join5 rfl rfl rfl
private theorem rec_3_16_2368_0_join7 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 0 1152 = 2105913675238853923347413495520 :=
  phaseBlock_append rec_3_16_2368_0_join2 rec_3_16_2368_0_join6 rfl rfl rfl
private theorem rec_3_16_2368_0_join8 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1152 256 = 257898059556781510617750802368 :=
  phaseBlock_append rec_3_16_2368_0_part9 rec_3_16_2368_0_part10 rfl rfl rfl
private theorem rec_3_16_2368_0_join9 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1536 256 = 159365445895624128763195682752 :=
  phaseBlock_append rec_3_16_2368_0_part12 rec_3_16_2368_0_part13 rfl rfl rfl
private theorem rec_3_16_2368_0_join10 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1408 384 = 262955193776021075965859745696 :=
  phaseBlock_append rec_3_16_2368_0_part11 rec_3_16_2368_0_join9 rfl rfl rfl
private theorem rec_3_16_2368_0_join11 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1152 640 = 520853253332802586583610548064 :=
  phaseBlock_append rec_3_16_2368_0_join8 rec_3_16_2368_0_join10 rfl rfl rfl
private theorem rec_3_16_2368_0_join12 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1792 256 = 99594896479516719637897818048 :=
  phaseBlock_append rec_3_16_2368_0_part14 rec_3_16_2368_0_part15 rfl rfl rfl
private theorem rec_3_16_2368_0_join13 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 2176 227 = 19482918006443649977398352929 :=
  phaseBlock_append rec_3_16_2368_0_part17 rec_3_16_2368_0_part18 rfl rfl rfl
private theorem rec_3_16_2368_0_join14 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 2048 355 = 48394358024565242258578476033 :=
  phaseBlock_append rec_3_16_2368_0_part16 rec_3_16_2368_0_join13 rfl rfl rfl
private theorem rec_3_16_2368_0_join15 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1792 611 = 147989254504081961896476294081 :=
  phaseBlock_append rec_3_16_2368_0_join12 rec_3_16_2368_0_join14 rfl rfl rfl
private theorem rec_3_16_2368_0_join16 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 1152 1251 = 668842507836884548480086842145 :=
  phaseBlock_append rec_3_16_2368_0_join11 rec_3_16_2368_0_join15 rfl rfl rfl
private theorem rec_3_16_2368_0_join17 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 0) 0 2403 = 2774756183075738471827500337665 :=
  phaseBlock_append rec_3_16_2368_0_join7 rec_3_16_2368_0_join16 rfl rfl rfl

private theorem rec_3_16_2368_0 : fastPhase (bank 3 16).shape 179798 2368 138 1 1 1 0 = 2774756183075738471827500337665 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_3_16_2368_0_join17

private theorem rec_3_16_2368_1_part0 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 0 128 = 317174511998268927111625949984 := by decide +kernel
private theorem rec_3_16_2368_1_part1 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 128 128 = 295170584999123233494550614816 := by decide +kernel
private theorem rec_3_16_2368_1_part2 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 256 128 = 273653346691184163785187615520 := by decide +kernel
private theorem rec_3_16_2368_1_part3 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 384 128 = 252632304061635304557526922016 := by decide +kernel
private theorem rec_3_16_2368_1_part4 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 512 128 = 232116946871694035143396360992 := by decide +kernel
private theorem rec_3_16_2368_1_part5 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 640 128 = 212116747666057959792266564384 := by decide +kernel
private theorem rec_3_16_2368_1_part6 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 768 128 = 192641161782351339831055917856 := by decide +kernel
private theorem rec_3_16_2368_1_part7 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 896 128 = 173699627360571525823935509280 := by decide +kernel
private theorem rec_3_16_2368_1_part8 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1024 128 = 155301565352535389732134077216 := by decide +kernel
private theorem rec_3_16_2368_1_part9 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1152 128 = 137456379531325757073742959392 := by decide +kernel
private theorem rec_3_16_2368_1_part10 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1280 128 = 120173456500737839083521041184 := by decide +kernel
private theorem rec_3_16_2368_1_part11 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1408 128 = 103462165704725664872699704096 := by decide +kernel
private theorem rec_3_16_2368_1_part12 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1536 128 = 87331859436848513588787774240 := by decide +kernel
private theorem rec_3_16_2368_1_part13 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1664 128 = 71791872849717346575376470816 := by decide +kernel
private theorem rec_3_16_2368_1_part14 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1792 128 = 56851523964441239531944354592 := by decide +kernel
private theorem rec_3_16_2368_1_part15 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1920 128 = 42520113680073814673662276384 := by decide +kernel
private theorem rec_3_16_2368_1_part16 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 2048 128 = 28806925783059672891198325536 := by decide +kernel
private theorem rec_3_16_2368_1_part17 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 2176 128 = 15721226956680825910522778400 := by decide +kernel
private theorem rec_3_16_2368_1_part18 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 2304 99 = 3588310697153274415263646860 := by decide +kernel
private theorem rec_3_16_2368_1_join0 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 0 256 = 612345096997392160606176564800 :=
  phaseBlock_append rec_3_16_2368_1_part0 rec_3_16_2368_1_part1 rfl rfl rfl
private theorem rec_3_16_2368_1_join1 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 256 256 = 526285650752819468342714537536 :=
  phaseBlock_append rec_3_16_2368_1_part2 rec_3_16_2368_1_part3 rfl rfl rfl
private theorem rec_3_16_2368_1_join2 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 0 512 = 1138630747750211628948891102336 :=
  phaseBlock_append rec_3_16_2368_1_join0 rec_3_16_2368_1_join1 rfl rfl rfl
private theorem rec_3_16_2368_1_join3 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 512 256 = 444233694537751994935662925376 :=
  phaseBlock_append rec_3_16_2368_1_part4 rec_3_16_2368_1_part5 rfl rfl rfl
private theorem rec_3_16_2368_1_join4 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 896 256 = 329001192713106915556069586496 :=
  phaseBlock_append rec_3_16_2368_1_part7 rec_3_16_2368_1_part8 rfl rfl rfl
private theorem rec_3_16_2368_1_join5 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 768 384 = 521642354495458255387125504352 :=
  phaseBlock_append rec_3_16_2368_1_part6 rec_3_16_2368_1_join4 rfl rfl rfl
private theorem rec_3_16_2368_1_join6 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 512 640 = 965876049033210250322788429728 :=
  phaseBlock_append rec_3_16_2368_1_join3 rec_3_16_2368_1_join5 rfl rfl rfl
private theorem rec_3_16_2368_1_join7 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 0 1152 = 2104506796783421879271679532064 :=
  phaseBlock_append rec_3_16_2368_1_join2 rec_3_16_2368_1_join6 rfl rfl rfl
private theorem rec_3_16_2368_1_join8 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1152 256 = 257629836032063596157264000576 :=
  phaseBlock_append rec_3_16_2368_1_part9 rec_3_16_2368_1_part10 rfl rfl rfl
private theorem rec_3_16_2368_1_join9 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1536 256 = 159123732286565860164164245056 :=
  phaseBlock_append rec_3_16_2368_1_part12 rec_3_16_2368_1_part13 rfl rfl rfl
private theorem rec_3_16_2368_1_join10 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1408 384 = 262585897991291525036863949152 :=
  phaseBlock_append rec_3_16_2368_1_part11 rec_3_16_2368_1_join9 rfl rfl rfl
private theorem rec_3_16_2368_1_join11 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1152 640 = 520215734023355121194127949728 :=
  phaseBlock_append rec_3_16_2368_1_join8 rec_3_16_2368_1_join10 rfl rfl rfl
private theorem rec_3_16_2368_1_join12 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1792 256 = 99371637644515054205606630976 :=
  phaseBlock_append rec_3_16_2368_1_part14 rec_3_16_2368_1_part15 rfl rfl rfl
private theorem rec_3_16_2368_1_join13 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 2176 227 = 19309537653834100325786425260 :=
  phaseBlock_append rec_3_16_2368_1_part17 rec_3_16_2368_1_part18 rfl rfl rfl
private theorem rec_3_16_2368_1_join14 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 2048 355 = 48116463436893773216984750796 :=
  phaseBlock_append rec_3_16_2368_1_part16 rec_3_16_2368_1_join13 rfl rfl rfl
private theorem rec_3_16_2368_1_join15 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1792 611 = 147488101081408827422591381772 :=
  phaseBlock_append rec_3_16_2368_1_join12 rec_3_16_2368_1_join14 rfl rfl rfl
private theorem rec_3_16_2368_1_join16 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 1152 1251 = 667703835104763948616719331500 :=
  phaseBlock_append rec_3_16_2368_1_join11 rec_3_16_2368_1_join15 rfl rfl rfl
private theorem rec_3_16_2368_1_join17 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2368 138 1 1 1 1) 0 2403 = 2772210631888185827888398863564 :=
  phaseBlock_append rec_3_16_2368_1_join7 rec_3_16_2368_1_join16 rfl rfl rfl

private theorem rec_3_16_2368_1 : fastPhase (bank 3 16).shape 179798 2368 138 1 1 1 1 = 2772210631888185827888398863564 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_3_16_2368_1_join17

private theorem rec_3_16_2369_0_part0 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 0 128 = 317348734989839201987485181472 := by decide +kernel
private theorem rec_3_16_2369_0_part1 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 128 128 = 295340878546462814138921768480 := by decide +kernel
private theorem rec_3_16_2369_0_part2 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 256 128 = 273819658044334333062241617440 := by decide +kernel
private theorem rec_3_16_2369_0_part3 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 384 128 = 252794579635147570817202861600 := by decide +kernel
private theorem rec_3_16_2369_0_part4 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 512 128 = 232275132246196733705964873248 := by decide +kernel
private theorem rec_3_16_2369_0_part5 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 640 128 = 212270787589821974823590991392 := by decide +kernel
private theorem rec_3_16_2369_0_part6 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 768 128 = 192791000172854946608551249440 := by decide +kernel
private theorem rec_3_16_2369_0_part7 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 896 128 = 173845207306064353393225102880 := by decide +kernel
private theorem rec_3_16_2369_0_part8 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1024 128 = 155442829113601503954404156960 := by decide +kernel
private theorem rec_3_16_2369_0_part9 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1152 128 = 137593268542445864063794894368 := by decide +kernel
private theorem rec_3_16_2369_0_part10 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1280 128 = 120305911371850609038521402912 := by decide +kernel
private theorem rec_3_16_2369_0_part11 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1408 128 = 103590126222788176291628103200 := by decide +kernel
private theorem rec_3_16_2369_0_part12 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1536 128 = 87455264567395817882582476320 := by decide +kernel
private theorem rec_3_16_2369_0_part13 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1664 128 = 71910660738421153067777791520 := by decide +kernel
private theorem rec_3_16_2369_0_part14 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1792 128 = 56965631938667720851035833888 := by decide +kernel
private theorem rec_3_16_2369_0_part15 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1920 128 = 42629478250440532534109632032 := by decide +kernel
private theorem rec_3_16_2369_0_part16 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 2048 128 = 28911482644991624267186185760 := by decide +kernel
private theorem rec_3_16_2369_0_part17 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 2176 128 = 15820910991965609599389193760 := by decide +kernel
private theorem rec_3_16_2369_0_part18 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 2304 99 = 3662026406237947062458324775 := by decide +kernel
private theorem rec_3_16_2369_0_join0 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 0 256 = 612689613536302016126406949952 :=
  phaseBlock_append rec_3_16_2369_0_part0 rec_3_16_2369_0_part1 rfl rfl rfl
private theorem rec_3_16_2369_0_join1 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 256 256 = 526614237679481903879444479040 :=
  phaseBlock_append rec_3_16_2369_0_part2 rec_3_16_2369_0_part3 rfl rfl rfl
private theorem rec_3_16_2369_0_join2 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 0 512 = 1139303851215783920005851428992 :=
  phaseBlock_append rec_3_16_2369_0_join0 rec_3_16_2369_0_join1 rfl rfl rfl
private theorem rec_3_16_2369_0_join3 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 512 256 = 444545919836018708529555864640 :=
  phaseBlock_append rec_3_16_2369_0_part4 rec_3_16_2369_0_part5 rfl rfl rfl
private theorem rec_3_16_2369_0_join4 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 896 256 = 329288036419665857347629259840 :=
  phaseBlock_append rec_3_16_2369_0_part7 rec_3_16_2369_0_part8 rfl rfl rfl
private theorem rec_3_16_2369_0_join5 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 768 384 = 522079036592520803956180509280 :=
  phaseBlock_append rec_3_16_2369_0_part6 rec_3_16_2369_0_join4 rfl rfl rfl
private theorem rec_3_16_2369_0_join6 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 512 640 = 966624956428539512485736373920 :=
  phaseBlock_append rec_3_16_2369_0_join3 rec_3_16_2369_0_join5 rfl rfl rfl
private theorem rec_3_16_2369_0_join7 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 0 1152 = 2105928807644323432491587802912 :=
  phaseBlock_append rec_3_16_2369_0_join2 rec_3_16_2369_0_join6 rfl rfl rfl
private theorem rec_3_16_2369_0_join8 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1152 256 = 257899179914296473102316297280 :=
  phaseBlock_append rec_3_16_2369_0_part9 rec_3_16_2369_0_part10 rfl rfl rfl
private theorem rec_3_16_2369_0_join9 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1536 256 = 159365925305816970950360267840 :=
  phaseBlock_append rec_3_16_2369_0_part12 rec_3_16_2369_0_part13 rfl rfl rfl
private theorem rec_3_16_2369_0_join10 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1408 384 = 262956051528605147241988371040 :=
  phaseBlock_append rec_3_16_2369_0_part11 rec_3_16_2369_0_join9 rfl rfl rfl
private theorem rec_3_16_2369_0_join11 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1152 640 = 520855231442901620344304668320 :=
  phaseBlock_append rec_3_16_2369_0_join8 rec_3_16_2369_0_join10 rfl rfl rfl
private theorem rec_3_16_2369_0_join12 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1792 256 = 99595110189108253385145465920 :=
  phaseBlock_append rec_3_16_2369_0_part14 rec_3_16_2369_0_part15 rfl rfl rfl
private theorem rec_3_16_2369_0_join13 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 2176 227 = 19482937398203556661847518535 :=
  phaseBlock_append rec_3_16_2369_0_part17 rec_3_16_2369_0_part18 rfl rfl rfl
private theorem rec_3_16_2369_0_join14 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 2048 355 = 48394420043195180929033704295 :=
  phaseBlock_append rec_3_16_2369_0_part16 rec_3_16_2369_0_join13 rfl rfl rfl
private theorem rec_3_16_2369_0_join15 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1792 611 = 147989530232303434314179170215 :=
  phaseBlock_append rec_3_16_2369_0_join12 rec_3_16_2369_0_join14 rfl rfl rfl
private theorem rec_3_16_2369_0_join16 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 1152 1251 = 668844761675205054658483838535 :=
  phaseBlock_append rec_3_16_2369_0_join11 rec_3_16_2369_0_join15 rfl rfl rfl
private theorem rec_3_16_2369_0_join17 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 0) 0 2403 = 2774773569319528487150071641447 :=
  phaseBlock_append rec_3_16_2369_0_join7 rec_3_16_2369_0_join16 rfl rfl rfl

private theorem rec_3_16_2369_0 : fastPhase (bank 3 16).shape 179798 2369 138 1 1 1 0 = 2774773569319528487150071641447 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_3_16_2369_0_join17

private theorem rec_3_16_2369_1_part0 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 0 128 = 317177318005665301971646992480 := by decide +kernel
private theorem rec_3_16_2369_1_part1 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 128 128 = 295173050019863004746976903264 := by decide +kernel
private theorem rec_3_16_2369_1_part2 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 256 128 = 273655497694694916630330912864 := by decide +kernel
private theorem rec_3_16_2369_1_part3 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 384 128 = 252634167040421018056174116960 := by decide +kernel
private theorem rec_3_16_2369_1_part4 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 512 128 = 232118546842978407416600629344 := by decide +kernel
private theorem rec_3_16_2369_1_part5 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 640 128 = 212118108673426853611836309600 := by decide +kernel
private theorem rec_3_16_2369_1_part6 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 768 128 = 192642306897394348600741490784 := by decide +kernel
private theorem rec_3_16_2369_1_part7 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 896 128 = 173700578684522659951313707104 := by decide +kernel
private theorem rec_3_16_2369_1_part8 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1024 128 = 155302344017912883391190421600 := by decide +kernel
private theorem rec_3_16_2369_1_part9 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1152 128 = 137457005703570995358151753824 := by decide +kernel
private theorem rec_3_16_2369_1_part10 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1280 128 = 120173949379853405550623207520 := by decide +kernel
private theorem rec_3_16_2369_1_part11 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1408 128 = 103462543526912509478178398304 := by decide +kernel
private theorem rec_3_16_2369_1_part12 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1536 128 = 87332139476142241012041781344 := by decide +kernel
private theorem rec_3_16_2369_1_part13 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1664 128 = 71792071419623624935591379040 := by decide +kernel
private theorem rec_3_16_2369_1_part14 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1792 128 = 56851656419570329494861508704 := by decide +kernel
private theorem rec_3_16_2369_1_part15 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1920 128 = 42520194417774218949045510240 := by decide +kernel
private theorem rec_3_16_2369_1_part16 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 2048 128 = 28806968245050906120998473824 := by decide +kernel
private theorem rec_3_16_2369_1_part17 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 2176 128 = 15721243630685304947739967584 := by decide +kernel
private theorem rec_3_16_2369_1_part18 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 2304 99 = 3588313255389592381390393116 := by decide +kernel
private theorem rec_3_16_2369_1_join0 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 0 256 = 612350368025528306718623895744 :=
  phaseBlock_append rec_3_16_2369_1_part0 rec_3_16_2369_1_part1 rfl rfl rfl
private theorem rec_3_16_2369_1_join1 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 256 256 = 526289664735115934686505029824 :=
  phaseBlock_append rec_3_16_2369_1_part2 rec_3_16_2369_1_part3 rfl rfl rfl
private theorem rec_3_16_2369_1_join2 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 0 512 = 1138640032760644241405128925568 :=
  phaseBlock_append rec_3_16_2369_1_join0 rec_3_16_2369_1_join1 rfl rfl rfl
private theorem rec_3_16_2369_1_join3 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 512 256 = 444236655516405261028436938944 :=
  phaseBlock_append rec_3_16_2369_1_part4 rec_3_16_2369_1_part5 rfl rfl rfl
private theorem rec_3_16_2369_1_join4 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 896 256 = 329002922702435543342504128704 :=
  phaseBlock_append rec_3_16_2369_1_part7 rec_3_16_2369_1_part8 rfl rfl rfl
private theorem rec_3_16_2369_1_join5 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 768 384 = 521645229599829891943245619488 :=
  phaseBlock_append rec_3_16_2369_1_part6 rec_3_16_2369_1_join4 rfl rfl rfl
private theorem rec_3_16_2369_1_join6 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 512 640 = 965881885116235152971682558432 :=
  phaseBlock_append rec_3_16_2369_1_join3 rec_3_16_2369_1_join5 rfl rfl rfl
private theorem rec_3_16_2369_1_join7 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 0 1152 = 2104521917876879394376811484000 :=
  phaseBlock_append rec_3_16_2369_1_join2 rec_3_16_2369_1_join6 rfl rfl rfl
private theorem rec_3_16_2369_1_join8 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1152 256 = 257630955083424400908774961344 :=
  phaseBlock_append rec_3_16_2369_1_part9 rec_3_16_2369_1_part10 rfl rfl rfl
private theorem rec_3_16_2369_1_join9 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1536 256 = 159124210895765865947633160384 :=
  phaseBlock_append rec_3_16_2369_1_part12 rec_3_16_2369_1_part13 rfl rfl rfl
private theorem rec_3_16_2369_1_join10 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1408 384 = 262586754422678375425811558688 :=
  phaseBlock_append rec_3_16_2369_1_part11 rec_3_16_2369_1_join9 rfl rfl rfl
private theorem rec_3_16_2369_1_join11 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1152 640 = 520217709506102776334586520032 :=
  phaseBlock_append rec_3_16_2369_1_join8 rec_3_16_2369_1_join10 rfl rfl rfl
private theorem rec_3_16_2369_1_join12 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1792 256 = 99371850837344548443907018944 :=
  phaseBlock_append rec_3_16_2369_1_part14 rec_3_16_2369_1_part15 rfl rfl rfl
private theorem rec_3_16_2369_1_join13 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 2176 227 = 19309556886074897329130360700 :=
  phaseBlock_append rec_3_16_2369_1_part17 rec_3_16_2369_1_part18 rfl rfl rfl
private theorem rec_3_16_2369_1_join14 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 2048 355 = 48116525131125803450128834524 :=
  phaseBlock_append rec_3_16_2369_1_part16 rec_3_16_2369_1_join13 rfl rfl rfl
private theorem rec_3_16_2369_1_join15 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1792 611 = 147488375968470351894035853468 :=
  phaseBlock_append rec_3_16_2369_1_join12 rec_3_16_2369_1_join14 rfl rfl rfl
private theorem rec_3_16_2369_1_join16 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 1152 1251 = 667706085474573128228622373500 :=
  phaseBlock_append rec_3_16_2369_1_join11 rec_3_16_2369_1_join15 rfl rfl rfl
private theorem rec_3_16_2369_1_join17 :
    phaseBlock (fastLayerG (bank 3 16).shape 179798 2369 138 1 1 1 1) 0 2403 = 2772228003351452522605433857500 :=
  phaseBlock_append rec_3_16_2369_1_join7 rec_3_16_2369_1_join16 rfl rfl rfl

private theorem rec_3_16_2369_1 : fastPhase (bank 3 16).shape 179798 2369 138 1 1 1 1 = 2772228003351452522605433857500 :=
  phase_of_blockG (n := 2403) (by decide +kernel) rec_3_16_2369_1_join17

theorem receipt_3_16 : Checked (bank 3 16) 138 1 1 := by
  refine checked_from_values (bank 3 16) 138 1 1
    (P3_7_1.checked (bank 3 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_10849_2402)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_3_16_2368_0 rec_3_16_2368_1 rec_3_16_2369_0 rec_3_16_2369_1 (by decide +kernel) (by decide +kernel)

theorem rect3_checked (i : Fin 17) (hi : i ≠ 0) :
    Checked (bank 3 i) (reserve i) (excess 3) (seed 3) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact receipt_3_1
  · exact receipt_3_2
  · exact receipt_3_3
  · exact receipt_3_4
  · exact receipt_3_5
  · exact receipt_3_6
  · exact receipt_3_7
  · exact receipt_3_8
  · exact receipt_3_9
  · exact receipt_3_10
  · exact receipt_3_11
  · exact receipt_3_12
  · exact receipt_3_13
  · exact receipt_3_14
  · exact receipt_3_15
  · exact receipt_3_16

end Lower6961.Lo.RescueSource
