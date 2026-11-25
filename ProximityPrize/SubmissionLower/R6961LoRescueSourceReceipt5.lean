import ProximityPrize.SubmissionLower.R6961LoRescueSourceSchedule
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
open Lower6961.Lo.RescuePoolMoments

private def pchk (f : ℕ → ℕ) : ℕ → List (ℕ × ℕ) → Option (ℕ × ℕ)
  | _, [] => some (0, 0)
  | s, (n, v) :: rest =>
      if phaseBlock f s n == v then
        match pchk f (s + n) rest with
        | some (tn, tv) => some (n + tn, v + tv)
        | none => none
      else none

private theorem pchk_sound {f : ℕ → ℕ} {s tn tv : ℕ} {cs : List (ℕ × ℕ)}
    (h : pchk f s cs = some (tn, tv)) : phaseBlock f s tn = tv := by
  induction cs generalizing s tn tv with
  | nil =>
    simp only [pchk, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; rfl
  | cons cv rest ih =>
    rcases cv with ⟨n, v⟩
    unfold pchk at h
    split at h
    · rename_i heq
      cases hrest : pchk f (s + n) rest with
      | none => simp [hrest] at h
      | some p =>
        rw [hrest] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact phaseBlock_append (Nat.eq_of_beq_eq_true heq) (ih hrest) rfl rfl rfl
    · simp at h

private theorem ps {f : ℕ → ℕ} {s n1 v1 : ℕ} (n2 v2 n v : ℕ) (cs : List (ℕ × ℕ))
    (h1 : phaseBlock f s n1 = v1) (h2 : pchk f (s + n1) cs = some (n2, v2))
    (hn : n1 + n2 = n) (hv : v1 + v2 = v) : phaseBlock f s n = v :=
  phaseBlock_append h1 (pchk_sound h2) rfl hn hv

private theorem p1 (r : Fin 10) (s : Fin 17) (h a b c d e n z : ℕ) (cs : List (ℕ × ℕ))
    (h1 : (bank r s).shape.J / b + 1 = n)
    (h2 : pchk (fastLayer (bank r s).shape 179808 h a b c d e) 0 cs = some (n, z)) :
    fastPhase (bank r s).shape 179808 h a b c d e = z :=
  phase_of_block h1 (pchk_sound h2)

private theorem rec_5_1_2346_0 : fastPhase (bank 5 1).shape 179808 2346 1 1 4 1 0 = 2031320849467299611477 := p1 5 1 2346 1 1 4 1 0 130 2031320849467299611477 [(128,2031320849467299611477),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_1_2346_1 : fastPhase (bank 5 1).shape 179808 2346 1 1 4 1 1 = 1989792959911637627681 := p1 5 1 2346 1 1 4 1 1 130 1989792959911637627681 [(128,1989792959911637627681),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_1_2347_0 : fastPhase (bank 5 1).shape 179808 2347 1 1 4 1 0 = 2031331338504973337758 := p1 5 1 2347 1 1 4 1 0 130 2031331338504973337758 [(128,2031331338504973337758),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_1_2347_1 : fastPhase (bank 5 1).shape 179808 2347 1 1 4 1 1 = 1989803152095265065936 := p1 5 1 2347 1 1 4 1 1 130 1989803152095265065936 [(128,1989803152095265065936),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_1 : Checked (bank 5 1) 1 4 1 := by
  refine checked_from_values (bank 5 1) 1 4 1
    (P3_7_1.checked (bank 5 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_1_2346_0 rec_5_1_2346_1 rec_5_1_2347_0 rec_5_1_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_2_2346_0 : fastPhase (bank 5 2).shape 179808 2346 2 1 4 1 0 = 2319046678839098044073 := p1 5 2 2346 2 1 4 1 0 130 2319046678839098044073 [(128,2319046678839098044073),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_2_2346_1 : fastPhase (bank 5 2).shape 179808 2346 2 1 4 1 1 = 2271671102652654678437 := p1 5 2 2346 2 1 4 1 1 130 2271671102652654678437 [(128,2271671102652654678437),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_2_2347_0 : fastPhase (bank 5 2).shape 179808 2347 2 1 4 1 0 = 2319058537157046990332 := p1 5 2 2347 2 1 4 1 0 130 2319058537157046990332 [(128,2319058537157046990332),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_2_2347_1 : fastPhase (bank 5 2).shape 179808 2347 2 1 4 1 1 = 2271682625146926294430 := p1 5 2 2347 2 1 4 1 1 130 2271682625146926294430 [(128,2271682625146926294430),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_2 : Checked (bank 5 2) 2 4 1 := by
  refine checked_from_values (bank 5 2) 2 4 1
    (P3_7_1.checked (bank 5 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_2_2346_0 rec_5_2_2346_1 rec_5_2_2347_0 rec_5_2_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_3_2346_0 : fastPhase (bank 5 3).shape 179808 2346 3 1 4 1 0 = 2671424661806753151384 := p1 5 3 2346 3 1 4 1 0 130 2671424661806753151384 [(128,2671424661806753151384),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_3_2346_1 : fastPhase (bank 5 3).shape 179808 2346 3 1 4 1 1 = 2616890034911262859648 := p1 5 3 2346 3 1 4 1 1 130 2616890034911262859648 [(128,2616890034911262859648),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_3_2347_0 : fastPhase (bank 5 3).shape 179808 2347 3 1 4 1 0 = 2671438187857665422124 := p1 5 3 2347 3 1 4 1 0 130 2671438187857665422124 [(128,2671438187857665422124),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_3_2347_1 : fastPhase (bank 5 3).shape 179808 2347 3 1 4 1 1 = 2616903177651350195072 := p1 5 3 2347 3 1 4 1 1 130 2616903177651350195072 [(128,2616903177651350195072),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_3 : Checked (bank 5 3) 3 4 1 := by
  refine checked_from_values (bank 5 3) 3 4 1
    (P3_7_1.checked (bank 5 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_3_2346_0 rec_5_3_2346_1 rec_5_3_2347_0 rec_5_3_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_4_2346_0 : fastPhase (bank 5 4).shape 179808 2346 4 1 4 1 0 = 3111226848768471673020 := p1 5 4 2346 4 1 4 1 0 130 3111226848768471673020 [(128,3111226848768471673020),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_4_2346_1 : fastPhase (bank 5 4).shape 179808 2346 4 1 4 1 1 = 3047760281651799454284 := p1 5 4 2346 4 1 4 1 1 130 3047760281651799454284 [(128,3047760281651799454284),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_4_2347_0 : fastPhase (bank 5 4).shape 179808 2347 4 1 4 1 0 = 3111242445404340919716 := p1 5 4 2347 4 1 4 1 0 130 3111242445404340919716 [(128,3111242445404340919716),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_4_2347_1 : fastPhase (bank 5 4).shape 179808 2347 4 1 4 1 1 = 3047775435991693583964 := p1 5 4 2347 4 1 4 1 1 130 3047775435991693583964 [(128,3047775435991693583964),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_4 : Checked (bank 5 4) 4 4 1 := by
  refine checked_from_values (bank 5 4) 4 4 1
    (P3_7_1.checked (bank 5 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_4_2346_0 rec_5_4_2346_1 rec_5_4_2347_0 rec_5_4_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_5_2346_0 : fastPhase (bank 5 5).shape 179808 2346 5 1 4 1 0 = 3668637689825063843981 := p1 5 5 2346 5 1 4 1 0 130 3668637689825063843981 [(128,3668637689825063843981),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_5_2346_1 : fastPhase (bank 5 5).shape 179808 2346 5 1 4 1 1 = 3593854799292043115945 := p1 5 5 2346 5 1 4 1 1 130 3593854799292043115945 [(128,3593854799292043115945),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_5_2347_0 : fastPhase (bank 5 5).shape 179808 2347 5 1 4 1 0 = 3668655896528542448774 := p1 5 5 2347 5 1 4 1 0 130 3668655896528542448774 [(128,3668655896528542448774),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_5_2347_1 : fastPhase (bank 5 5).shape 179808 2347 5 1 4 1 1 = 3593872489309858201552 := p1 5 5 2347 5 1 4 1 1 130 3593872489309858201552 [(128,3593872489309858201552),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_5 : Checked (bank 5 5) 5 4 1 := by
  refine checked_from_values (bank 5 5) 5 4 1
    (P3_7_1.checked (bank 5 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_5_2346_0 rec_5_5_2346_1 rec_5_5_2347_0 rec_5_5_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_6_2346_0 : fastPhase (bank 5 6).shape 179808 2346 7 1 4 1 0 = 5345034850915038708678 := p1 5 6 2346 7 1 4 1 0 130 5345034850915038708678 [(128,5345034850915038708678),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_6_2346_1 : fastPhase (bank 5 6).shape 179808 2346 7 1 4 1 1 = 5236237922954287269502 := p1 5 6 2346 7 1 4 1 1 130 5236237922954287269502 [(128,5236237922954287269502),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_6_2347_0 : fastPhase (bank 5 6).shape 179808 2347 7 1 4 1 0 = 5345060840305445053368 := p1 5 6 2347 7 1 4 1 0 130 5345060840305445053368 [(128,5345060840305445053368),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_6_2347_1 : fastPhase (bank 5 6).shape 179808 2347 7 1 4 1 1 = 5236263173672718245516 := p1 5 6 2347 7 1 4 1 1 130 5236263173672718245516 [(128,5236263173672718245516),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_6 : Checked (bank 5 6) 7 4 1 := by
  refine checked_from_values (bank 5 6) 7 4 1
    (P3_7_1.checked (bank 5 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_6_2346_0 rec_5_6_2346_1 rec_5_6_2347_0 rec_5_6_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_7_2346_0 : fastPhase (bank 5 7).shape 179808 2346 10 1 4 1 0 = 11236072639105167189036 := p1 5 7 2346 10 1 4 1 0 130 11236072639105167189036 [(128,11236072639105167189036),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_7_2346_1 : fastPhase (bank 5 7).shape 179808 2346 10 1 4 1 1 = 11007863315101323763900 := p1 5 7 2346 10 1 4 1 1 130 11007863315101323763900 [(128,11007863315101323763900),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_7_2347_0 : fastPhase (bank 5 7).shape 179808 2347 10 1 4 1 0 = 11236125579255914356884 := p1 5 7 2347 10 1 4 1 0 130 11236125579255914356884 [(128,11236125579255914356884),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_7_2347_1 : fastPhase (bank 5 7).shape 179808 2347 10 1 4 1 1 = 11007914746836416955212 := p1 5 7 2347 10 1 4 1 1 130 11007914746836416955212 [(128,11007914746836416955212),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_7 : Checked (bank 5 7) 10 4 1 := by
  refine checked_from_values (bank 5 7) 10 4 1
    (P3_7_1.checked (bank 5 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_7_2346_0 rec_5_7_2346_1 rec_5_7_2347_0 rec_5_7_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_8_2346_0 : fastPhase (bank 5 8).shape 179808 2346 16 1 4 1 0 = 61281647855786184464586 := p1 5 8 2346 16 1 4 1 0 191 61281647855786184464586 [(128,59382177624607080973184),(63,1899470231179103491402)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_8_2346_1 : fastPhase (bank 5 8).shape 179808 2346 16 1 4 1 1 = 60432009092312592265858 := p1 5 8 2346 16 1 4 1 1 191 60432009092312592265858 [(128,58640576508694321919232),(63,1791432583618270346626)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_8_2347_0 : fastPhase (bank 5 8).shape 179808 2347 16 1 4 1 0 = 61281933657599252529780 := p1 5 8 2347 16 1 4 1 0 191 61281933657599252529780 [(128,59382465273134795989120),(63,1899468384464456540660)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_8_2347_1 : fastPhase (bank 5 8).shape 179808 2347 16 1 4 1 1 = 60432289324374108475856 := p1 5 8 2347 16 1 4 1 1 191 60432289324374108475856 [(128,58640858495647284476928),(63,1791430828726823998928)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_8 : Checked (bank 5 8) 16 4 1 := by
  refine checked_from_values (bank 5 8) 16 4 1
    (P3_7_1.checked (bank 5 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_8_2346_0 rec_5_8_2346_1 rec_5_8_2347_0 rec_5_8_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_9_2346_0 : fastPhase (bank 5 9).shape 179808 2346 10 1 4 1 0 = 11236072639105167189036 := p1 5 9 2346 10 1 4 1 0 130 11236072639105167189036 [(128,11236072639105167189036),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_9_2346_1 : fastPhase (bank 5 9).shape 179808 2346 10 1 4 1 1 = 11007863315101323763900 := p1 5 9 2346 10 1 4 1 1 130 11007863315101323763900 [(128,11007863315101323763900),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_9_2347_0 : fastPhase (bank 5 9).shape 179808 2347 10 1 4 1 0 = 11236125579255914356884 := p1 5 9 2347 10 1 4 1 0 130 11236125579255914356884 [(128,11236125579255914356884),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_9_2347_1 : fastPhase (bank 5 9).shape 179808 2347 10 1 4 1 1 = 11007914746836416955212 := p1 5 9 2347 10 1 4 1 1 130 11007914746836416955212 [(128,11007914746836416955212),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_9 : Checked (bank 5 9) 10 4 1 := by
  refine checked_from_values (bank 5 9) 10 4 1
    (P3_7_1.checked (bank 5 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_9_2346_0 rec_5_9_2346_1 rec_5_9_2347_0 rec_5_9_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_10_2346_0 : fastPhase (bank 5 10).shape 179808 2346 20 1 4 1 0 = 123987954645049742096997 := p1 5 10 2346 20 1 4 1 0 191 123987954645049742096997 [(128,120130745529592791165536),(63,3857209115456950931461)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_10_2346_1 : fastPhase (bank 5 10).shape 179808 2346 20 1 4 1 1 = 122272315948636916530357 := p1 5 10 2346 20 1 4 1 1 191 122272315948636916530357 [(128,118634390374458069091680),(63,3637925574178847438677)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_10_2347_0 : fastPhase (bank 5 10).shape 179808 2347 20 1 4 1 0 = 123988516016532611284464 := p1 5 10 2347 20 1 4 1 0 191 123988516016532611284464 [(128,120131311034836336541824),(63,3857204981696274742640)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_10_2347_1 : fastPhase (bank 5 10).shape 179808 2347 20 1 4 1 1 = 122272866351951941815304 := p1 5 10 2347 20 1 4 1 1 191 122272866351951941815304 [(128,118634944702598502479616),(63,3637921649353439335688)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_10 : Checked (bank 5 10) 20 4 1 := by
  refine checked_from_values (bank 5 10) 20 4 1
    (P3_7_1.checked (bank 5 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_10_2346_0 rec_5_10_2346_1 rec_5_10_2347_0 rec_5_10_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_11_2346_0 : fastPhase (bank 5 11).shape 179808 2346 32 1 4 1 0 = 910961186226981869151419 := p1 5 11 2346 32 1 4 1 0 278 910961186226981869151419 [(128,762568259221587380317920),(128,148392927005394488833499),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_11_2346_1 : fastPhase (bank 5 11).shape 179808 2346 32 1 4 1 1 = 902258724557495941060967 := p1 5 11 2346 32 1 4 1 1 278 902258724557495941060967 [(128,756991396872378877302688),(128,145267327685117063758279),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_11_2347_0 : fastPhase (bank 5 11).shape 179808 2347 32 1 4 1 0 = 910965243031803318426469 := p1 5 11 2347 32 1 4 1 0 278 910965243031803318426469 [(128,762572276835619657924320),(128,148392966196183660502149),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_11_2347_1 : fastPhase (bank 5 11).shape 179808 2347 32 1 4 1 1 = 902262726453618790118479 := p1 5 11 2347 32 1 4 1 1 278 902262726453618790118479 [(128,756995361520315433825120),(128,145267364933303356293359),(22,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_11 : Checked (bank 5 11) 32 4 1 := by
  refine checked_from_values (bank 5 11) 32 4 1
    (P3_7_1.checked (bank 5 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_11_2346_0 rec_5_11_2346_1 rec_5_11_2347_0 rec_5_11_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_12_2346_0 : fastPhase (bank 5 12).shape 179808 2346 31 1 4 1 0 = 803735438660605709687352 := p1 5 12 2346 31 1 4 1 0 278 803735438660605709687352 [(128,672865870415326678975488),(128,130869568245279030711864),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_12_2346_1 : fastPhase (bank 5 12).shape 179808 2346 31 1 4 1 1 = 796054686852676597575909 := p1 5 12 2346 31 1 4 1 1 278 796054686852676597575909 [(128,667942064697210219269760),(128,128112622155466378306149),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_12_2347_0 : fastPhase (bank 5 12).shape 179808 2347 31 1 4 1 0 = 803739036798189101683500 := p1 5 12 2347 31 1 4 1 0 278 803739036798189101683500 [(128,672869431549501363520096),(128,130869605248687738163404),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_12_2347_1 : fastPhase (bank 5 12).shape 179808 2347 31 1 4 1 1 = 796058236313077253918313 := p1 5 12 2347 31 1 4 1 1 278 796058236313077253918313 [(128,667945578922828664837664),(128,128112657390248589080649),(22,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_12 : Checked (bank 5 12) 31 4 1 := by
  refine checked_from_values (bank 5 12) 31 4 1
    (P3_7_1.checked (bank 5 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_12_2346_0 rec_5_12_2346_1 rec_5_12_2347_0 rec_5_12_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_13_2346_0 : fastPhase (bank 5 13).shape 179808 2346 44 1 4 1 0 = 4230789908825324002723910 := p1 5 13 2346 44 1 4 1 0 370 4230789908825324002723910 [(128,2975717438369976142180160),(128,1155086398713259110100800),(114,99986071742088750442950)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_13_2346_1 : fastPhase (bank 5 13).shape 179808 2346 44 1 4 1 1 = 4200414005082539216848920 := p1 5 13 2346 44 1 4 1 1 370 4200414005082539216848920 [(128,2960962427229707865416448),(128,1142752094883120753623808),(114,96699482969710597808664)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_13_2347_0 : fastPhase (bank 5 13).shape 179808 2347 44 1 4 1 0 = 4230808666031338872726520 := p1 5 13 2347 44 1 4 1 0 370 4230808666031338872726520 [(128,2975734777938160663423360),(128,1155087944112891980999040),(114,99985943980286228304120)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_13_2347_1 : fastPhase (bank 5 13).shape 179808 2347 44 1 4 1 1 = 4200432571251234644264850 := p1 5 13 2347 44 1 4 1 1 370 4200432571251234644264850 [(128,2960979602318651417534016),(128,1142753609855750712294976),(114,96699359076832514435858)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_13 : Checked (bank 5 13) 44 4 1 := by
  refine checked_from_values (bank 5 13) 44 4 1
    (P3_7_1.checked (bank 5 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_13_2346_0 rec_5_13_2346_1 rec_5_13_2347_0 rec_5_13_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_14_2346_0 : fastPhase (bank 5 14).shape 179808 2346 76 1 4 1 0 = 91915380033479695988780091 := p1 5 14 2346 76 1 4 1 0 678 91915380033479695988780091 [(128,40537730880115956921793056),(128,28010477436337276725807648),(128,16070622518697799630952992),(128,6441457725818151947627040),(128,855091472510510762599355),(38,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_14_2346_1 : fastPhase (bank 5 14).shape 179808 2346 76 1 4 1 1 = 91554015481054649631495711 := p1 5 14 2346 76 1 4 1 1 678 91554015481054649631495711 [(128,40443089889095056596115104),(128,27913252300633703564308128),(128,15984525226340130829647520),(128,6379901574731424741887648),(128,833246490254333899537311),(38,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_14_2347_0 : fastPhase (bank 5 14).shape 179808 2347 76 1 4 1 0 = 91915791497758784934627168 := p1 5 14 2347 76 1 4 1 0 678 91915791497758784934627168 [(128,40538012222378287560057600),(128,28010586199530439656039168),(128,16070647177024176262210304),(128,6441455806610655395734272),(128,855090092215226060585824),(38,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_14_2347_1 : fastPhase (bank 5 14).shape 179808 2347 76 1 4 1 1 = 91554424652991357114723270 := p1 5 14 2347 76 1 4 1 1 678 91554424652991357114723270 [(128,40443369883871964415894848),(128,27913360360324110831060288),(128,15984549623971703420642624),(128,6379899640909320524186944),(128,833245143914257922938566),(38,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_14 : Checked (bank 5 14) 76 4 1 := by
  refine checked_from_values (bank 5 14) 76 4 1
    (P3_7_1.checked (bank 5 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_14_2346_0 rec_5_14_2346_1 rec_5_14_2347_0 rec_5_14_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_15_2346_0 : fastPhase (bank 5 15).shape 179808 2346 105 1 4 1 0 = 554368954618566707819843572 := p1 5 15 2346 105 1 4 1 0 925 554368954618566707819843572 [(128,186632440758369688092593664),(128,146198627664412411225976320),(128,105512417422571597326814720),(128,67615206465634968759627264),(128,35498111569661680337309184),(128,12102230368089260381023744),(128,809920369827101696498676),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_15_2346_1 : fastPhase (bank 5 15).shape 179808 2346 105 1 4 1 1 = 552769725496334444664579886 := p1 5 15 2346 105 1 4 1 1 925 552769725496334444664579886 [(128,186328879786362176515785280),(128,145880169175744389912969792),(128,105203195834440765918724672),(128,67338960247019290303513152),(128,35278185285291499954029120),(128,11961576722419423933088320),(128,778758445056898126469550),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_15_2347_0 : fastPhase (bank 5 15).shape 179808 2347 105 1 4 1 0 = 554371430921531506474711325 := p1 5 15 2347 105 1 4 1 0 925 554371430921531506474711325 [(128,186633811514869096498388448),(128,146199349240823500624391648),(128,105512730125350057385393632),(128,67615295919640375655108064),(128,35498109587019656930467296),(128,12102215812611609415298528),(128,809918721217209965663709),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_15_2347_1 : fastPhase (bank 5 15).shape 179808 2347 105 1 4 1 1 = 552772191670396343253312723 := p1 5 15 2347 105 1 4 1 1 925 552772191670396343253312723 [(128,186330245857311307647733152),(128,145880887728457814116179360),(128,105203506820654874910289312),(128,67339048942772181872688544),(128,35278183159754145653067168),(128,11961562302284809791856032),(128,778756859161209261499155),(29,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_15 : Checked (bank 5 15) 105 4 1 := by
  refine checked_from_values (bank 5 15) 105 4 1
    (P3_7_1.checked (bank 5 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_15_2346_0 rec_5_15_2346_1 rec_5_15_2347_0 rec_5_15_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_5_16_2346_0 : fastPhase (bank 5 16).shape 179808 2346 138 1 4 1 0 = 1693200108845542627539809705 := p1 5 16 2346 138 1 4 1 0 925 1693200108845542627539809705 [(128,568606885080648124158187360),(128,446226223445285285506262880),(128,322625175762997743792568160),(128,207117832656252790172108640),(128,108930244911914489701488480),(128,37200683995350622398801760),(128,2493062993093571810392425),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_16_2346_1 : fastPhase (bank 5 16).shape 179808 2346 138 1 4 1 1 = 1688332149343899637980899216 := p1 5 16 2346 138 1 4 1 1 925 1688332149343899637980899216 [(128,567690099157158905954773600),(128,445260516913711329415649888),(128,321684190519080480421612128),(128,206274518068828024768510560),(128,108256859866884520821647968),(128,36768798939656360575670880),(128,2397165878580016023034192),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_16_2347_0 : fastPhase (bank 5 16).shape 179808 2347 138 1 4 1 0 = 1693207278953968865075953522 := p1 5 16 2347 138 1 4 1 0 925 1693207278953968865075953522 [(128,568610916395603213579293280),(128,446228322767485554254307936),(128,322626063774000469644358240),(128,207118066363047576877662816),(128,108930219159507016585106016),(128,37200632974904366983914080),(128,2493057519420667151311154),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_5_16_2347_1 : fastPhase (bank 5 16).shape 179808 2347 138 1 4 1 1 = 1688339289971731854520904224 := p1 5 16 2347 138 1 4 1 1 925 1688339289971731854520904224 [(128,567694116611745443713779680),(128,445262607339640908852025312),(128,321685073540811291223107552),(128,206274749646505146117158880),(128,108256833808892678510823392),(128,36768748410730657150932960),(128,2397160613405728953076448),(29,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_5_16 : Checked (bank 5 16) 138 4 1 := by
  refine checked_from_values (bank 5 16) 138 4 1
    (P3_7_1.checked (bank 5 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_5_16_2346_0 rec_5_16_2346_1 rec_5_16_2347_0 rec_5_16_2347_1 (by decide +kernel) (by decide +kernel)

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
