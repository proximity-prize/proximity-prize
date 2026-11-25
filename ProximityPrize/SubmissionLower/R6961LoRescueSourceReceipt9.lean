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

private theorem rec_9_0_2346_0 : fastPhase (bank 9 0).shape 179808 2346 0 1 4 12 0 = 805262000710346890974 := p1 9 0 2346 0 1 4 12 0 130 805262000710346890974 [(128,805262000710346890974),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_0_2346_1 : fastPhase (bank 9 0).shape 179808 2346 0 1 4 12 1 = 785469324751379533830 := p1 9 0 2346 0 1 4 12 1 130 785469324751379533830 [(128,785469324751379533830),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_0_2347_0 : fastPhase (bank 9 0).shape 179808 2347 0 1 4 12 0 = 805266514305031955400 := p1 9 0 2347 0 1 4 12 0 130 805266514305031955400 [(128,805266514305031955400),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_0_2347_1 : fastPhase (bank 9 0).shape 179808 2347 0 1 4 12 1 = 785473688534399671092 := p1 9 0 2347 0 1 4 12 1 130 785473688534399671092 [(128,785473688534399671092),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_0 : Checked (bank 9 0) 0 4 12 := by
  refine checked_from_values (bank 9 0) 0 4 12
    (P3_7_1.checked (bank 9 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_0_2346_0 rec_9_0_2346_1 rec_9_0_2347_0 rec_9_0_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_1_2346_0 : fastPhase (bank 9 1).shape 179808 2346 1 1 4 12 0 = 918183656025994110443 := p1 9 1 2346 1 1 4 12 0 130 918183656025994110443 [(128,918183656025994110443),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_1_2346_1 : fastPhase (bank 9 1).shape 179808 2346 1 1 4 12 1 = 895874423005909697439 := p1 9 1 2346 1 1 4 12 1 130 895874423005909697439 [(128,895874423005909697439),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_1_2347_0 : fastPhase (bank 9 1).shape 179808 2347 1 1 4 12 0 = 918188733511251061366 := p1 9 1 2347 1 1 4 12 0 130 918188733511251061366 [(128,918188733511251061366),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_1_2347_1 : fastPhase (bank 9 1).shape 179808 2347 1 1 4 12 1 = 895879333394045993828 := p1 9 1 2347 1 1 4 12 1 130 895879333394045993828 [(128,895879333394045993828),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_1 : Checked (bank 9 1) 1 4 12 := by
  refine checked_from_values (bank 9 1) 1 4 12
    (P3_7_1.checked (bank 9 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_1_2346_0 rec_9_1_2346_1 rec_9_1_2347_0 rec_9_1_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_2_2346_0 : fastPhase (bank 9 2).shape 179808 2346 2 1 4 12 0 = 1056010775395723006887 := p1 9 2 2346 2 1 4 12 0 130 1056010775395723006887 [(128,1056010775395723006887),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_2_2346_1 : fastPhase (bank 9 2).shape 179808 2346 2 1 4 12 1 = 1030648791141494364543 := p1 9 2 2346 2 1 4 12 1 130 1030648791141494364543 [(128,1030648791141494364543),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_2_2347_0 : fastPhase (bank 9 2).shape 179808 2347 2 1 4 12 0 = 1056016535742330518016 := p1 9 2 2347 2 1 4 12 0 130 1056016535742330518016 [(128,1056016535742330518016),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_2_2347_1 : fastPhase (bank 9 2).shape 179808 2347 2 1 4 12 1 = 1030654363538885149308 := p1 9 2 2347 2 1 4 12 1 130 1030654363538885149308 [(128,1030654363538885149308),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_2 : Checked (bank 9 2) 2 4 12 := by
  refine checked_from_values (bank 9 2) 2 4 12
    (P3_7_1.checked (bank 9 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_2_2346_0 rec_9_2_2346_1 rec_9_2_2347_0 rec_9_2_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_3_2346_0 : fastPhase (bank 9 3).shape 179808 2346 3 1 4 12 0 = 1225457659393766669481 := p1 9 3 2346 3 1 4 12 0 130 1225457659393766669481 [(128,1225457659393766669481),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_3_2346_1 : fastPhase (bank 9 3).shape 179808 2346 3 1 4 12 1 = 1196365559077167347037 := p1 9 3 2346 3 1 4 12 1 130 1196365559077167347037 [(128,1196365559077167347037),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_3_2347_0 : fastPhase (bank 9 3).shape 179808 2347 3 1 4 12 0 = 1225464252312254753214 := p1 9 3 2347 3 1 4 12 0 130 1225464252312254753214 [(128,1225464252312254753214),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_3_2347_1 : fastPhase (bank 9 3).shape 179808 2347 3 1 4 12 1 = 1196371938720352804956 := p1 9 3 2347 3 1 4 12 1 130 1196371938720352804956 [(128,1196371938720352804956),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_3 : Checked (bank 9 3) 3 4 12 := by
  refine checked_from_values (bank 9 3) 3 4 12
    (P3_7_1.checked (bank 9 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_3_2346_0 rec_9_3_2346_1 rec_9_3_2347_0 rec_9_3_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_4_2346_0 : fastPhase (bank 9 4).shape 179808 2346 4 1 4 12 0 = 1437531308459449030515 := p1 9 4 2346 4 1 4 12 0 130 1437531308459449030515 [(128,1437531308459449030515),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_4_2346_1 : fastPhase (bank 9 4).shape 179808 2346 4 1 4 12 1 = 1403799228143574466371 := p1 9 4 2346 4 1 4 12 1 130 1403799228143574466371 [(128,1403799228143574466371),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_4_2347_0 : fastPhase (bank 9 4).shape 179808 2347 4 1 4 12 0 = 1437538934976730626084 := p1 9 4 2347 4 1 4 12 0 130 1437538934976730626084 [(128,1437538934976730626084),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_4_2347_1 : fastPhase (bank 9 4).shape 179808 2347 4 1 4 12 1 = 1403806610066500101156 := p1 9 4 2347 4 1 4 12 1 130 1403806610066500101156 [(128,1403806610066500101156),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_4 : Checked (bank 9 4) 4 4 12 := by
  refine checked_from_values (bank 9 4) 4 4 12
    (P3_7_1.checked (bank 9 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_4_2346_0 rec_9_4_2346_1 rec_9_4_2347_0 rec_9_4_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_5_2346_0 : fastPhase (bank 9 5).shape 179808 2346 5 1 4 12 0 = 1707855257553106622454 := p1 9 5 2346 5 1 4 12 0 130 1707855257553106622454 [(128,1707855257553106622454),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_5_2346_1 : fastPhase (bank 9 5).shape 179808 2346 5 1 4 12 1 = 1668244793141757288990 := p1 9 5 2346 5 1 4 12 1 130 1668244793141757288990 [(128,1668244793141757288990),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_5_2347_0 : fastPhase (bank 9 5).shape 179808 2347 5 1 4 12 0 = 1707864190958711732652 := p1 9 5 2347 5 1 4 12 0 130 1707864190958711732652 [(128,1707864190958711732652),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_5_2347_1 : fastPhase (bank 9 5).shape 179808 2347 5 1 4 12 1 = 1668253442508500031384 := p1 9 5 2347 5 1 4 12 1 130 1668253442508500031384 [(128,1668253442508500031384),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_5 : Checked (bank 9 5) 5 4 12 := by
  refine checked_from_values (bank 9 5) 5 4 12
    (P3_7_1.checked (bank 9 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_5_2346_0 rec_9_5_2346_1 rec_9_5_2347_0 rec_9_5_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_6_2346_0 : fastPhase (bank 9 6).shape 179808 2346 7 1 4 12 0 = 2525240922042066881507 := p1 9 6 2346 7 1 4 12 0 130 2525240922042066881507 [(128,2525240922042066881507),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_6_2346_1 : fastPhase (bank 9 6).shape 179808 2346 7 1 4 12 1 = 2468025148502325552303 := p1 9 6 2346 7 1 4 12 1 130 2468025148502325552303 [(128,2468025148502325552303),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_6_2347_0 : fastPhase (bank 9 6).shape 179808 2347 7 1 4 12 0 = 2525253756376142887858 := p1 9 6 2347 7 1 4 12 0 130 2525253756376142887858 [(128,2525253756376142887858),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_6_2347_1 : fastPhase (bank 9 6).shape 179808 2347 7 1 4 12 1 = 2468037581790753495860 := p1 9 6 2347 7 1 4 12 1 130 2468037581790753495860 [(128,2468037581790753495860),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_6 : Checked (bank 9 6) 7 4 12 := by
  refine checked_from_values (bank 9 6) 7 4 12
    (P3_7_1.checked (bank 9 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_6_2346_0 rec_9_6_2346_1 rec_9_6_2347_0 rec_9_6_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_7_2346_0 : fastPhase (bank 9 7).shape 179808 2346 10 1 4 12 0 = 5425475748589832551989 := p1 9 7 2346 10 1 4 12 0 130 5425475748589832551989 [(128,5425475748589832551989),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_7_2346_1 : fastPhase (bank 9 7).shape 179808 2346 10 1 4 12 1 = 5306798506273588712445 := p1 9 7 2346 10 1 4 12 1 130 5306798506273588712445 [(128,5306798506273588712445),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_7_2347_0 : fastPhase (bank 9 7).shape 179808 2347 10 1 4 12 0 = 5425502124043364809008 := p1 9 7 2347 10 1 4 12 0 130 5425502124043364809008 [(128,5425502124043364809008),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_7_2347_1 : fastPhase (bank 9 7).shape 179808 2347 10 1 4 12 1 = 5306824078902340367940 := p1 9 7 2347 10 1 4 12 1 130 5306824078902340367940 [(128,5306824078902340367940),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_7 : Checked (bank 9 7) 10 4 12 := by
  refine checked_from_values (bank 9 7) 10 4 12
    (P3_7_1.checked (bank 9 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_7_2346_0 rec_9_7_2346_1 rec_9_7_2347_0 rec_9_7_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_8_2346_0 : fastPhase (bank 9 8).shape 179808 2346 16 1 4 12 0 = 29119825649974116159297 := p1 9 8 2346 16 1 4 12 0 191 29119825649974116159297 [(128,28388357125245603137184),(63,731468524728513022113)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_8_2346_1 : fastPhase (bank 9 8).shape 179808 2346 16 1 4 12 1 = 28673036511992251557609 := p1 9 8 2346 16 1 4 12 1 191 28673036511992251557609 [(128,27984390284349299612448),(63,688646227642951945161)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_8_2347_0 : fastPhase (bank 9 8).shape 179808 2347 16 1 4 12 0 = 29119967404940355240132 := p1 9 8 2347 16 1 4 12 0 191 29119967404940355240132 [(128,28388499584619083390976),(63,731467820321271849156)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_8_2347_1 : fastPhase (bank 9 8).shape 179808 2347 16 1 4 12 1 = 28673175245314180949448 := p1 9 8 2347 16 1 4 12 1 191 28673175245314180949448 [(128,27984529686203474888448),(63,688645559110706061000)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_8 : Checked (bank 9 8) 16 4 12 := by
  refine checked_from_values (bank 9 8) 16 4 12
    (P3_7_1.checked (bank 9 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_8_2346_0 rec_9_8_2346_1 rec_9_8_2347_0 rec_9_8_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_9_2346_0 : fastPhase (bank 9 9).shape 179808 2346 10 1 4 12 0 = 5425475748589832551989 := p1 9 9 2346 10 1 4 12 0 130 5425475748589832551989 [(128,5425475748589832551989),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_9_2346_1 : fastPhase (bank 9 9).shape 179808 2346 10 1 4 12 1 = 5306798506273588712445 := p1 9 9 2346 10 1 4 12 1 130 5306798506273588712445 [(128,5306798506273588712445),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_9_2347_0 : fastPhase (bank 9 9).shape 179808 2347 10 1 4 12 0 = 5425502124043364809008 := p1 9 9 2347 10 1 4 12 0 130 5425502124043364809008 [(128,5425502124043364809008),(2,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_9_2347_1 : fastPhase (bank 9 9).shape 179808 2347 10 1 4 12 1 = 5306824078902340367940 := p1 9 9 2347 10 1 4 12 1 130 5306824078902340367940 [(128,5306824078902340367940),(2,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_9 : Checked (bank 9 9) 10 4 12 := by
  refine checked_from_values (bank 9 9) 10 4 12
    (P3_7_1.checked (bank 9 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_584_129)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_9_2346_0 rec_9_9_2346_1 rec_9_9_2347_0 rec_9_9_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_10_2346_0 : fastPhase (bank 9 10).shape 179808 2346 20 1 4 12 0 = 60112666198688949915615 := p1 9 10 2346 20 1 4 12 0 191 60112666198688949915615 [(128,58492087914991756489056),(63,1620578283697193426559)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_10_2346_1 : fastPhase (bank 9 10).shape 179808 2346 20 1 4 12 1 = 59219282464429499534007 := p1 9 10 2346 20 1 4 12 1 191 59219282464429499534007 [(128,57692641110735381096672),(63,1526641353694118437335)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_10_2347_0 : fastPhase (bank 9 10).shape 179808 2347 20 1 4 12 0 = 60112946892484533131532 := p1 9 10 2347 20 1 4 12 0 191 60112946892484533131532 [(128,58492370335585948941312),(63,1620576556898584190220)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_10_2347_1 : fastPhase (bank 9 10).shape 179808 2347 20 1 4 12 1 = 59219557313847434872008 := p1 9 10 2347 20 1 4 12 1 191 59219557313847434872008 [(128,57692917598220665577216),(63,1526639715626769294792)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_10 : Checked (bank 9 10) 20 4 12 := by
  refine checked_from_values (bank 9 10) 20 4 12
    (P3_7_1.checked (bank 9 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_862_190)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_10_2346_0 rec_9_10_2346_1 rec_9_10_2347_0 rec_9_10_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_11_2346_0 : fastPhase (bank 9 11).shape 179808 2346 32 1 4 12 0 = 437965115050716654273369 := p1 9 11 2346 32 1 4 12 0 278 437965115050716654273369 [(128,374058397537978194075168),(128,63906717512738460198201),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_11_2346_1 : fastPhase (bank 9 11).shape 179808 2346 32 1 4 12 1 = 433429027393480671120810 := p1 9 11 2346 32 1 4 12 1 278 433429027393480671120810 [(128,370924887633644510298336),(128,62504139759836160822474),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_11_2347_0 : fastPhase (bank 9 11).shape 179808 2347 32 1 4 12 0 = 437967135394006764625527 := p1 9 11 2347 32 1 4 12 0 278 437967135394006764625527 [(128,374060399240582069691840),(128,63906736153424694933687),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_11_2347_1 : fastPhase (bank 9 11).shape 179808 2347 32 1 4 12 1 = 433431018357121916521608 := p1 9 11 2347 32 1 4 12 1 278 433431018357121916521608 [(128,370926860876048827791360),(128,62504157481073088730248),(22,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_11 : Checked (bank 9 11) 32 4 12 := by
  refine checked_from_values (bank 9 11) 32 4 12
    (P3_7_1.checked (bank 9 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_11_2346_0 rec_9_11_2346_1 rec_9_11_2347_0 rec_9_11_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_12_2346_0 : fastPhase (bank 9 12).shape 179808 2346 31 1 4 12 0 = 385071950318954223771243 := p1 9 12 2346 31 1 4 12 0 278 385071950318954223771243 [(128,329334860863180359078112),(128,55737089455773864693131),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_12_2346_1 : fastPhase (bank 9 12).shape 179808 2346 31 1 4 12 1 = 381061596945205769823926 := p1 9 12 2346 31 1 4 12 1 278 381061596945205769823926 [(128,326551495729163519346976),(128,54510101216042250476950),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_12_2347_0 : fastPhase (bank 9 12).shape 179808 2347 31 1 4 12 0 = 385073739807046715941215 := p1 9 12 2347 31 1 4 12 0 278 385073739807046715941215 [(128,329336632943807907902528),(128,55737106863238808038687),(22,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_12_2347_1 : fastPhase (bank 9 12).shape 179808 2347 31 1 4 12 1 = 381063360305523690679408 := p1 9 12 2347 31 1 4 12 1 278 381063360305523690679408 [(128,326553242513742591202688),(128,54510117791781099476720),(22,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_12 : Checked (bank 9 12) 31 4 12 := by
  refine checked_from_values (bank 9 12) 31 4 12
    (P3_7_1.checked (bank 9 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1251_277)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_12_2346_0 rec_9_12_2346_1 rec_9_12_2347_0 rec_9_12_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_13_2346_0 : fastPhase (bank 9 13).shape 179808 2346 44 1 4 12 0 = 2025747459561440006231790 := p1 9 13 2346 44 1 4 12 0 370 2025747459561440006231790 [(128,1476509435611123405689120),(128,509531061090757242151200),(114,39706962859559358391470)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_13_2346_1 : fastPhase (bank 9 13).shape 179808 2346 44 1 4 12 1 = 2009854115228798022624795 := p1 9 13 2346 44 1 4 12 1 370 2009854115228798022624795 [(128,1467849445937916107283552),(128,503632829258184764992608),(114,38371840032697150348635)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_13_2347_0 : fastPhase (bank 9 13).shape 179808 2347 44 1 4 12 0 = 2025756795580760484157740 := p1 9 13 2347 44 1 4 12 0 370 2025756795580760484157740 [(128,1476518122819169754892224),(128,509531760392152278575040),(114,39706912369438450690476)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_13_2347_1 : fastPhase (bank 9 13).shape 179808 2347 44 1 4 12 1 = 2009863348389773026327125 := p1 9 13 2347 44 1 4 12 1 370 2009863348389773026327125 [(128,1467858043026870457179648),(128,503633514260021312749056),(114,38371791102881256398421)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_13 : Checked (bank 9 13) 44 4 12 := by
  refine checked_from_values (bank 9 13) 44 4 12
    (P3_7_1.checked (bank 9 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1669_369)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_13_2346_0 rec_9_13_2346_1 rec_9_13_2347_0 rec_9_13_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_14_2346_0 : fastPhase (bank 9 14).shape 179808 2346 76 1 4 12 0 = 43187846163129285927264120 := p1 9 14 2346 76 1 4 12 0 678 43187846163129285927264120 [(128,20558081388992135741236480),(128,13017636556969967837668608),(128,6818933372604524886353152),(128,2489492558484846513317120),(128,303702286077810948688760),(38,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_14_2346_1 : fastPhase (bank 9 14).shape 179808 2346 76 1 4 12 1 = 42996995410222668847889752 := p1 9 14 2346 76 1 4 12 1 678 42996995410222668847889752 [(128,20496409206891554872327424),(128,12963412324557415528856832),(128,6777492769638683329199360),(128,2463913145246552862227712),(128,295767963888462255278424),(38,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_14_2347_0 : fastPhase (bank 9 14).shape 179808 2347 76 1 4 12 0 = 43188049536872192473243200 := p1 9 14 2347 76 1 4 12 0 678 43188049536872192473243200 [(128,20558224583274363445734656),(128,13017687362641372340612352),(128,6818943945426442211519744),(128,2489491848449177831992576),(128,303701797080836643383872),(38,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_14_2347_1 : fastPhase (bank 9 14).shape 179808 2347 76 1 4 12 1 = 42997197528111893090331548 := p1 9 14 2347 76 1 4 12 1 678 42997197528111893090331548 [(128,20496551620787151893673088),(128,12963462766877922125182080),(128,6777503223553210631140480),(128,2463912429715321319191680),(128,295767487178287121144220),(38,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_14 : Checked (bank 9 14) 76 4 12 := by
  refine checked_from_values (bank 9 14) 76 4 12
    (P3_7_1.checked (bank 9 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3060_677)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_14_2346_0 rec_9_14_2346_1 rec_9_14_2347_0 rec_9_14_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_15_2346_0 : fastPhase (bank 9 15).shape 179808 2346 105 1 4 12 0 = 259709440422347865642873186 := p1 9 15 2346 105 1 4 12 0 925 259709440422347865642873186 [(128,95615541380428898392543424),(128,70135674965894048300298432),(128,47285231387306453336707264),(128,28239586830503939773378752),(128,13787880257879294433071296),(128,4370527439779777314025664),(128,274998160555454092848354),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_15_2346_1 : fastPhase (bank 9 15).shape 179808 2346 105 1 4 12 1 = 258864073003032155048250668 := p1 9 15 2346 105 1 4 12 1 925 258864073003032155048250668 [(128,95411870228737018523481152),(128,69946329073901643776873536),(128,47121133845943271268004928),(128,28108477626026144141677632),(128,13694610603854554264794176),(128,4317354109072354850690112),(128,264297515497168222729132),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_15_2347_0 : fastPhase (bank 9 15).shape 179808 2347 105 1 4 12 0 = 259710662871549646056341808 := p1 9 15 2347 105 1 4 12 0 925 259710662871549646056341808 [(128,95616245026061406989326528),(128,70136021977235468109035712),(128,47285372015671921262483648),(128,28239624445515365187287232),(128,13787879595469152242014400),(128,4370522210543016455551168),(128,274997601053315810643120),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_15_2347_1 : fastPhase (bank 9 15).shape 179808 2347 105 1 4 12 1 = 258865289891757391859582532 := p1 9 15 2347 105 1 4 12 1 925 258865289891757391859582532 [(128,95412571116331769749394624),(128,69946674451424085756556480),(128,47121273627475365664986304),(128,28108514902249225823122624),(128,13694609885590206674162880),(128,4317348931171400805430464),(128,264296977515337385929156),(29,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_15 : Checked (bank 9 15) 105 4 12 := by
  refine checked_from_values (bank 9 15) 105 4 12
    (P3_7_1.checked (bank 9 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_15_2346_0 rec_9_15_2346_1 rec_9_15_2347_0 rec_9_15_2347_1 (by decide +kernel) (by decide +kernel)

private theorem rec_9_16_2346_0 : fastPhase (bank 9 16).shape 179808 2346 138 1 4 12 0 = 820963450957002067909220505 := p1 9 16 2346 138 1 4 12 0 925 820963450957002067909220505 [(128,290225691001104211287679200),(128,219394607041490092816470240),(128,152687444675822777456460000),(128,94290745991756469367730400),(128,47681850966527482917216480),(128,15666411498353755303039200),(128,1016699781947278760624985),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_16_2346_1 : fastPhase (bank 9 16).shape 179808 2346 138 1 4 12 1 = 818433485079668685861167022 := p1 9 16 2346 138 1 4 12 1 925 818433485079668685861167022 [(128,289673867683247229235636128),(128,218855177799171793073510304),(128,152196331041281443117467552),(128,93878149740368036054267808),(128,47372548448790626948474784),(128,15480047971874981866788768),(128,977362394934575565021678),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_16_2347_0 : fastPhase (bank 9 16).shape 179808 2347 138 1 4 12 0 = 820967037886678022998402071 := p1 9 16 2347 138 1 4 12 0 925 820967037886678022998402071 [(128,290227751026019957200330560),(128,219395640696410491792588608),(128,152687865813234939164024640),(128,94290852846314962791874368),(128,47681839891594225648312128),(128,15666390062886018249817920),(128,1016697550217428151453847),(29,0)] (by decide +kernel) (by decide +kernel)

private theorem rec_9_16_2347_1 : fastPhase (bank 9 16).shape 179808 2347 138 1 4 12 1 = 818437056322643262935384415 := p1 9 16 2347 138 1 4 12 1 925 818437056322643262935384415 [(128,289675920032468997166788096),(128,218856206771405380538912256),(128,152196749688129174748442112),(128,93878255591021693957869056),(128,47372537242108422298430976),(128,15480026748806641919479296),(128,977360248702952305462623),(29,0)] (by decide +kernel) (by decide +kernel)

theorem receipt_9_16 : Checked (bank 9 16) 138 4 12 := by
  refine checked_from_values (bank 9 16) 138 4 12
    (P3_7_1.checked (bank 9 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4173_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) rec_9_16_2346_0 rec_9_16_2346_1 rec_9_16_2347_0 rec_9_16_2347_1 (by decide +kernel) (by decide +kernel)

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
